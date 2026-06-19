#!/usr/bin/env python3
from __future__ import annotations

import json
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parent / "RequestProject"
OUTPUT = Path(__file__).resolve().parent / "dependency-graph.json"
CONTENT_OUTPUT = Path(__file__).resolve().parent / "dependency-content-library.json"

DECL_RE = re.compile(r"^\s*(?:(?:@[^\r\n]+)\s+)*(?:(?:local|nonrec|protected|private)\s+)*(def|theorem|lemma|structure|class|abbrev|inductive)\s+([^\s(:=]+)")
IMPORT_RE = re.compile(r'^\s*import\s+(.+)$')
SORRY_RE = re.compile(r'\bsorry\b')


def strip_block_comments(text: str) -> str:
    pieces: list[str] = []
    i = 0
    depth = 0
    while i < len(text):
        if text.startswith('/-', i):
            depth += 1
            pieces.append('  ')
            i += 2
            continue
        if depth > 0 and text.startswith('-/', i):
            depth -= 1
            pieces.append('  ')
            i += 2
            continue
        ch = text[i]
        if depth > 0:
            pieces.append('\n' if ch == '\n' else ' ')
        else:
            pieces.append(ch)
        i += 1
    return ''.join(pieces)


def strip_line_comments(line: str) -> str:
    if '--' not in line:
        return line
    idx = line.find('--')
    return line[:idx]


def parse_file(path: Path):
    raw_text = path.read_text(encoding='utf-8')
    text = strip_block_comments(raw_text)
    lines = text.splitlines()
    raw_lines = raw_text.splitlines()

    imports: list[str] = []
    decls: list[dict] = []

    for i, line in enumerate(lines, start=1):
        m_import = IMPORT_RE.match(line)
        if m_import:
            imports.extend(m_import.group(1).split())
        clean = strip_line_comments(line)
        m_decl = DECL_RE.match(clean)
        if m_decl:
            decls.append(
                {
                    'kind': m_decl.group(1),
                    'name': m_decl.group(2),
                    'line_start': i,
                    'signature': raw_lines[i - 1].strip(),
                }
            )

    for idx, decl in enumerate(decls):
        start = decl['line_start']
        end = decls[idx + 1]['line_start'] - 1 if idx + 1 < len(decls) else len(lines)
        decl['line_end'] = end
        span = '\n'.join(raw_lines[start - 1 : end])
        decl['status'] = 'placeholder' if SORRY_RE.search(span) else 'complete'
        decl['span'] = span

    return imports, decls


def main() -> None:
    files = sorted(ROOT.glob('*.lean'))
    modules = {path.name: f'RequestProject.{path.stem}' for path in files}
    parsed = {}
    all_decl_names: dict[str, list[tuple[str, str]]] = {}

    for path in files:
        imports, decls = parse_file(path)
        parsed[path.name] = {'imports': imports, 'decls': decls}
        for decl in decls:
            all_decl_names.setdefault(decl['name'], []).append((path.name, decl['name']))

    nodes = []
    edges = []
    content_entries = []

    for path in files:
        file_id = f'file:{path.name}'
        module_name = modules[path.name]
        nodes.append(
            {
                'id': file_id,
                'type': 'file',
                'name': path.name,
                'module': module_name,
                'path': str(path),
            }
        )

        for imported in parsed[path.name]['imports']:
            if imported.startswith('RequestProject.'):
                imported_stem = imported.split('.')[-1] + '.lean'
                if imported_stem in modules:
                    edges.append(
                        {
                            'from': file_id,
                            'to': f'file:{imported_stem}',
                            'type': 'imports',
                            'confidence': 1.0,
                        }
                    )

        for decl in parsed[path.name]['decls']:
            node_id = f"decl:{path.name}::{decl['name']}@{decl['line_start']}"
            decl['id'] = node_id
            content_entries.append(
                {
                    'id': node_id,
                    'type': 'declaration_content',
                    'kind': decl['kind'],
                    'name': decl['name'],
                    'file': path.name,
                    'module': module_name,
                    'line_start': decl['line_start'],
                    'line_end': decl['line_end'],
                    'status': decl['status'],
                    'signature': decl['signature'],
                    'text': decl['span'],
                }
            )
            nodes.append(
                {
                    'id': node_id,
                    'type': 'declaration',
                    'kind': decl['kind'],
                    'name': decl['name'],
                    'file': path.name,
                    'module': module_name,
                    'line_start': decl['line_start'],
                    'line_end': decl['line_end'],
                    'status': decl['status'],
                    'signature': decl['signature'],
                }
            )
            edges.append(
                {
                    'from': file_id,
                    'to': node_id,
                    'type': 'contains',
                    'confidence': 1.0,
                }
            )

    all_names = sorted(all_decl_names, key=len, reverse=True)
    name_pattern = re.compile(r'\b(' + '|'.join(re.escape(n) for n in all_names) + r')\b') if all_names else None

    for path in files:
        decls = parsed[path.name]['decls']
        for decl in decls:
            span = decl['span']
            refs = set()
            if name_pattern is not None:
                for match in name_pattern.finditer(span):
                    ref = match.group(1)
                    if ref != decl['name']:
                        refs.add(ref)
            for ref in sorted(refs):
                for ref_file, _ in all_decl_names.get(ref, []):
                    target_decl = next((d for d in parsed[ref_file]['decls'] if d['name'] == ref), None)
                    if target_decl is None:
                        continue
                    edges.append(
                        {
                            'from': decl['id'],
                            'to': target_decl['id'],
                            'type': 'decl_ref',
                            'confidence': 0.65 if ref_file == path.name else 0.45,
                        }
                    )

    graph = {
        'project': 'Erdos-306',
        'root': str(ROOT),
        'generated_by': 'generate_dependency_graph.py',
        'node_count': len(nodes),
        'edge_count': len(edges),
        'nodes': nodes,
        'edges': edges,
    }

    OUTPUT.write_text(json.dumps(graph, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
    content_library = {
        'project': 'Erdos-306',
        'root': str(ROOT),
        'generated_by': 'generate_dependency_graph.py',
        'entry_count': len(content_entries),
        'entries': content_entries,
    }
    CONTENT_OUTPUT.write_text(json.dumps(content_library, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
    print(f'wrote {OUTPUT} with {len(nodes)} nodes and {len(edges)} edges')
    print(f'wrote {CONTENT_OUTPUT} with {len(content_entries)} content entries')


if __name__ == '__main__':
    main()
