#!/usr/bin/env python3
"""Fail if any Lean source under Complexity/ or lean/ contains a forbidden token outside comments.

Forbidden: `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern`, `unsafe`.
Comments (`-- ...`, `/- ... -/`, docstrings) are stripped first, so the attribution
headers and the port's explanatory comments may mention these words.
"""
import re, sys, pathlib

ROOT = pathlib.Path(__file__).resolve().parent.parent
FORBIDDEN = re.compile(r'(?<![\w.])(sorry|admit|axiom|native_decide|implemented_by|extern|unsafe)(?![\w])')

def strip_comments(text: str) -> str:
    text = re.sub(r'/-.*?-/', ' ', text, flags=re.S)
    text = re.sub(r'--[^\n]*', ' ', text)
    return text

bad = []
for path in sorted(list((ROOT / 'Complexity').rglob('*.lean')) + list((ROOT / 'lean').rglob('*.lean')) + [ROOT / 'Complexity.lean']):
    stripped = strip_comments(path.read_text(encoding='utf-8'))
    for m in FORBIDDEN.finditer(stripped):
        line = stripped.count('\n', 0, m.start()) + 1
        bad.append(f'{path.relative_to(ROOT)}:{line}: {m.group(1)}')
if bad:
    print('forbidden tokens found:', file=sys.stderr)
    print('\n'.join(bad), file=sys.stderr)
    sys.exit(1)
print('forbidden-token scan: clean')
