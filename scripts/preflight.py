#!/usr/bin/env python3
"""Static packaging checks only. This is not a Lean parser or proof checker."""
from pathlib import Path
import json
import re
import sys
import tomllib
try:
    import yaml
except ImportError:
    raise SystemExit('Install audit dependencies: python3 -m pip install -r requirements-audit.txt')

ROOT = Path(__file__).resolve().parents[1]
errors = []

def require(test, message):
    if not test:
        errors.append(message)


def strip_comments(s):
    """Remove nested block comments and line comments for these source files."""
    out, depth, i = [], 0, 0
    while i < len(s):
        if s.startswith('/-', i):
            depth += 1
            i += 2
        elif depth and s.startswith('-/', i):
            depth -= 1
            i += 2
        elif depth:
            i += 1
        elif s.startswith('--', i):
            j = s.find('\n', i)
            i = len(s) if j < 0 else j
        else:
            out.append(s[i])
            i += 1
    require(depth == 0, 'Unterminated block comment')
    return ''.join(out)

required = ['Challenge.lean', 'Solution.lean', 'AxiomAudit.lean', 'lakefile.toml',
            'lake-manifest.json', 'lean-toolchain', 'comparator.json',
            'formalization.yaml', 'LICENSE', 'NOTICE', 'docs/manuscript-source.pdf']
for name in required:
    require((ROOT / name).is_file(), f'Missing {name}')
if errors:
    raise SystemExit('\n'.join(errors))

challenge = (ROOT / 'Challenge.lean').read_text()
solution = (ROOT / 'Solution.lean').read_text()
cfg = json.loads((ROOT / 'comparator.json').read_text())
manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
lake = tomllib.loads((ROOT / 'lakefile.toml').read_text())
meta = yaml.safe_load((ROOT / 'formalization.yaml').read_text())

for p in ROOT.rglob('*.lean'):
    if any(x in p.parts for x in ('.lake', '.git', '.cache')):
        continue
    require(not p.is_symlink(), f'Symlinked Lean source: {p.relative_to(ROOT)}')
    text = p.read_text()
    code = strip_comments(text)
    require(code.lstrip().startswith('module\n'), f'Missing module header: {p.name}')
    require(len(text.splitlines()) <= 10000, f'Over 10000 lines: {p.name}')
    if p.name != 'Challenge.lean':
        require(not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|sorryAx)\b', code),
                f'Forbidden proof hole, declaration or tactic in {p.name}')
require(len(challenge.splitlines()) <= 1000, 'Challenge exceeds 1000 lines')
require(len(challenge.encode()) <= 100 * 1024, 'Challenge exceeds 100 KiB')
require(not (ROOT / 'TWS.lean').exists() and not (ROOT / 'TWS').exists(),
        'Remove the legacy TWS tree; do not simply overlay this candidate')
require(not (ROOT / 'lakefile.lean').exists(), 'Two Lake configurations present')
require(cfg['challenge_module'] == 'Challenge' and cfg['solution_module'] == 'Solution',
        'Unexpected module selection')
require('external_kernels' not in cfg, 'external_kernels is not a submission field')
require(cfg.get('definition_names') == [], 'Definitions must remain explicit')
require(set(cfg['permitted_axioms']) == {'propext','Classical.choice','Quot.sound'},
        'Unexpected permitted axioms')
require(len(set(cfg['theorem_names'])) == len(cfg['theorem_names']), 'Duplicate selections')

# Compare declarations textually after stripping comments. Comparator must still
# compare elaborated types and definitions; textual equality is not a substitute.
c = strip_comments(challenge)
s = strip_comments(solution)
cdefs = c[c.index('open Finset Real'):c.index('theorem convolution_opNorm')]
sdefs = s[s.index('open Finset Real'):s.index('@[simp] theorem convolutionOperator_apply')]
require(' '.join(cdefs.split()) == ' '.join(sdefs.split()), 'Definition surfaces differ')
for qualified in cfg['theorem_names']:
    name = qualified.split('.')[-1]
    pattern = r'\btheorem\s+' + re.escape(name) + r'\b(.*?):= by'
    cm, sm = re.search(pattern, c, re.S), re.search(pattern, s, re.S)
    require(cm is not None and sm is not None, f'Missing selected theorem: {qualified}')
    if cm and sm:
        require(' '.join(cm[1].split()) == ' '.join(sm[1].split()),
                f'Statement text differs: {qualified}')
require(len(re.findall(r'\bsorry\b', c)) == len(cfg['theorem_names']),
        'Challenge holes do not match selected theorem count')
require(all(x.startswith('Mathlib.') for x in re.findall(r'^public import (\S+)', c, re.M)),
        'Non-Mathlib direct Challenge import')

require(meta['version'] == 'v0.4', 'Unexpected metadata version')
require(meta['project']['license'] == 'Apache-2.0', 'Licence mismatch')
require(bool(meta['project']['authors']) and bool(meta['project']['responsible_maintainers']),
        'Missing authors or maintainers')
require('repository' not in meta, 'Review changed repository role: this candidate is substantive')
require(bool(meta['sources']), 'Missing sources')
require(any(x['relationship'] in {'formalizes','adapts','independently-proves'}
            for x in meta['sources']), 'Missing source-based origin')
for source in meta['sources']:
    require(source['relationship'] in {'formalizes','adapts','independently-proves','background','other'},
            'Unknown source relationship')
    require(source.get('type') in {'paper','book','web discussion','folklore','other'},
            'Unexpected source type')
require(set(x['lean'] for x in meta['alignment']['statements']) == set(cfg['theorem_names']),
        'Metadata/Comparator alignment mismatch')
require(1 <= len(meta['classification']['arxiv']) <= 2, 'arXiv classification count')
require(1 <= len(meta['classification']['msc2020']) <= 8, 'MSC classification count')
require(all(re.fullmatch(r'\d{2}[A-Z]\d{2}', x) for x in meta['classification']['msc2020']),
        'MSC spelling')
require('arXiv:XXXX' not in (ROOT/'formalization.yaml').read_text(), 'Placeholder arXiv ID')
require((ROOT/'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.35.0-rc2',
        'Review changed toolchain and Mathlib compatibility together')
mathlib = next(p for p in manifest['packages'] if p['name'] == 'mathlib')
require(mathlib['rev'] == lake['require'][0]['rev'] == '065356127b1dc0016f66b7283ce0ce2c4055aa55',
        'Mathlib lock mismatch')
require(all(re.fullmatch(r'[0-9a-f]{40}', p['rev']) for p in manifest['packages']),
        'Non-immutable dependency revision')
if errors:
    print('\n'.join('FAIL: ' + x for x in errors))
    sys.exit(1)
print(f'PASS: static packaging checks; {len(cfg["theorem_names"])} selected statements; '
      f'Challenge {len(challenge.splitlines())} lines / {len(challenge.encode())} bytes.')
print('NOT CHECKED: Lean elaboration, proof correctness, transitive import closure, '
      'axiom dependencies, Comparator, or editorial eligibility.')
