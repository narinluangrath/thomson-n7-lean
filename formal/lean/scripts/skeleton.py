"""The statement skeleton of Solution.lean: every declaration after the preamble with its proof and
certificate data removed, grouped by the namespace or section it sits in.

A declaration is data (left out) when it is a `def`/`abbrev` whose text is at least 30% numerals, or it
builds a packed certificate block (`mkBlk`, `zpad`, a `TBlk` literal), or it is named like certificate
data (`tc_*`, `certH*`, `parH*`, `S<k>…`, `F<k>…`, anything in `Case1Data`).
Usage: python3 scripts/skeleton.py ThomsonN7/Solution.lean > SKELETON.lean.txt
"""
import collections, re, sys

src = open(sys.argv[1]).read()
L = src.split('\n')
NUM = re.compile(r'^-?(0x[0-9a-f]+|\d+(/\d+)?|\d+e-?\d+)$')
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private |protected |noncomputable )*"
                  r"(theorem|lemma|def|abbrev|structure|instance|inductive)\s+(\S+)")
BND = re.compile(r'^(namespace|section|end|open|/--|/-!|@\[)|' + DECL.pattern[1:])

groups = collections.OrderedDict()
counts = collections.Counter()
for i in (i for i, l in enumerate(L) if i >= 310 and DECL.match(l)):
    j = next((t for t in range(i + 1, len(L)) if BND.match(L[t])), len(L))
    body = ' '.join(L[i:j])
    kind, name = DECL.match(L[i]).groups()
    sec = next(m.group(1) or m.group(2) for t in range(i, -1, -1)
               if (m := re.match(r'^section (Asm_\S+)|^namespace (\S+)', L[t])))
    toks = [re.sub(r'[\[\](),⟨⟩]', '', x) for x in body.split()]
    data = kind in ('def', 'abbrev') and (
        sum(1 for x in toks if NUM.match(x)) >= 0.3 * len(toks) or 'mkBlk' in body or 'zpad' in body
        or ('TBlk' in body and re.search(r'\bmons\d\b', body)) or sec == 'Case1Data'
        or name.startswith('tc_') or re.match(r'cert[A-Z]|par[A-Z]|S\d|F\d', name))
    counts['data' if data else kind] += 1
    if data:
        continue
    stmt = ' '.join(re.split(r':=|\bwhere\b|\n\s*\|', '\n'.join(L[i:j]))[0].split())
    groups.setdefault(sec, []).append(stmt)

kept = [s for ss in groups.values() for s in ss]
print(f'-- Statement skeleton of Solution.lean: {len(kept)} declarations, '
      f'{sum(len(s.split()) for s in kept)} words; left out {counts["data"]} data definitions.')
print('-- Not valid Lean: proofs and definition bodies are cut at `:=`.')
for sec, ss in groups.items():
    print(f'\n-- ## {sec} ({len(ss)} declarations, {sum(len(s.split()) for s in ss)} words)')
    for s in ss:
        print(s)
