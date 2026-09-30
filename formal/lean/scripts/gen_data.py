"""Write certificate data as plain numerals.

* `(N : Int)` / `(-N : Int)` inside `List Int` data: the ascription is redundant (same elaborated term).
* `Int.ofNat (nat_lit N)` → `N`, `Int.negSucc (nat_lit N)` → `-(N+1)` (evaluated), `nat_lit N` → `N`.

Only lines longer than 300 characters after the protected preamble (line 310) are touched.
Usage: python3 scripts/gen_data.py <in.lean> <out.lean> [--ascriptions-only]
"""
import re, sys

src, dst = sys.argv[1], sys.argv[2]
only_asc = '--ascriptions-only' in sys.argv
L = open(src).read().split('\n')
n_changed = 0
for i, l in enumerate(L):
    if i < 310 or len(l) <= 300:
        continue
    new = re.sub(r'\((-?\d+) : Int\)', r'\1', l)
    if not only_asc:
        new = re.sub(r'Int\.ofNat \(nat_lit (\d+)\)', r'\1', new)
        new = re.sub(r'Int\.negSucc \(nat_lit (\d+)\)', lambda m: f'-{int(m.group(1)) + 1}', new)
        new = re.sub(r'nat_lit (\d+)', r'\1', new)
    if new != l:
        L[i] = new
        n_changed += 1
open(dst, 'w').write('\n'.join(L))
print('lines changed:', n_changed)
