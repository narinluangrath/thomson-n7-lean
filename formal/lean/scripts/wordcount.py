"""Word counts for Solution.lean: total, data, proof (everything else, minus comments/blank lines).

A line is data if at least half of its tokens are numerals (with brackets/commas/parens stripped) and it
has at least 8 tokens, independent of how the numerals are encoded or how long the line is.
Usage: python3 scripts/wordcount.py <file>
"""
import re, sys

NUM = re.compile(r'^-?(0x[0-9a-f]+|\d+(/\d+)?)$')
WRAP = {'Int.ofNat', 'Int.negSucc', 'nat_lit', 'Int', ':', 'Int)', ':=', 'Nat'}
total = data = proof = 0
for line in open(sys.argv[1]):
    toks = line.split()
    total += len(toks)
    core = [re.sub(r'[\[\](),⟨⟩]', '', t) for t in toks]
    nums = sum(1 for t in core if NUM.match(t))
    wraps = sum(1 for t in core if t in WRAP or t == '')
    if len(toks) >= 8 and (nums + wraps) >= 0.5 * len(toks):
        data += len(toks)
    elif toks and not toks[0].startswith('--'):
        proof += len(re.sub(r'--.*', '', line).split())
print(f'total {total}  data {data}  proof {proof}')
