"""Case1Data: write triangular L columns without their leading zeros.

`def X : List Int := [0, 0, 0, 0, a, b, …]` becomes `def X : List Int := zpad 4 [a, b, …]` with
`zpad k xs = List.replicate k 0 ++ xs` (same value). Only runs of at least 3 leading zeros are rewritten.
Usage: python3 scripts/gen_zpad.py <in.lean> <out.lean>
"""
import re, sys

src = open(sys.argv[1]).read()
s = src.index('namespace Case1Data')
e = src.index('end Case1Data', s)
body = src[s:e]
n = saved = 0


def repl(m):
    global n, saved
    items = [x.strip() for x in m.group(2).split(',')]
    k = 0
    while k < len(items) and items[k] == '0':
        k += 1
    if k < 3 or k == len(items):
        return m.group(0)
    n += 1
    saved += k - 2
    return f'def {m.group(1)} : List Int := zpad {k} [{", ".join(items[k:])}]'


body = re.sub(r'^def (\S+) : List Int := \[([^\]]*)\]$', repl, body, flags=re.M)
head = re.search(r'^def ', body, re.M).start()
body = body[:head] + ('/-- `k` zeros followed by `xs` (triangular columns are stored without their zero prefix). -/\n'
                      'def zpad (k : ℕ) (xs : List ℤ) : List ℤ := List.replicate k 0 ++ xs\n\n') + body[head:]
open(sys.argv[2], 'w').write(src[:s] + body + src[e:])
print('columns rewritten:', n, ' zeros removed (net of the 2 added words each):', saved)
