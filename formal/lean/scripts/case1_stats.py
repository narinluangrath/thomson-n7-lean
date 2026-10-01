"""Splice the 13 Case-1 chunk statistics (from `#eval` output) into the regenerated Solution.lean.

Input lines `c1_stat_X (l1, dx, dy, dz, kev)`. Also recomputes the total of `c1_idE_stat` exactly as
`c1Stat_idE` combines the pieces, and checks `log2 l1 + 1 = 179` and total Kronecker value `0`.
Usage: python3 scripts/case1_stats.py <eval-output> <in.lean> <out.lean>
"""
import re, sys
sys.set_int_max_str_digits(0)

N = 7
stats = {}
for m in re.finditer(r'(c1_stat_\w+) \((\d+),\s*(\d+),\s*(\d+),\s*(\d+),\s*(-?\d+)\)', re.sub(r'\s+', ' ', open(sys.argv[1]).read())):
    stats[m.group(1)] = tuple(int(x) for x in m.groups()[1:])
assert len(stats) == 13, sorted(stats)


def add(s, t): return (s[0] + t[0], max(s[1], t[1]), max(s[2], t[2]), max(s[3], t[3]), s[4] + t[4])
def mul(s, t): return (s[0] * t[0], s[1] + t[1], s[2] + t[2], s[3] + t[3], s[4] * t[4])
def C(a): return (abs(a), 0, 0, 0, a)
def sub(s, t): return add(s, mul(C(-1), t))
def ssum(l):
    r = C(0)
    for x in reversed(l):
        r = add(x, r)
    return r


src = open(sys.argv[2]).read()
W = int(re.search(r"c1Stat (\d+) 11 Case1Data.cf.idE", src).group(1))
eps = int(re.search(r'eps := \((-?\d+) : Int\)', src).group(1))
c2 = N * (N - 1) // 2
F = ssum([stats[f'c1_stat_F{k}'] for k in range(4)])
S = ssum([stats[f'c1_stat_S{r}'] for r in range(8)])
tot = sub(sub(sub(mul(C(2 * (N - 1) * c2), stats['c1_stat_H']), C(6 * (N - 1) * eps)), mul(C(c2), F)),
          mul(C(6 * (N - 1) * c2), S))
print('total l1 bits', tot[0].bit_length(), ' degrees', tot[1:4], ' kev == 0:', tot[4] == 0)
assert tot[4] == 0 and tot[0].bit_length() == W and max(tot[1:4]) + 1 <= 11


def lit(s):
    k = str(s[4]) if s[4] >= 0 else f'(({s[4]}) : Int)'
    return f'({s[0]}, {s[1]}, {s[2]}, {s[3]}, {k})'


for name, s in stats.items():
    src, n = re.subn(rf'(theorem {name} :\n    c1Stat {W} 11 \(.*?\)) = \(.*?\) := by', lambda m: f'{m.group(1)} = {lit(s)} := by',
                     src, count=1, flags=re.S)
    assert n == 1, name
src, n = re.subn(rf'(theorem c1_idE_stat : c1Stat {W} 11 Case1Data.cf.idE = \()\d+(, 10, 10, 10, \(0 : Int\)\))',
                 lambda m: f'{m.group(1)}{tot[0]}{m.group(2)}', src, count=1)
assert n == 1 and tot[1:4] == (10, 10, 10)
open(sys.argv[3], 'w').write(src)
print('written', sys.argv[3])
