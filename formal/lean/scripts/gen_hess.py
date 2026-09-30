"""Generate the `Reg.Hess` certificate block (Lean source) from Solution.lean's own data.

Reads the Hessian form `Fq` (which coefficient `CP_k` multiplies which monomial) and the
enclosures `enc_k : lo ≤ CP_k ≤ hi`, computes an `L D Lᵀ` factorisation of
`M₀ - (λ + μ) I` (M₀ = interval midpoints) rounded to dyadics, verifies exactly that the
remainder stays diagonally dominant for every matrix within the enclosures, and prints Lean.

Usage: python3 scripts/gen_hess.py > hess.lean
"""
import os, re, sys
from fractions import Fraction as Fr
import numpy as np

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
src = open(os.path.join(ROOT, 'ThomsonN7/Solution.lean')).read()
N, LAM, MU, BITS = 21, Fr(449, 100000), Fr(5, 100000), 20

q = lambda s: Fr(s.replace(' ', ''))
enc = {}
for m in re.finditer(r'lemma enc_(\d+) \(c s p q r : ℝ\) \(hb : InBox c s p q r\) :\n    \(([^:]+) : ℝ\) ≤ CP_\1 '
                     r'c s p q r ∧ CP_\1 c s p q r ≤ \(([^:]+) : ℝ\)', src):
    enc[int(m.group(1))] = (q(m.group(2)), q(m.group(3)))
K = len(enc)
assert sorted(enc) == list(range(K))
fq = src[src.index('noncomputable def Fq'):]
fq = fq[:fq.index('\n\n')]
idx = [[K] * N for _ in range(N)]
for k, i, j in re.findall(r'CP_(\d+) c s p q r \* \(x(\d+)(?: \^ 2| \* x(\d+))\)', fq):
    i, j = int(i), int(j) if j else int(i)
    idx[i][j] = idx[j][i] = int(k)

wt = lambda i, j: Fr(1) if i == j else Fr(1, 2)
mid = lambda k: (enc[k][0] + enc[k][1]) / 2 if k < K else Fr(0)
rad = lambda k: (enc[k][1] - enc[k][0]) / 2 if k < K else Fr(0)
M0 = [[wt(i, j) * mid(idx[i][j]) for j in range(N)] for i in range(N)]
dl = [[wt(i, j) * rad(idx[i][j]) for j in range(N)] for i in range(N)]

A = np.array([[float(M0[i][j] - (LAM + MU if i == j else 0)) for j in range(N)] for i in range(N)])
Lf, Df = np.eye(N), np.zeros(N)
for j in range(N):
    Df[j] = A[j, j] - sum(Lf[j, k] ** 2 * Df[k] for k in range(j))
    for i in range(j + 1, N):
        Lf[i, j] = (A[i, j] - sum(Lf[i, k] * Lf[j, k] * Df[k] for k in range(j))) / Df[j]
rd = lambda x: Fr(round(x * 2 ** BITS), 2 ** BITS)
L = [[rd(Lf[i][j]) if i > j else Fr(int(i == j)) for j in range(N)] for i in range(N)]
D = [rd(Df[i]) for i in range(N)]
R = [[M0[i][j] - (LAM if i == j else 0) - sum(L[i][k] * D[k] * L[j][k] for k in range(N)) for j in range(N)]
     for i in range(N)]
slack = min(R[i][i] - dl[i][i] - sum(abs(R[i][j]) + dl[i][j] for j in range(N) if j != i) for i in range(N))
assert all(d >= 0 for d in D) and slack > 0, slack
print(f'-- exact check in Python: min diagonal-dominance slack {float(slack):.2e}', file=sys.stderr)

fr = lambda x: str(x.numerator) if x.denominator == 1 else f'{x.numerator}/{x.denominator}'
lst = lambda xs: '[' + ', '.join(xs) + ']'
cp = ', '.join(f'CP_{k} c s p q r' for k in range(K))
Lrows = lst(lst(fr(L[i][j]) for j in range(i)) for i in range(N))
print(f'''/-! ### The Hessian certificate as data

`Fq = ∑ᵢⱼ xᵢ Hm i j xⱼ`. With `M₀` the midpoints of the enclosures `enc_k` and `δ` their radii,
`Hm - λ I = L D Lᵀ + (R + E)` where `R = M₀ - λ I - L D Lᵀ` is computed from the data below and
`|E| ≤ δ` entrywise; `check` verifies `D ≥ 0` and that `R + E` is diagonally dominant for every such `E`. -/

namespace Hess

/-- The coefficients `CP_k`, indexed (`0` past the end). -/
noncomputable def cp (c s p q r : ℝ) (k : ℕ) : ℝ := [{cp}].getD k 0

/-- Lower and upper ends of the enclosures `enc_k`. -/
def lo : List ℚ := {lst(fr(enc[k][0]) for k in range(K))}
def hi : List ℚ := {lst(fr(enc[k][1]) for k in range(K))}

/-- Entry `(i, j)` of the Hessian matrix is `wt i j * cp (ix i j)`; index {K} means zero. -/
def idx : List (List ℕ) := {lst(lst(str(x) for x in row) for row in idx)}

/-- Strictly lower part of `L` (unit diagonal) and the pivots `D`. -/
def Ld : List (List ℚ) := {Lrows}
def Dd : List ℚ := {lst(fr(x) for x in D)}

def ix (i j : ℕ) : ℕ := (idx.getD i []).getD j {K}
def wt (i j : ℕ) : ℚ := if i = j then 1 else 1 / 2
def mid (k : ℕ) : ℚ := (lo.getD k 0 + hi.getD k 0) / 2
def rad (k : ℕ) : ℚ := (hi.getD k 0 - lo.getD k 0) / 2
def M0 (i j : ℕ) : ℚ := wt i j * mid (ix i j)
def dl (i j : ℕ) : ℚ := wt i j * rad (ix i j)
def Lq (i j : ℕ) : ℚ := if i = j then 1 else (Ld.getD i []).getD j 0
def Dq (i : ℕ) : ℚ := Dd.getD i 0
def lam : ℚ := {fr(LAM)}
def ldl (i j : ℕ) : ℚ := ((List.range {N}).map fun k => Lq i k * Dq k * Lq j k).sum
def res (i j : ℕ) : ℚ := M0 i j - (if i = j then lam else 0) - ldl i j

/-- The computable check. -/
def check : Bool :=
  (List.range {N}).all fun i => decide (0 ≤ Dq i) &&
    (List.range {N}).all (fun j => decide (ix i j = ix j i) && decide (res i j = res j i)) &&
    decide (((List.range {N}).map fun j => if i = j then dl i i else |res i j| + dl i j).sum ≤ res i i)

theorem check_ok : check = true := by decide +kernel

end Hess''')
