"""Case1Data SOS blocks as matrices: the kernel computes the integer L D Lᵀ + Δ split itself.

Each `S#_B : Blk` was stored as pivots `d`, columns `l` and a dense remainder `Δ`. Only
`M = Σ d l lᵀ + Δ` matters (the checker verifies Δ symmetric and diagonally dominant, d ≥ 0). We store
the upper triangle of M and a shift μ; `ldlBlk` runs a rounded integer elimination of `M - μ I`
(scale S = 2^55, round-to-nearest) and returns ⟨d, l, final Schur complement + μ I⟩, so the check is unchanged.

Usage: python3 scripts/gen_case1.py <in.lean> <out.lean> [--emit-test K]
"""
import re, sys

S = 2 ** 55
LEAN_DEFS = '''/-- `a / b` rounded to the nearest integer (for `b > 0`). -/
def rdiv (a b : ℤ) : ℤ := (2 * a + b) / (2 * b)

/-- One rounded elimination step at pivot `q`: pivot `d_q`, column `l_q` (scaled by `2^55`), updated matrix. -/
def ldlStep (q : ℕ) (A : List (List ℤ)) : ℤ × List ℤ × List (List ℤ) :=
  let P := (A.getD q []).getD q 0
  let col := (List.range A.length).zipWith (fun i row =>
    if i < q then 0 else if i = q then 2 ^ 55 else rdiv (2 ^ 55 * row.getD q 0) P) A
  let d := rdiv P (2 ^ 55 * 2 ^ 55)
  (d, col, A.zipWith (fun row ci => row.zipWith (fun x cj => x - d * ci * cj) col) col)

/-- The block of `M` (given by its upper triangle, row `i` = `M i i, M i (i+1), …`) with shift `μ`:
rounded `L D Lᵀ` of `M - μ I`, remainder `Δ = M - Σ d l lᵀ`. -/
def ldlBlk (U : List (List ℤ)) (μ : ℤ) : Blk :=
  let n := U.length
  let ent (i j : ℕ) : ℤ := if i ≤ j then (U.getD i []).getD (j - i) 0 else (U.getD j []).getD (i - j) 0
  let A := (List.range n).map fun i => (List.range n).map fun j => ent i j - if i = j then μ else 0
  let r := (List.range n).foldl (fun (acc : List ℤ × List (List ℤ) × List (List ℤ)) q =>
    let s := ldlStep q acc.2.2
    (acc.1 ++ [s.1], acc.2.1 ++ [s.2.1], s.2.2)) ([], [], A)
  ⟨r.1, r.2.1, (List.range n).zipWith (fun i row =>
    (List.range n).zipWith (fun j x => x + if i = j then μ else 0) row) r.2.2⟩
'''


def rdiv(a, b):
    return (2 * a + b) // (2 * b)


def parse(src):
    s = src.index('namespace Case1Data')
    e = src.index('end Case1Data', s)
    body = src[s:e]
    defs = {n: v for n, v in re.findall(r'^def (\S+) : [^:=]+:= (.*)$', body, re.M)}
    nl = lambda v: [int(x) for x in re.findall(r'-?\d+', v)]
    blocks = {}
    for k in range(8):
        nm = f'S{k}_B'
        if nm + '_d' not in defs:
            continue
        d0 = nl(defs[nm + '_d'])
        r = len(d0)
        l0 = [nl(defs[f'{nm}_l_{q}']) for q in range(r)]
        D0 = [nl(defs[f'{nm}_D_{a}']) for a in range(r)]
        M = [[sum(d0[q] * l0[q][a] * l0[q][c] for q in range(r)) + D0[a][c] for c in range(r)] for a in range(r)]
        mu = min(D0[i][i] for i in range(r)) // 2
        blocks[nm] = (M, mu)
    return blocks


def ldl(M, mu):
    """Exactly what the Lean `ldlBlk` computes."""
    n = len(M)
    A = [[M[i][j] - (mu if i == j else 0) for j in range(n)] for i in range(n)]
    d, l = [], []
    for q in range(n):
        P = A[q][q]
        col = [0 if i < q else (S if i == q else rdiv(S * A[i][q], P)) for i in range(n)]
        dq = rdiv(P, S * S)
        A = [[A[i][j] - dq * col[i] * col[j] for j in range(n)] for i in range(n)]
        d.append(dq); l.append(col)
    Delta = [[A[i][j] + (mu if i == j else 0) for j in range(n)] for i in range(n)]
    return d, l, Delta


def ok(d, l, Delta):
    n = len(d)
    return all(x >= 0 for x in d) and all(Delta[i][j] == Delta[j][i] for i in range(n) for j in range(n)) and \
        all(sum(abs(Delta[i][j]) for j in range(n) if j != i) <= Delta[i][i] for i in range(n))


def upper_defs(nm, M):
    """Row defs `nm_M_i : List ℤ` (upper triangle) and the list of them (big nested literals elaborate slowly)."""
    rows = ''.join(f'def {nm}_M_{i} : List ℤ := [' + ', '.join(str(x) for x in M[i][i:]) + ']\n' for i in range(len(M)))
    return rows, '[' + ', '.join(f'{nm}_M_{i}' for i in range(len(M))) + ']'


if __name__ == '__main__':
    src = open(sys.argv[1]).read()
    blocks = parse(src)
    for nm, (M, mu) in blocks.items():
        assert ok(*ldl(M, mu)), nm
    print('all blocks pass the Blk.ok conditions in Python:', len(blocks))
    if '--emit-test' in sys.argv:
        k = sys.argv[sys.argv.index('--emit-test') + 1]
        M, mu = blocks[f'S{k}_B']
        d, l, D = ldl(M, mu)
        rows, lst = upper_defs('T', M)
        open(sys.argv[2], 'w').write(LEAN_DEFS + '\n' + rows + f'def testB : Blk := ldlBlk {lst} {mu}\n'
            f'theorem test_d : testB.d = {d} := by decide +kernel\n'
            f'theorem test_ok : testB.ok {len(M)} = true := by decide +kernel\n')
        sys.exit()
    # rewrite the file
    s = src.index('namespace Case1Data')
    e = src.index('end Case1Data', s)
    body = src[s:e]
    for nm, (M, mu) in blocks.items():
        body = re.sub(r'^def ' + nm + r'_(d|l|D)(_\d+)? : [^\n]*\n', '', body, flags=re.M)
        rows, lst = upper_defs(nm, M)
        body = re.sub(r'^def ' + nm + r' : Blk := [^\n]*$', lambda _: rows + f'def {nm} : Blk := ldlBlk {lst} {mu}', body, flags=re.M)
    head = re.search(r'^def ', body, re.M).start()  # after the section's `open`s
    body = body[:head] + LEAN_DEFS + '\n' + body[head:]
    open(sys.argv[2], 'w').write(src[:s] + body + src[e:])
    print('rewritten')
