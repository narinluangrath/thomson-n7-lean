"""Regenerate the Case-1 certificate with smaller SOS blocks for the multipliers 1-u, 1-v, 1-t.

1. Solve the SDP (floats, cvxpy/Clarabel) with e fixed at E(P) + MARGIN, maximising the smallest eigenvalue
   margin λ of every PSD block (so rounding keeps them PSD).
2. Exactify over Λ = 2^160: h ∈ 6ℤ, eps ∈ 42ℤ, F-matrices ∈ 72ℤ, SOS Gram matrices ∈ 2ℤ (then every
   coefficient of 252 hE - 36 eps - 21 F_tot - 756 Σ sos is a multiple of 1512), and absorb the remaining
   exact residual into the degree-5 block S0 (every monomial of degree ≤ 10 is a product of two basis monomials).
3. Check the identity residual is exactly zero (case1_model), factor every block as ⟨d, l, Δ⟩ with Δ diagonally
   dominant (rounded L D Lᵀ of M - μI, scale 2^55), check H ≤ φ by the Bernstein test, and write the Lean data.

Usage: PYTHONPATH=<pylib> python3 scripts/case1_gen.py <Solution.lean> <out.lean>
"""
import math, re, sys
import numpy as np
import cvxpy as cp
import scipy.sparse as sps
sys.path.insert(0, 'scripts')
import case1_model as M

EP = 14.452977414221342
MARGIN = 1.0e-3
LAM = 2 ** 160
CUT = -0.9
SOS = [([], 'mons5'), ([10], 'mons4'), ([11], 'mons4'), ([12], 'mons4'),
       ([4], 'mons0'), ([6], 'mons0'), ([8], 'mons0'), ([3], 'mons3')]
FSIZES = [6, 5, 4, 3]


def solve(mons):
    D = 10
    allm = [m for s in range(D + 1) for m in M.monos(s)]
    idx = {m: i for i, m in enumerate(allm)}
    N = len(allm)
    lam = cp.Variable()
    cons = []

    def lin(polys, shape):  # list of (column, poly) -> sparse N × shape
        rows, cols, vals = [], [], []
        for col, p in polys:
            for mo, c in p.items():
                rows.append(idx[mo]); cols.append(col); vals.append(float(c))
        return sps.csr_matrix((vals, (rows, cols)), shape=(N, shape))

    # h part: 252 hE
    h = cp.Variable(11)
    hpart = lin([(j, {(j, 0, 0): 252, (0, j, 0): 252, (0, 0, j): 252} if j else {(0, 0, 0): 756}) for j in range(11)], 11) @ h
    e = EP + MARGIN
    const = np.zeros(N); const[idx[(0, 0, 0)]] = -36 * e
    # F part: -21 F_tot
    Fs, fpart = [], 0
    for k, m in enumerate(FSIZES):
        F = cp.Variable((m, m), symmetric=True)
        Fs.append(F)
        cons.append(F - lam * np.eye(m) >> 0)
        cols = []
        for a in range(m):
            for c in range(m):
                Mk = [[1 if (x, y) == (a, c) else 0 for y in range(m)] for x in range(m)]
                fp = {(a, c, 0): 1}
                f = M.pmul(fp, M.Q(k))
                ft = M.padd(M.pscale(30, M.six(0, 1, 2, f)),
                            M.pscale(6, M.padd(M.six(0, 0, 3, f), M.six(1, 1, 3, f), M.six(2, 2, 3, f))), M.six(3, 3, 3, f))
                cols.append((a * m + c, M.pscale(-21, ft)))
        fpart = fpart + lin(cols, m * m) @ cp.vec(F, order='C')
    # SOS part: -756 Σ g zᵀ B z
    Bs, spart = [], 0
    for g, zname in SOS:
        z = mons[zname]
        B = cp.Variable((len(z), len(z)), symmetric=True)
        Bs.append(B)
        cons.append(B - lam * np.eye(len(z)) >> 0)
        gp = M.ONE
        for code in g:
            gp = M.pmul(M.CODES[code], gp)
        cols = []
        for a, za in enumerate(z):
            for c, zc in enumerate(z):
                cols.append((a * len(z) + c, M.pscale(-756, M.pmul(gp, {(za[0] + zc[0], za[1] + zc[1], za[2] + zc[2]): 1}))))
        spart = spart + lin(cols, len(z) ** 2) @ cp.vec(B, order='C')
    cons.append(hpart + const + fpart + spart == 0)
    # H ≤ φ on [-9/10, 1): 1 - 2y H(1-2y²) = σ0 + y σ1 + (b2-y²) σ2 + y (b2-y²) σ3   (Lukács on [0, √b2])
    b2 = (1 - CUT) / 2
    deg = 21
    qrows, qcols, qvals = [], [], []
    for j in range(11):
        base = np.polynomial.polynomial.polypow([1, 0, -2], j)
        for p, c in enumerate(base):
            qrows.append(p + 1); qcols.append(j); qvals.append(-2 * c)
    qvec = sps.csr_matrix((qvals, (qrows, qcols)), shape=(deg + 1, 11)) @ h + np.eye(deg + 1)[0]
    terms = []
    for mult, dd in (([1], 10), ([0, 1], 10), ([b2, 0, -1], 9), ([0, b2, 0, -1], 9)):
        G = cp.Variable((dd + 1, dd + 1), symmetric=True)
        cons.append(G - lam * 1e-3 * np.eye(dd + 1) >> 0)
        rows, cols, vals = [], [], []
        for i in range(dd + 1):
            for jj in range(dd + 1):
                for p, c in enumerate(mult):
                    if c and i + jj + p <= deg:
                        rows.append(i + jj + p); cols.append(i * (dd + 1) + jj); vals.append(c)
        terms.append(sps.csr_matrix((vals, (rows, cols)), shape=(deg + 1, (dd + 1) ** 2)) @ cp.vec(G, order='C'))
    cons.append(qvec == sum(terms))
    cons.append(lam <= 1)
    prob = cp.Problem(cp.Maximize(lam), cons)
    prob.solve(solver=cp.CLARABEL)
    print('SDP:', prob.status, ' λ =', lam.value, flush=True)
    return h.value, [F.value for F in Fs], [B.value for B in Bs]


def rnd(x, q):
    return q * int(round(x / q))


def exactify(h, Fs, Bs, mons):
    hI = [rnd(x * LAM, 6) for x in h]
    eps = 42 * math.floor((EP + MARGIN) * LAM / 42)
    FI = [[[rnd(F[a][c] * LAM, 72) for c in range(len(F))] for a in range(len(F))] for F in Fs]
    for F in FI:  # symmetrise
        for a in range(len(F)):
            for c in range(a):
                F[a][c] = F[c][a]
    GI = []
    for B in Bs:
        G = [[rnd(B[a][c] * LAM, 2) for c in range(len(B))] for a in range(len(B))]
        for a in range(len(G)):
            for c in range(a):
                G[a][c] = G[c][a]
        GI.append(G)
    Sb = [(g, 0, mons[zn], G) for (g, zn), G in zip(SOS, GI)]
    res = M.residual(hI, eps, FI, Sb)  # = -756 (needed correction to zᵀ G0 z)
    z0 = mons['mons5']
    diag = {}
    pair = {}
    for a, za in enumerate(z0):
        for c, zc in enumerate(z0):
            key = (za[0] + zc[0], za[1] + zc[1], za[2] + zc[2])
            if a == c:
                diag.setdefault(key, a)
            elif a < c:
                pair.setdefault(key, (a, c))
    G0 = GI[0]
    for mo, r in res.items():
        assert r % 756 == 0, (mo, r % 756)
        delta = r // 756  # add to zᵀG0z
        if mo in diag:
            G0[diag[mo]][diag[mo]] += delta
        else:
            assert delta % 2 == 0, mo
            a, c = pair[mo]
            G0[a][c] += delta // 2; G0[c][a] += delta // 2
    res2 = M.residual(hI, eps, FI, Sb)
    assert not res2, 'residual not zero'
    print('exact identity: residual = 0', flush=True)
    return hI, eps, FI, GI


S_LDL = 2 ** 55


def rdiv(a, b):
    return (2 * a + b) // (2 * b)


def ldl(Mx, mu):
    n = len(Mx)
    A = [[Mx[i][j] - (mu if i == j else 0) for j in range(n)] for i in range(n)]
    d, l = [], []
    for q in range(n):
        P = A[q][q]
        if P <= 0:
            return None
        col = [0 if i < q else (S_LDL if i == q else rdiv(S_LDL * A[i][q], P)) for i in range(n)]
        dq = rdiv(P, S_LDL * S_LDL)
        A = [[A[i][j] - dq * col[i] * col[j] for j in range(n)] for i in range(n)]
        d.append(dq); l.append(col)
    Dl = [[A[i][j] + (mu if i == j else 0) for j in range(n)] for i in range(n)]
    ok = all(x >= 0 for x in d) and all(sum(abs(Dl[i][j]) for j in range(n) if j != i) <= Dl[i][i] for i in range(n))
    return (d, l, Dl) if ok else None


def factor(Mx):
    if len(Mx) == 1:
        return ([], [], [[Mx[0][0]]]) if Mx[0][0] >= 0 else None
    w = np.linalg.eigvalsh(np.array(Mx, dtype=float))
    for frac in (0.5, 0.25, 0.75, 0.1, 0.9):
        b = ldl(Mx, int(w.min() * frac))
        if b:
            return b
    return None


def bern_ok(Lam, Q, B=974680, D=10 ** 6, depth=6):
    def padd(p, q): return [(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0) for i in range(max(len(p), len(q)))]
    def pmul(p, q):
        r = [0] * (len(p) + len(q) - 1) if p and q else []
        for i, a in enumerate(p):
            for j, b in enumerate(q): r[i + j] += a * b
        return r
    def ppow(p, k):
        r = [1]
        for _ in range(k): r = pmul(p, r)
        return r
    cq = []
    for c in reversed(Q): cq = padd(pmul(cq, [1, 0, -2]), [c])
    p = padd([Lam], [-x for x in pmul([0, 2], cq)])
    def bern(A, Bb, Dd):
        n = len(p) - 1; r = []
        for k, c in enumerate(p):
            if c: r = padd(r, [c * x for x in pmul(ppow([A, Bb], k), ppow([Dd, Dd], n - k))])
        return r
    def ok(d, A, Bb, Dd):
        if all(x >= 0 for x in bern(A, Bb, Dd)): return True
        return d > 0 and ok(d - 1, 2 * A, A + Bb, 2 * Dd) and ok(d - 1, A + Bb, 2 * Bb, 2 * Dd)
    return ok(depth, 0, B, D)


def lean_list(xs):
    return '[' + ', '.join(str(x) for x in xs) + ']'


def lean_col(xs):
    k = 0
    while k < len(xs) and xs[k] == 0:
        k += 1
    return f'zpad {k} {lean_list(xs[k:])}' if k >= 3 and k < len(xs) else lean_list(xs)


def emit_blk(name, b):
    d, l, Dl = b
    out = [f'def {name}_d : List Int := {lean_list(d)}']
    for q, col in enumerate(l):
        out.append(f'def {name}_l_{q} : List Int := {lean_col(col)}')
    out.append(f'def {name}_l : List (List Int) := [{", ".join(f"{name}_l_{q}" for q in range(len(l)))}]')
    for a, row in enumerate(Dl):
        out.append(f'def {name}_D_{a} : List Int := {lean_list(row)}')
    out.append(f'def {name}_D : List (List Int) := [{", ".join(f"{name}_D_{a}" for a in range(len(Dl)))}]')
    out.append(f'def {name} : Blk := ⟨{name}_d, {name}_l, {name}_D⟩')
    return '\n'.join(out)


if __name__ == '__main__':
    src = open(sys.argv[1]).read()
    mons = {m: [tuple(map(int, t)) for t in re.findall(r'\((\d+), (\d+), (\d+)\)', v)]
            for m, v in re.findall(r'^def (mons\d) : List \(ℕ × ℕ × ℕ\) := (.*)$', src, re.M)}
    mons['mons0'] = [(0, 0, 0)]
    h, Fs, Bs = solve(mons)
    hI, eps, FI, GI = exactify(h, Fs, Bs, mons)
    print('e - E(P) =', eps / LAM - EP, flush=True)
    assert bern_ok(LAM, hI), 'H ≤ φ Bernstein check fails'
    print('H ≤ φ: Bernstein check passes', flush=True)
    blocks = []
    for k, F in enumerate(FI):
        b = factor(F); assert b, f'F{k} not factorable'; blocks.append((f'F{k}', b))
    for r, G in enumerate(GI):
        b = factor(G); assert b, f'S{r} not factorable'; blocks.append((f'S{r}_B', b))
    print('all blocks factor with diagonally dominant remainder', flush=True)
    # write the new Case1Data body
    s = src.index('namespace Case1Data')
    e = src.index('end Case1Data', s)
    body = src[s:e]
    head = body[:body.index('def h_ ')]
    parts = [head.rstrip('\n'), '', f'def h_ : List Int := {lean_list(hI)}']
    for name, b in blocks:
        parts.append(emit_blk(name, b))
        if name.startswith('S'):
            r = int(name[1])
            g, zn = SOS[r]
            zdef = zn if zn != 'mons0' else '[(0, 0, 0)]'
            parts.append(f'def S{r}_z : List (Nat × Nat × Nat) := {zdef}')
            parts.append(f'def S{r} : SBlk := ⟨{lean_list(g) if g else "[]"}, (0 : Nat), S{r}_z, S{r}_B⟩')
    cf = body[body.index('def cf : Cert3'):]
    cf = re.sub(r'eps := \(?-?\d+[^,]*', f'eps := ({eps} : Int)', cf, count=1)
    parts.append(cf.rstrip('\n'))
    newbody = '\n'.join(parts) + '\n'
    out = src[:s] + newbody + src[e:]
    # the 1D certificate shares Q with h
    out = re.sub(r'(def cutCert : Cert where\n  Lam := \d+\n  Q := )\[[^\]]*\]', lambda m: m.group(1) + lean_list(hI), out)
    open(sys.argv[2], 'w').write(out)
    print('written', sys.argv[2])
