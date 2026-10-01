"""Exact integer model of the Case-1 identity `Cert3.idE ≡ 0` (Lean: Cert3.idE, ftotE, sblkE, hE).

    252·hE(h) − 36·eps − 21·F_tot − 756·Σ_r g_r · zᵀ G_r z  ≡ 0       (n = 7)

with F_tot = Σ_k [30·six(0,1,2,f_k) + 6·(six(0,0,3,f_k)+six(1,1,3,f_k)+six(2,2,3,f_k)) + six(3,3,3,f_k)],
f_k = (Σ_ac M_k[a][c] u^a v^c) · Q_k(u,v,t), six = sum over the 6 orderings of variable codes
(code 3 = the constant 1), M = Σ d l lᵀ + Δ for a block ⟨d, l, Δ⟩.
`parse` reads Case1Data from Solution.lean; `residual` returns the identity's polynomial (dict).
"""
import re

N, AN, AD = 7, -9, 10


def padd(*ps):
    r = {}
    for p in ps:
        for k, c in p.items():
            r[k] = r.get(k, 0) + c
    return {k: c for k, c in r.items() if c}


def pmul(p, q):
    r = {}
    for (a, b, c), x in p.items():
        for (d, e, f), y in q.items():
            k = (a + d, b + e, c + f)
            r[k] = r.get(k, 0) + x * y
    return {k: c for k, c in r.items() if c}


def pscale(c, p):
    return {k: c * v for k, v in p.items() if c * v}


U, V, T, ONE = {(1, 0, 0): 1}, {(0, 1, 0): 1}, {(0, 0, 1): 1}, {(0, 0, 0): 1}


def Q(k):
    q0, q1 = ONE, padd(T, pscale(-1, pmul(U, V)))
    if k == 0:
        return q0
    w = pmul(padd(ONE, pscale(-1, pmul(U, U))), padd(ONE, pscale(-1, pmul(V, V))))
    a, b = q0, q1
    for _ in range(k - 1):
        a, b = b, padd(pscale(2, pmul(q1, b)), pscale(-1, pmul(w, a)))
    return b


def sbst(p, i, j, k):
    """Lean `sbst i j k`: u ↦ var_i, v ↦ var_j, t ↦ var_k (codes 0,1,2 = u,v,t; 3 = constant 1)."""
    r = {}
    for (a, b, d), c in p.items():
        e = [0, 0, 0, 0]
        e[i] += a; e[j] += b; e[k] += d
        key = (e[0], e[1], e[2])
        r[key] = r.get(key, 0) + c
    return {k: c for k, c in r.items() if c}


def six(i, j, k, p):
    return padd(*[sbst(p, *o) for o in ((i, j, k), (i, k, j), (j, i, k), (j, k, i), (k, i, j), (k, j, i))])


CODES = {0: padd(ONE, pscale(-1, pmul(U, U))), 1: padd(ONE, pscale(-1, pmul(V, V))),
         2: padd(ONE, pscale(-1, pmul(T, T))),
         3: padd(ONE, pscale(2, pmul(pmul(U, V), T)), pscale(-1, pmul(U, U)), pscale(-1, pmul(V, V)),
                 pscale(-1, pmul(T, T))),
         4: padd(ONE, pscale(-1, U)), 5: padd(ONE, U), 6: padd(ONE, pscale(-1, V)), 7: padd(ONE, V),
         8: padd(ONE, pscale(-1, T)), 9: padd(ONE, T),
         10: padd(pscale(AD, U), {(0, 0, 0): -AN}), 11: padd(pscale(AD, V), {(0, 0, 0): -AN}),
         12: padd(pscale(AD, T), {(0, 0, 0): -AN})}


def mat(d, l, D):
    r = len(D)
    return [[sum(d[q] * l[q][a] * l[q][c] for q in range(len(d))) + D[a][c] for c in range(r)] for a in range(r)]


def residual(h, eps, Fms, Sblocks):
    """Fms: list of integer matrices M_k; Sblocks: list of (g codes, sigma, z monomials, G matrix)."""
    hE = {}
    for j, hj in enumerate(h):
        for mo in ((j, 0, 0), (0, j, 0), (0, 0, j)):
            hE[mo] = hE.get(mo, 0) + hj
    ftot = {}
    for k, M in enumerate(Fms):
        fp = {}
        for a, row in enumerate(M):
            for c, x in enumerate(row):
                if x:
                    fp[(a, c, 0)] = fp.get((a, c, 0), 0) + x
        f = pmul(fp, Q(k))
        ftot = padd(ftot, pscale((N - 1) * (N - 2), six(0, 1, 2, f)),
                    pscale(N - 1, padd(six(0, 0, 3, f), six(1, 1, 3, f), six(2, 2, 3, f))), six(3, 3, 3, f))
    sos = {}
    for g, sigma, z, G in Sblocks:
        assert sigma == 0
        qf = {}
        for a, za in enumerate(z):
            for c, zc in enumerate(z):
                if G[a][c]:
                    key = (za[0] + zc[0], za[1] + zc[1], za[2] + zc[2])
                    qf[key] = qf.get(key, 0) + G[a][c]
        gp = ONE
        for code in g:
            gp = pmul(CODES[code], gp)
        sos = padd(sos, pmul(gp, qf))
    c2 = N * (N - 1) // 2
    return padd(pscale(2 * (N - 1) * c2, hE), {(0, 0, 0): -6 * (N - 1) * eps}, pscale(-c2, ftot),
                pscale(-6 * (N - 1) * c2, sos))


def monos(d):
    return [(a, b, c) for s in range(d + 1) for a in range(s, -1, -1) for b in range(s - a, -1, -1) for c in [s - a - b]]


def parse(src):
    s = src.index('namespace Case1Data')
    e = src.index('end Case1Data', s)
    body = src[s:e]
    defs = dict(re.findall(r'^def (\S+) : [^\n:=]*:= (.*)$', body, re.M))
    nl = lambda v: [int(x) for x in re.findall(r'-?\d+', v)]

    def ints(name):
        v = defs[name].strip()
        m = re.match(r'zpad (\d+) \[(.*)\]$', v)
        if m:
            return [0] * int(m.group(1)) + nl(m.group(2))
        return nl(v)

    def blk(prefix):
        d = ints(prefix + '_d')
        l = [ints(nm) for nm in re.findall(r'\w+', defs[prefix + '_l'])] if prefix + '_l' in defs else \
            [ints(f'{prefix}_l_{q}') for q in range(len(d))]
        D = [ints(nm) for nm in re.findall(r'\w+', defs[prefix + '_D'])] if prefix + '_D' in defs else \
            [ints(f'{prefix}_D_{a}') for a in range(len(d))]
        return d, l, D

    mons = {m: [tuple(map(int, t)) for t in re.findall(r'\((\d+), (\d+), (\d+)\)', v)]
            for m, v in re.findall(r'^def (mons\d) : List \(ℕ × ℕ × ℕ\) := (.*)$', src, re.M)}
    h = ints('h_')
    cf = defs['cf'] if 'cf' in defs else ''
    cfbody = body[body.index('def cf : Cert3'):]
    eps = int(re.search(r'eps := \(?(-?\d+)', cfbody).group(1))
    Lam = int(re.search(r'Lam := \(?(\d+)', cfbody).group(1))
    Fms = [mat(*blk(f'F{k}')) for k in range(4)]
    S = []
    for r in range(8):
        sb = re.search(r'⟨\[([^\]]*)\], \(?(\d+)', defs[f'S{r}']).groups()
        g = [int(x) for x in re.findall(r'\d+', sb[0])]
        zv = defs[f'S{r}_z'].strip()
        z = mons[zv] if zv in mons else [tuple(map(int, t)) for t in re.findall(r'\((\d+), (\d+), (\d+)\)', zv)]
        S.append((g, int(sb[1]), z, mat(*blk(f'S{r}_B'))))
    return dict(h=h, eps=eps, Lam=Lam, F=Fms, S=S)


if __name__ == '__main__':
    import sys
    data = parse(open(sys.argv[1] if len(sys.argv) > 1 else 'ThomsonN7/Solution.lean').read())
    r = residual(data['h'], data['eps'], data['F'], data['S'])
    print('Lam = 2^%d' % (data['Lam'].bit_length() - 1), ' F sizes', [len(M) for M in data['F']],
          ' S sizes', [len(s[2]) for s in data['S']], ' codes', [s[0] for s in data['S']])
    print('identity residual: %d nonzero coefficients' % len(r), '(exact zero)' if not r else list(r.items())[:3])
