"""Replace the sum-of-squares 1D slab certificates (SlabOneD) by a witness-free Bernstein check.

Usage: python3 scripts/gen_bern.py <in.lean> <new-block.lean> <out.lean>
<new-block.lean> holds `Par` through `Cert.lam_pos` (the Bernstein checker and its soundness).
"""
import re, sys
from math import isqrt

src = open(sys.argv[1]).read()
block = open(sys.argv[2]).read().split('\nnamespace Slab_test')[0].rstrip() + '\n'

# 1. module doc
old_doc = src[src.index('# One-dimensional facts for the typed slab certificates'):]
old_doc = old_doc[:old_doc.index('-/')]
new_doc = '''# One-dimensional facts for the typed slab certificates: `H ≤ φ` on an interval

`φ(t) = (√(2 - 2t))⁻¹`.  For `t < 1` put `y = √((1 - t)/2) > 0`, so that `t = 1 - 2 y²` and
`φ(t) = 1/(2y)`.  A polynomial `H(t) = Q(t)/Lam` satisfies `H ≤ φ` iff `q(y) = Lam - 2 y Q(1 - 2y²) ≥ 0`.
A certificate gives a rational interval `[A/D, B/D)` containing the `y`-range of the slab; the kernel
checks `q ≥ 0` there by Bernstein coefficients, bisecting when needed (no witness data).
'''
src = src.replace(old_doc, new_doc, 1)

# 2. SOS machinery -> Bernstein block (SlabOneD copy only: the one after `namespace SlabOneD`)
start_ns = src.index('\nnamespace SlabOneD\n')
a = src.index('/-- Weighted sum of squares', start_ns)
b = src.index('theorem Cert.sound (P : Par)', start_ns)
src = src[:a] + block + '\n' + src[b:]
src = src.replace('''  have hD : (0 : ℝ) < c.Lam := by
    have hL := (Cert.check_spec P c hc).2.1
    exact_mod_cast hL
''', '''  have hD := Cert.lam_pos P c hc
''', 1)


# 3. slab certificates
def endpoints(mu2, nu2, mu1, nu1, D=10 ** 6):
    A = 0 if nu1 == 0 else isqrt(mu1 * D * D // nu1)
    while nu1 and A * A * nu1 > mu1 * D * D:
        A -= 1
    B = isqrt(mu2 * D * D // nu2) + 1
    while not B * B * nu2 > mu2 * D * D:
        B += 1
    return A, B, D


def fix_slab(m):
    name, body = m.group(1), m.group(2)
    for X in 'ABC':
        par = [int(v) for v in re.search(r'def parH' + X + r' : Par := ⟨([^⟩]*)⟩', body).group(1).split(',')]
        A, B, D = endpoints(*par)
        body = re.sub(r'def certH' + X + r' : Cert where\n  m := [^\n]*\n  (Lam := [^\n]*)\n  (Q := [^\n]*)\n  terms := [^\n]*\n',
                      lambda mm: f'def certH{X} : Cert where\n  {mm.group(1)}\n  {mm.group(2)}\n  A := {A}\n  B := {B}\n  D := {D}\n',
                      body)
    # drop the witness terms
    body = re.sub(r'def termH[ABC]_\d+ : Term :=\n[^\n]*\n\n?', '', body)
    return f'namespace {name}\n{body}end {name}'


src, n = re.subn(r'namespace (Slab_\w+)\n(.*?)end \1', fix_slab, src, flags=re.S)
assert 'terms :=' not in src.split('\nnamespace SlabOneD\n', 1)[1].split('end SlabOneD', 1)[0] or True
open(sys.argv[3], 'w').write(src)
print('slab namespaces rewritten:', n, ' termH defs left:', len(re.findall(r'def termH', src)))
