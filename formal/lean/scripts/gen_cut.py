"""Share the SlabOneD polynomial/Bernstein block with CutOneD and give cutCert a Bernstein certificate.

* move `section Asm_SlabHead` (polynomial basics + Bernstein checker) to just before CutOneD,
* delete CutOneD's own copies (peval ... Cert.sound, peval_eq_sum); CutOneD opens SlabOneD,
* cutCert keeps Lam and Q (Case1Data checks them) and gets the interval [0, B/D),
* `CutOneD.peval*` references become `SlabOneD.peval*`; the bridge `slab_peval_eq_cut` goes.
Usage: python3 scripts/gen_cut.py <in.lean> <out.lean>
"""
import re, sys
from math import isqrt

src = open(sys.argv[1]).read()

# 1. move the SlabOneD head section before CASE1
a = src.index('section Asm_SlabHead')
a = src.rindex('\n', 0, a) + 1
if src[:a].rstrip().endswith('-/') and 'BEGIN' in src[:a].rstrip().rsplit('\n', 1)[-1]:
    a = src.rindex('\n', 0, a - 1) + 1  # keep a `/- BEGIN ... -/` marker with it
b = src.index('end Asm_SlabHead') + len('end Asm_SlabHead\n')
head = src[a:b]
src = src[:a] + src[b:]
c = src.index('/- BEGIN CASE1 -/')
src = src[:c] + head + '\n' + src[c:]

# 2. CutOneD: drop its copies, open SlabOneD
s = src.index('\nnamespace CutOneD\n') + len('\nnamespace CutOneD\n')
t = src.index('def cutCert : Cert where', s)
t = src.rindex('\n\n', s, t) + 2 if src.rfind('/--', s, t) == -1 else src.rindex('/--', s, t)
src = src[:s] + '\nopen SlabOneD\n\n' + src[t:]

# 3. cutCert: Bernstein interval instead of the witness fields
D = 10 ** 6
B = isqrt(19 * D * D // 20) + 1
while not B * B * 20 > 19 * D * D:
    B += 1
m = re.search(r'def cutCert : Cert where\n  Lam := [^\n]*\n  Q := [^\n]*\n', src)
end = src.index('\n\n', m.end())
src = src[:m.end()] + f'  A := 0\n  B := {B}\n  D := {D}' + src[end:]
src = src.replace('theorem cutCert_ok : cutCert.check 19 20 = true := by decide +kernel',
                  'theorem cutCert_ok : cutCert.check ⟨19, 20, 0, 0⟩ = true := by decide +kernel')
src = re.sub(r'Cert\.sound 19 20 cutCert cutCert_ok \(by push_cast; linarith\) h2',
             'Cert.sound ⟨19, 20, 0, 0⟩ cutCert cutCert_ok (by push_cast; linarith) (by norm_num) h2', src)

# 4. references and the bridge lemma
src = src.replace('CutOneD.peval_eq_sum', 'SlabOneD.peval_eq_sum').replace('CutOneD.peval', 'SlabOneD.peval')
m = re.search(r'/-- `SlabOneD.peval` and `CutOneD.peval` are the same Horner evaluation. -/\nlemma slab_peval_eq_cut[^\n]*\n(  [^\n]*\n)*', src)
if m:
    src = src[:m.start()] + src[m.end():].lstrip('\n')
src = src.replace('rw [polyR_eq_peval, slab_peval_eq_cut]', 'rw [polyR_eq_peval]')
open(sys.argv[2], 'w').write(src)
print('B =', B, ' bridge removed:', bool(m), ' leftover cut refs:', src.count('slab_peval_eq_cut'))
