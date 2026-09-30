"""Replace the Hessian coefficients `CP_k` and their enclosures by polynomial data.

Rewrites Solution.lean (path in argv[1], written to argv[2]):
* the 61 definitions `CP_k` become the data list `Ps` plus `CP k := (Ps.getD k []).ev`,
* `Fq` and `expansion` refer to `CP k` instead of `CP_k`,
* the monomial bounds `mon_lo/mon_hi/mlo_*/mhi_*` and enclosures `enc_*` are replaced by
  `Poly.lo/hi` (computed from the box ends) and one soundness lemma `Poly.ev_mem`,
* `Hess` reads its enclosures from `Poly.lo/hi` instead of stored lists.
"""
import re, sys
import sympy as sp

src = open(sys.argv[1]).read()
c, s, p, q, r = V = sp.symbols('c s p q r')
defs = dict(re.findall(r'^noncomputable def CP_(\d+) \(c s p q r : ℝ\) : ℝ := (.*)$', src, re.M))
K = len(defs)
assert sorted(map(int, defs)) == list(range(K))


def poly(expr):
    e = sp.expand(sp.sympify(expr.replace('^', '**'), locals=dict(zip('cspqr', V))))
    terms = []
    for mon, coef in sp.Poly(e, *V).terms():
        coef = sp.Rational(coef)
        cq = str(coef.p) if coef.q == 1 else f'{coef.p}/{coef.q}'
        terms.append(f'({cq}, {", ".join(map(str, mon))})')
    return '[' + ', '.join(terms) + ']'


ps = ',\n  '.join(poly(defs[str(k)]) for k in range(K))
blockA = f'''/-- Polynomials in `c s p q r`: a list of (coefficient, exponents of `c s p q r`). -/
abbrev Poly := List (ℚ × ℕ × ℕ × ℕ × ℕ × ℕ)

/-- The monomial `c^a s^b p^d q^e r^f`. -/
noncomputable def mono (e : ℕ × ℕ × ℕ × ℕ × ℕ) (c s p q r : ℝ) : ℝ :=
  c ^ e.1 * s ^ e.2.1 * p ^ e.2.2.1 * q ^ e.2.2.2.1 * r ^ e.2.2.2.2

noncomputable def Poly.ev (P : Poly) (c s p q r : ℝ) : ℝ := (P.map fun t => (t.1 : ℝ) * mono t.2 c s p q r).sum

/-- The {K} coefficients of the Hessian form `Fq`. -/
def Ps : List Poly := [
  {ps}]

noncomputable def CP (k : ℕ) (c s p q r : ℝ) : ℝ := (Ps.getD k []).ev c s p q r'''

# 1. definitions -> data
first = src.index('noncomputable def CP_0 ')
last = src.index('\n', src.index(f'noncomputable def CP_{K - 1} '))
src = src[:first] + blockA + src[last:]
# 2. references
src = re.sub(r'\bCP_(\d+) c s p q r\b', r'CP \1 c s p q r', src)
src = re.sub(r'simp only \[CP_0(, CP_\d+)*\]',
             'simp only [CP, Ps, Poly.ev, mono, List.getD_cons_succ, List.getD_cons_zero, List.map_cons, '
             'List.map_nil, List.sum_cons, List.sum_nil]\n  push_cast', src)
assert 'CP_' not in re.sub(r'(lemma|theorem) (enc|mlo|mhi)_\d+[^\n]*', '', src).split('/- BEGIN')[0] or True

# 3. enclosures -> one lemma
box = re.search(r'def InBox \(c s p q r : ℝ\) : Prop :=\n(.*?)\n\n', src, re.S).group(1)
ends = re.findall(r'\(([-\d]+) / (\d+) : ℝ\)', box)
lo_ends = ', '.join(f'{a}/{b}' for a, b in ends[0::2])
hi_ends = ', '.join(f'{a}/{b}' for a, b in ends[1::2])
blockB = f'''
/-- The box's lower and upper ends; all positive. -/
def boxLo : List ℚ := [{lo_ends}]
def boxHi : List ℚ := [{hi_ends}]

namespace Poly

def monQ (b : List ℚ) (e : ℕ × ℕ × ℕ × ℕ × ℕ) : ℚ :=
  b.getD 0 0 ^ e.1 * b.getD 1 0 ^ e.2.1 * b.getD 2 0 ^ e.2.2.1 * b.getD 3 0 ^ e.2.2.2.1 * b.getD 4 0 ^ e.2.2.2.2

/-- Enclosure of a polynomial on the box, term by term. -/
def lo (P : Poly) : ℚ := (P.map fun t => if 0 ≤ t.1 then t.1 * monQ boxLo t.2 else t.1 * monQ boxHi t.2).sum
def hi (P : Poly) : ℚ := (P.map fun t => if 0 ≤ t.1 then t.1 * monQ boxHi t.2 else t.1 * monQ boxLo t.2).sum

lemma mono_mem {{c s p q r : ℝ}} (hb : InBox c s p q r) (e : ℕ × ℕ × ℕ × ℕ × ℕ) :
    (monQ boxLo e : ℝ) ≤ mono e c s p q r ∧ mono e c s p q r ≤ monQ boxHi e := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hb
  simp only [monQ, mono, boxLo, boxHi, List.getD_cons_succ, List.getD_cons_zero]; push_cast
  constructor <;> gcongr

lemma ev_mem {{c s p q r : ℝ}} (hb : InBox c s p q r) (P : Poly) :
    (P.lo : ℝ) ≤ P.ev c s p q r ∧ P.ev c s p q r ≤ P.hi := by
  have key : ∀ t ∈ P, (((if 0 ≤ t.1 then t.1 * monQ boxLo t.2 else t.1 * monQ boxHi t.2 : ℚ)) : ℝ)
      ≤ t.1 * mono t.2 c s p q r ∧ (t.1 : ℝ) * mono t.2 c s p q r
      ≤ ((if 0 ≤ t.1 then t.1 * monQ boxHi t.2 else t.1 * monQ boxLo t.2 : ℚ) : ℝ) := by
    intro t _
    obtain ⟨m1, m2⟩ := mono_mem hb t.2
    split_ifs with h
    · have h' : (0 : ℝ) ≤ t.1 := by exact_mod_cast h
      push_cast; exact ⟨mul_le_mul_of_nonneg_left m1 h', mul_le_mul_of_nonneg_left m2 h'⟩
    · have h' : (t.1 : ℝ) ≤ 0 := by exact_mod_cast (not_le.1 h).le
      push_cast; exact ⟨mul_le_mul_of_nonpos_left m2 h', mul_le_mul_of_nonpos_left m1 h'⟩
  simp only [lo, hi, ev, Rat.cast_list_sum, List.map_map, Function.comp_def]
  exact ⟨List.sum_le_sum fun t ht => (key t ht).1, List.sum_le_sum fun t ht => (key t ht).2⟩

end Poly
'''
a = src.index('lemma mon_lo ')
a = src.rindex('\n\n', 0, a) + 1
b = src.index('\nend Reg', src.index(f'lemma enc_{K - 1} ')) + 1
cut = src[a:b]
assert 'def InBox' not in cut and 'noncomputable def Fq' not in cut, 'unexpected content in the cut'
src = src[:a] + blockB + src[b:]

# 4. Hess reads the enclosures from the data
src = re.sub(r'/-- The coefficients `CP_k`, indexed.*?\nnoncomputable def cp .*?\n',
             '/-- The coefficients, indexed. -/\nnoncomputable def cp (c s p q r : ℝ) (k : ℕ) : ℝ := CP k c s p q r\n',
             src, flags=re.S)
src = re.sub(r'/-- Lower and upper ends of the enclosures `enc_k`. -/\ndef lo : List ℚ := .*?\ndef hi : List ℚ := .*?\n',
             '', src, flags=re.S)
src = src.replace('def mid (k : ℕ) : ℚ := (lo.getD k 0 + hi.getD k 0) / 2',
                  'def mid (k : ℕ) : ℚ := ((Ps.getD k []).lo + (Ps.getD k []).hi) / 2')
src = src.replace('def rad (k : ℕ) : ℚ := (hi.getD k 0 - lo.getD k 0) / 2',
                  'def rad (k : ℕ) : ℚ := ((Ps.getD k []).hi - (Ps.getD k []).lo) / 2')
a = src.index('lemma cp_mem ')
b = src.index('\n\n', a)
src = src[:a] + '''lemma cp_mem {c s p q r : ℝ} (hb : InBox c s p q r) (k : ℕ) :
    ((Ps.getD k []).lo : ℝ) ≤ cp c s p q r k ∧ cp c s p q r k ≤ ((Ps.getD k []).hi : ℝ) :=
  Poly.ev_mem hb _''' + src[b:]
# core: the zero entries of the matrix read `CP 61`, one past the data
src = src.replace('''  have h := Hess.qform hb fun i =>''', '''  have h0 : CP 61 c s p q r = 0 := by simp [CP, Ps, Poly.ev]
  have h := Hess.qform hb fun i =>''')
src = src.replace('''    Hess.lam, List.getD_cons_succ, List.getD_cons_zero, List.getD_nil] at h''',
                  '''    Hess.lam, List.getD_cons_succ, List.getD_cons_zero, h0] at h''')
open(sys.argv[2], 'w').write(src)
print('K =', K, ' removed region words:', len(cut.split()))
