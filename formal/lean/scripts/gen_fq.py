"""Drop `Fq`, `expansion` and `core`; prove `hessian_lower` straight from `Hess.qform`.

Usage: python3 scripts/gen_fq.py <in.lean> <out.lean>
"""
import re, sys

src = open(sys.argv[1]).read()


def cut_decl(src, head):
    """Remove the declaration starting with `head` (and its doc comment) up to the next unindented line."""
    a = src.index(head)
    if src[:a].rstrip().endswith('-/'):
        doc = src.rindex('/--', 0, a)
        if src[doc:a].count('-/') == 1:
            a = doc
    m = re.compile(r'\n(?=\S)').search(src, src.index('\n', a))
    b = m.start() + 1
    rest = src[b:].lstrip('\n')
    return src[:a] + rest, src[a:b]


src, _ = cut_decl(src, 'noncomputable def Fq ')
src, expansion = cut_decl(src, 'lemma expansion ')
src, _ = cut_decl(src, 'lemma core ')

# the rewriting steps of `expansion` (everything between `unfold ...` and `generalize`)
steps = expansion[expansion.index('  simp only [sum_Ioi_seven]'):expansion.index('  push_cast')]
steps = steps.replace('\n  simp only [CP, Ps', '\n  simp only [CP, Ps')  # keep as is
xs = ', '.join(f'h {i} {j}' for i in range(7) for j in range(3))
new = f'''lemma hessian_lower (h : Fin 7 → R3) :
    449 / 100000 * ∑ i, ‖h i‖ ^ 2 ≤ Qhess h + 2 * Pen h := by
  have hc2 : c2 = -1 / 2 - c1 := by unfold c1 c2; ring
  have h0 : CP 61 c1 s1 (phi c1) (phi c2) (phi 0) = 0 := by simp [CP, Ps, Poly.ev]
  have hq := Hess.qform atoms_inBox fun i => [{xs}].getD i 0
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Hess.Hm, Hess.ix, Hess.idx, Hess.wt, Hess.cp,
    Hess.lam, List.getD_cons_succ, List.getD_cons_zero, h0] at hq
  norm_num at hq
  unfold Qhess Pen gaugeG
{steps.rstrip()} at hq ⊢
  push_cast at hq ⊢
  simp only [phi_neg_one, s2_eq, hc2] at hq ⊢
  linear_combination hq
'''
a = src.index('lemma hessian_lower ')
if src[:a].rstrip().endswith('-/'):
    a = src.rindex('/--', 0, a)
b = src.index('\n\n', a)
doc = '/-- The penalised Hessian bound `449/100000 ∑ ‖hᵢ‖² ≤ Qhess h + 2 Pen h`, from the certificate. -/\n'
src = src[:a] + doc + new.rstrip('\n') + src[b:]
open(sys.argv[2], 'w').write(src)
