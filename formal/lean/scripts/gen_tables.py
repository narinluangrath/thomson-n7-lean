"""Replace the bipyramid value tables (g, W, muP, pent_critical, gP, pc, pb) by matrices + one lemma each.

Usage: python3 scripts/gen_tables.py <in.lean> <out.lean>
"""
import re, sys

sys.path.insert(0, 'scripts')
import golf

cs = golf.chunks(open(sys.argv[1]).read())
name = lambda c: (re.search(r'^(?:private |protected |noncomputable )*(?:theorem|lemma|def)\s+(\S+)', c, re.M) or [0, None])[1]
PENT = 'pent_0, pent_1, pent_2, pent_3, pent_4, pent_5\', pent_6\''
UP = ', '.join(f'g_{i}_{j}' for i in range(7) for j in range(i + 1, 7))

GRAM = f'''/-- The Gram matrix `⟪Pᵢ, Pⱼ⟫` of the bipyramid. -/
noncomputable def gt : Fin 7 → Fin 7 → ℝ :=
  ![![1, c1, c2, c2, c1, 0, 0], ![c1, 1, c1, c2, c2, 0, 0], ![c2, c1, 1, c1, c2, 0, 0], ![c2, c2, c1, 1, c1, 0, 0],
    ![c1, c2, c2, c1, 1, 0, 0], ![0, 0, 0, 0, 0, 1, -1], ![0, 0, 0, 0, 0, -1, 1]]

lemma gram (i j : Fin 7) : inner ℝ (pentBipyramid i) (pentBipyramid j) = gt i j := by
  fin_cases i <;> fin_cases j <;> simp [gt, pent_norm] <;>
    (first | simp only [{UP}] | (rw [real_inner_comm]; simp only [{UP}]))

lemma Wt (i j : Fin 7) : W i j = if i = j then 0 else phi (gt i j) ^ 3 := by unfold W; rw [gram]'''

MUP = '''/-- The multiplier `μ` at an equatorial vertex. -/
noncomputable def μ : ℝ := 2 * c1 * phi c1 ^ 3 + 2 * c2 * phi c2 ^ 3

lemma muPv (i : Fin 7) :
    muP i = ![μ, μ, μ, μ, μ, -(phi (-1) ^ 3), -(phi (-1) ^ 3)] i := by
  fin_cases i <;> simp [muP, μ, Fin.sum_univ_seven, Wt, gram, gt] <;> ring'''

CRIT = f'''/-- The bipyramid is a critical point: `∑ⱼ Wᵢⱼ Pⱼ = μᵢ Pᵢ`. -/
theorem pent_critical (i : Fin 7) :
    ∑ j, W i j • pentBipyramid j = muP i • pentBipyramid i := by
  rw [muPv]; unfold μ
  ext m
  fin_cases i <;> fin_cases m <;> simp [Fin.sum_univ_seven, Wt, gt, {PENT}] <;>
    first | ring1 | (linear_combination crit_1_x (phi c1 ^ 3) (phi c2 ^ 3)) | (linear_combination crit_1_y (phi c1 ^ 3) (phi c2 ^ 3)) | (linear_combination crit_2_x (phi c1 ^ 3) (phi c2 ^ 3)) | (linear_combination crit_2_y (phi c1 ^ 3) (phi c2 ^ 3)) | (linear_combination crit_3_x (phi c1 ^ 3) (phi c2 ^ 3)) | (linear_combination crit_3_y (phi c1 ^ 3) (phi c2 ^ 3)) | (linear_combination crit_4_x (phi c1 ^ 3) (phi c2 ^ 3)) | (linear_combination crit_4_y (phi c1 ^ 3) (phi c2 ^ 3)) | (linear_combination crit_5_x (phi 0 ^ 3))'''

PC = f'''/-- Coordinates of the bipyramid. -/
noncomputable def pt : Fin 7 → Fin 3 → ℝ :=
  ![![1, 0, 0], ![c1, s1, 0], ![c2, s2, 0], ![c2, -s2, 0], ![c1, -s1, 0], ![0, 0, 1], ![0, 0, -1]]

lemma pcv (i : Fin 7) (m : Fin 3) : pentBipyramid i m = pt i m := by
  fin_cases i <;> fin_cases m <;> simp [pt, {PENT}]'''

PB = '''lemma pb {i j : Fin 7} (h : i ≠ j) : phi (gP i j) ≤ 8507 / 10000 := by
  fin_cases i <;> fin_cases j <;> simp [gP, gram, gt] at h ⊢ <;>
    first | exact phi_c1_le | exact phi_c2_le | exact phi_zero_le | exact phi_neg_one_le'''

out = []
placed = set()
for c in cs:
    n = name(c) or ''
    m = re.fullmatch(r'g_(\d)_(\d)', n)
    if m and int(m.group(1)) > int(m.group(2)):
        continue
    if re.fullmatch(r'W_\d_\d', n):
        if 'W' not in placed:
            out.append(GRAM); placed.add('W')
        continue
    if re.fullmatch(r'muP_\d', n):
        if 'muP' not in placed:
            out.append(MUP); placed.add('muP')
        continue
    if re.fullmatch(r'pent_critical(_\d)?', n):
        if n == 'pent_critical':
            out.append(CRIT)
        continue
    if re.fullmatch(r'gP_\d_\d', n):
        continue
    if re.fullmatch(r'pc_\d_\d', n):
        if 'pc' not in placed:
            out.append(PC); placed.add('pc')
        continue
    if re.fullmatch(r'pb_\d_\d', n):
        if 'pb' not in placed:
            out.append(PB); placed.add('pb')
        continue
    out.append(c)
src = '\n'.join(out)

# hessian_lower: the long lists of table lemmas become the generic ones
def fix_list(mo):
    items = [x.strip() for x in mo.group(1).split(',')]
    kept = [x for x in items if not re.fullmatch(r'(gP_\d_\d|W_\d_\d|muP_\d|pc_\d_\d|g_\d_\d)', x)]
    return 'simp only [gP, gram]\n  simp only [' + ', '.join(kept + ['Wt', 'muPv', 'pcv']) + ']\n  simp only [gt, pt, μ, Fin.isValue, Matrix.cons_val\', Matrix.cons_val, Matrix.cons_val_fin_one, Matrix.cons_val_one,\n    Matrix.cons_val_zero, Fin.reduceEq, ↓reduceIte]'
a = src.index('lemma hessian_lower ')
b = src.index('\n\n', a)
body = re.sub(r'simp only \[(Fin\.sum_univ_seven, gP_0_1[^\]]*)\]', fix_list, src[a:b], flags=re.S)
src = src[:a] + body + src[b:]
# sum_Dpair_lower
src = re.sub(r'\(by decide\) pb_\d_\d', '(by decide) (pb (by decide))', src)
left = sorted(set(re.findall(r'\b(?:g_[1-6]_[0-5]|W_\d_\d|muP_\d|pent_critical_\d|gP_\d_\d|pc_\d_\d|pb_\d_\d)\b', src)))
left = [x for x in left if not (x.startswith('g_') and int(x[2]) < int(x[4]))]
print('leftover references:', left)
open(sys.argv[2], 'w').write(src)
