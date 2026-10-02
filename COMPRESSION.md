# Compressing the Thomson N = 7 Lean proof

This branch (`compress`) shrinks `formal/lean/ThomsonN7/Solution.lean` while keeping the same two theorems,
`ThomsonN7.thomson_seven` and `ThomsonN7.thomson_seven_unique`, fully verified. The work ran from 2026-09-29 to
2026-10-02 and was done by Claude (Opus 5.5) with a team of subagents, directed by Narin Luangrath.

## Result

| | Original (`25f2fa5`) | Now | Change |
|---|---:|---:|---:|
| Words, total | 389,377 | 56,106 | -85.6% |
| Words, data | 227,658 | 17,178 | -92.5% |
| Words, proof | 154,705 | 38,147 | -75.3% |
| Lines | 17,895 | 5,705 | -68.1% |
| Bytes | 8,079,343 | 5,094,277 | -36.9% |
| Full build | about 12 min | 9 min 38 s | |
| Peak memory of the build | about 19.3 GB | 15.3 GB | |

**Metric.** Words are whitespace-separated tokens, counted by `formal/lean/scripts/wordcount.py`. A line counts as data
when at least half its tokens are numerals, however they are written. Proof words are everything else except line
comments; doc comments count. Words were the target, not characters or bytes. That is why the byte count fell much
less: the remaining certificate data are long integers.

**Rules followed.** No joining of lines or squeezing of whitespace. No packing numbers into hex or big integers to cut
the word count. (The original's typed certificates were already packed by its authors; that encoding is unchanged.)
Every reported number comes from a build that passed the strict check below.

## How it was verified

Every commit on the branch passes `formal/lean/scripts/check-edited.sh`. That is the repository's `check.sh` with two
steps removed and one made strict:

- **Removed:** the package hash and the line-number claims. Both describe the original file, so they fail by design on
  an edited proof.
- **Made strict:** the preamble check. Lines 1 to 310 of `Solution.lean` must be byte-identical to the fixed statement
  `ComparatorChallenges/ThomsonN7.lean`. In the original `check.sh` this step is written `diff … && echo identical`
  under `set -e`, so it can never fail. Early on, edits to the preamble went unnoticed for 8 commits because of this;
  they were restored byte-for-byte (`5670d8f`) and the check was fixed in `check-edited.sh`.

What `check-edited.sh` does:

1. A full `lake build` with no errors.
2. The preamble identity above.
3. A scan for `sorry`, `native_decide`, `set_option`, macros, `#eval` and new axioms.
4. `#print axioms` for both theorems, which must show only `propext`, `Classical.choice` and `Quot.sound`.
5. The statement comparison: every constant of the challenge file must have the same type (and value, for
   definitions) in the solution.

`scripts/negative-control.sh` confirms that step 5 has teeth. It flips the inequality in a copy of the challenge, and
the comparison then fails on exactly that theorem. It passes on the final commit.

**Not re-run on the compressed proof:** the Lean Comparator and the second kernel (nanoda) described in the original
README and in `verification/`. Those results apply to the original file only. The README's line numbers and
`PACKAGE_SHA256SUMS.txt` also still describe the original file.

## What was done, in order

| Phase | Commits | Total words after | What changed |
|---|---|---:|---|
| Dead code | `6d9cbd6`, `050abc6` | 351,548 | Removed 327 declarations the two theorems never use, found by walking proof-term dependencies (`scripts/Unused.lean`). `@[simp]` lemmas proved by `rfl` never appear in proof terms, so they are extra roots. |
| Certificates as data | `577d953` to `b590c27` | 321,684 | Unrolled certificate proofs (the Hessian, polynomial coefficients, value tables) replaced by data plus one kernel-checked lemma each (`gen_hess.py`, `gen_poly.py`, `gen_fq.py`, `gen_tables.py`). |
| Tactic golf | `0e56cb1`, `6b7907b` | 320,380 | Greedy per-line deletion (`golf_lines.py`) and one-tactic substitutions (`golf_hints.py`). |
| Agent golf, rounds 1 to 7 | `43ea58b` to `569497c` | 94,313 | Subagents rewrote the largest proofs, about 30 per round, each replacement checked in place by a REPL server (`verify_server.py`, `verify.py`). Savings fell from 8.1k words in round 1 to 1.0k in round 7. |
| Data encoding | `e65bf96` | 171,000 | Certificate integers written as plain numerals instead of `Int.ofNat`/`Int.negSucc` wrappers (-134k words). |
| Witness-free 1D checks | `18c345f`, `7d2c659` | 114,441 | The one-dimensional slab certificates (sums of squares with stored witnesses) replaced by a Bernstein-basis positivity check that needs no witness (`gen_bern.py`, `gen_cut.py`). |
| Shared bases | `c1ff8e2`, `538c4cf` | 95,333 | Three monomial bases shared instead of repeated per block; triangular columns stored without their zero prefix (`zpad`). |
| Case 1 certificate regenerated | `97244d2`, `03ed182` | 86,685 | Re-solved the Case 1 three-point SDP. The blocks for the multipliers 1-u, 1-v, 1-t turned out to be dead weight, so each 35x35 block became 1x1 (`case1_gen.py`, `case1_model.py`, `case1_stats.py`). |
| Section rewrites | `574553f` onward | 56,106 | One subagent per section rewrote it from scratch against a REPL positioned just before it, keeping every declaration used later with an identical statement. See below. |

### Section rewrites

| Section | Before | After | Cut |
|---|---:|---:|---:|
| RegLocalSection (local minimality) | 7,344 | 3,092 | -58% |
| ThreePoint | 3,842 | 2,307 | -40% |
| Cert3Block (Case 1 checker) | 3,894 | 2,106 | -46% |
| Asm_T4 | 4,335 | 1,160 | -73% |
| Kron (expressions, Kronecker check) | 2,863 | 1,472 | -49% |
| GV | 2,416 | 1,001 | -59% |
| Asm_CertT (typed checker) | 7,784 | 3,770 | -52% |
| Reg (criticality, gauge) | 2,788 | 1,191 | -57% |
| Asm_Typed7 | 2,416 | 1,308 | -46% |
| Asm_Coerce | 2,568 | 1,422 | -45% |
| Asm_SlabHead (1D Bernstein checker) | 1,963 | 1,155 | -41% |
| Asm_Coerce2 | 1,819 | 1,049 | -42% |
| Asm_CertF (packed blocks) | 1,737 | 1,047 | -40% |
| Base | 931 | 496 | -47% |
| Case1 (then chunk machinery dropped) | 1,655 | 143 | -91% |
| M3 | 1,062 | 520 | -51% |
| TwoRegime | 1,343 | 807 | -40% |
| Asm_Glue2 | 1,164 | 638 | -45% |
| Cert1Block | 900 | 730 | -19% |
| Asm_Glue4 | 880 | 467 | -47% |
| Asm_Typed2 | 796 | 516 | -35% |
| Asm_Glue1 | 1,589 | 715 | -55% |

The rewrites removed intermediate lemma layers and replaced hand proofs with Mathlib facts (for example
`Matrix.posSemidef_gram` for Gram positivity, and Mathlib reflections for the gauge rotation). They also replaced
stored data with computation: the local-minimality Hessian is built from a formula and factorised in the kernel instead
of being stored. All rewrites removed doc comments, which the word count includes, so part of each cut is comments.
Where measured, the cut against comment-stripped originals is smaller (Cert3Block -37%, RegLocalSection -53%).

Three sections contain definitions that kernel checks evaluate downstream: Cert3Block, Kron and Asm_CertT feed the Case 1
chunk statistics and the six typed certificates. In those, every computable definition was kept `#print`-identical and
only proofs changed.

## What did not work

- **Kernel-computed Case 1 factorisation** (`gen_case1.py`): correct, but the build peaked at about 23 GB, so it was
  reverted. The script is kept for reference.
- **Merging the two certificate checkers** (Case 1 and the typed checker): the typed checker reads packed integers
  directly, so Case 1 could only join it by packing its data, which would game the metric. Only a 309-word cleanup
  came out of it (`03ed182`).
- **Shrinking the Case 1 SDP further:** with the multiplier blocks gone, every other block, and the degree-10 minorant,
  is tight. Making any of them smaller drops the bound below E(P).

## Caveats

- **Close to the time limit.** Two declarations are near Lean's default heartbeat limit: `hessian_lower` in
  RegLocalSection, and `typed7_bound_lo`, which uses about 45%. A toolchain or Mathlib bump could push them over.
- **Comments.** Removing doc comments made the file harder to read alongside `paper/PAPER.md`, which still describes
  the original file and its line numbers.
- **Dependencies between sections changed.** The rewritten GV section depends on lemmas in Reg and Base
  (`Reg.pent_0`, `pent_1`, `pent_5'`, `inner_vec3`, `s1`, `s1_sq`, `g_0_1`, `g_0_5`, `g_1_5`, `Base.c1`, `pent_norm`).

## Where the words are now

About 17.4k words are certificate data, 14k of them the Case 1 SDP certificate, which is at its minimum size for this
formulation. The largest proof regions not yet rewritten are Cert1Block (0.9k words), Asm_Glue4 (0.9k), Asm_Typed2
(0.8k) and Asm_Bridge (0.7k). Rewrites have cut 40 to 73%
per section; the later ones land near 40% because more of what remains is definitions and statements that must stay
identical.

## Reproducing

From `formal/lean`:

```
bash scripts/check-edited.sh          # full build plus the checks above, about 11 minutes, about 16 GB
bash scripts/negative-control.sh      # after check-edited.sh
python3 scripts/wordcount.py ThomsonN7/Solution.lean
```

Toolchain: Lean 4.34.1 and the Mathlib revision pinned in `lake-manifest.json`, as in the original package. The REPL
tooling (`repl_server.py`, `verify_server.py`) needs the Lean REPL (leanprover-community/repl) built for the same
toolchain; set `LEAN_REPL` to its binary (default `~/src/repl/.lake/build/bin/repl`).
