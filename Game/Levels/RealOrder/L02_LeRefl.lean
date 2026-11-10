import Game.Levels.RealOrder.L01_NegEpsLe

World "RealOrder"
Level 2
Title "x ≤ x"

namespace MyReal

open MyNat (succ)

Introduction "
* `le_iff_nonneg x y : x ≤ y ↔ nonneg (y - x)`
* `nonneg_ofSeq : nonneg (ofSeq s hs) ↔ ∀ k, ∃ N, ∀ n, N ≤ n → -frac 1 (succ k) ≤ s n`

Why this definition? A real is a limit, so its terms may stay a little below `0` for ever
(think of `-1, -1/2, -1/3, …`, which is the real `0`).
We only ask that they are not *much* below `0` in the end.
"

/-- $x \le x$ for reals. -/
Statement le_refl (x : ℝ) : x ≤ x := by
  Hint "Unfold `≤`, then simplify `x - x` to `0`:
  `rw [le_iff_nonneg, sub_eq_add_neg, add_neg]`."
  rw [le_iff_nonneg, sub_eq_add_neg, add_neg]
  Hint "Write `0` as a sequence and unfold `nonneg`: `rw [zero_def, ofRat_def, nonneg_ofSeq]`."
  Branch
    obtain ⟨s, hs, rfl⟩ := exists_ofSeq x
    Hint "No need for the sequence of `x`: the goal is about `0`. Write `0` as a sequence:
    `rw [zero_def, ofRat_def, nonneg_ofSeq]`."
  rw [zero_def, ofRat_def, nonneg_ofSeq]
  intro k
  use 0
  intro n hn
  Hint "`rw [MyRat.const_apply]`, then the last level."
  rw [MyRat.const_apply]
  exact MyRat.neg_eps_le k

Conclusion "
`≤` on `ℝ` is reflexive.
"

NewTheorem MyReal.le_iff_nonneg MyReal.nonneg_ofSeq
NewDefinition MyReal.nonneg
TheoremTab "≤ℝ"

end MyReal
