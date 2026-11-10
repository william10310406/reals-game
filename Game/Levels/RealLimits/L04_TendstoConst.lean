import Game.Levels.RealLimits.L03_EpsLe

World "RealLimits"
Level 4
Title "Constant sequences"

namespace MyReal

Introduction "
`Tendsto a L`: for every `k` there is `N` with `abs (a n - L) ≤ eps k` for all `n ≥ N`.

This is the textbook definition of a limit, with `ε = 1/(k+1)`.

`const c` is the sequence `c, c, c, …` (`const_apply c n : const c n = c`).
"

/-- The constant sequence $c, c, c, \dots$ tends to $c$. -/
Statement tendsto_const (c : ℝ) : Tendsto (const c) c := by
  intro k
  use 0
  intro n hn
  Hint "`rw [const_apply, sub_eq_add_neg, add_neg]`. Then the goal is `abs 0 ≤ eps k`."
  rw [const_apply, sub_eq_add_neg, add_neg]
  Hint "`apply abs_le`."
  Branch
    rw [abs_of_nonneg]
    Hint "That needs `nonneg 0`, which takes a detour. Easier: `apply abs_le`."
  apply abs_le
  · exact eps_nonneg k
  · rw [neg_zero]
    exact eps_nonneg k

Conclusion "
Constant sequences converge.
"

NewTheorem MyReal.const_apply
NewDefinition MyReal.Tendsto MyReal.const
TheoremTab "limℝ"

end MyReal
