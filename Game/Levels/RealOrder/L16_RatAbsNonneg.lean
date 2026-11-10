import Game.MyReal.Abs

World "RealOrder"
Level 16
Title "Absolute value in ℚ"

namespace MyRat

Introduction "
The absolute value: `abs a` is `a` if `a ≥ 0`, and `-a` otherwise.

* `abs_of_nonneg : nonneg a → abs a = a`
* `abs_of_not_nonneg : ¬ nonneg a → abs a = -a`

To use them, split with `by_cases h : nonneg a`.
"

/-- $|a| \ge 0$ for rationals. -/
Statement abs_nonneg (a : ℚ) : nonneg (abs a) := by
  Hint "`by_cases h : nonneg a`."
  Branch
    rw [abs_of_nonneg]
    Hint "`abs_of_nonneg` needs a proof of `nonneg a`. You do not have one yet.
    Split first: `by_cases h : nonneg a`."
  by_cases h : nonneg a
  · rw [abs_of_nonneg h]
    exact h
  · rw [abs_of_not_nonneg h]
    Hint "Use the signs: `obtain h2 | h2 := nonneg_or_nonneg_neg a`."
    obtain h2 | h2 := nonneg_or_nonneg_neg a
    · exfalso
      exact h h2
    · exact h2

Conclusion "
`|a| ≥ 0`.
"

NewTheorem MyRat.abs_of_nonneg MyRat.abs_of_not_nonneg
NewDefinition MyRat.abs
TheoremTab "abs"

end MyRat
