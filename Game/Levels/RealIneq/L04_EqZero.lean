import Game.Levels.RealIneq.L03_NegZero

World "RealIneq"
Level 4
Title "Neither positive nor negative"

namespace MyReal

Introduction "
If `x ≥ 0` and `-x ≥ 0`, then `x = 0`. Use antisymmetry with `0`.
"

/-- If $x \ge 0$ and $-x \ge 0$, then $x = 0$ for reals. -/
Statement eq_zero_of_nonneg_neg (x : ℝ) : nonneg x → nonneg (-x) → x = 0 := by
  intro h1 h2
  Hint "`apply le_antisymm`."
  apply le_antisymm
  · Hint "`x ≤ 0` means `nonneg (0 - x)`. Simplify with `rw [le_iff_nonneg, sub_eq_add_neg, zero_add]`."
    rw [le_iff_nonneg, sub_eq_add_neg, zero_add]
    exact h2
  · Hint "`0 ≤ x` means `nonneg (x - 0)`. `rw [le_iff_nonneg, sub_eq_add_neg, neg_zero, add_zero]`."
    rw [le_iff_nonneg, sub_eq_add_neg, neg_zero, add_zero]
    exact h1

Conclusion "
As for `ℚ`, but with `le_antisymm` instead of fractions.
"

TheoremTab "≤ℝ"

end MyReal
