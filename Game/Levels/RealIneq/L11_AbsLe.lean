import Game.Levels.RealIneq.L10_AbsBounds

World "RealIneq"
Level 11
Title "Bounding |x|"

namespace MyReal

Introduction "
To show `abs x ≤ y`, show `x ≤ y` and `-x ≤ y`. For reals there is no `abs_of_not_nonneg`,
but you have the signs (`nonneg_or_nonneg_neg`) and `abs_neg`.
"

/-- If $x \le y$ and $-x \le y$, then $|x| \le y$ for reals. -/
Statement abs_le (x y : ℝ) : x ≤ y → -x ≤ y → abs x ≤ y := by
  intro h1 h2
  Hint "Split by the sign of `x`: `obtain h | h := nonneg_or_nonneg_neg x`."
  Branch
    by_cases h : nonneg x
    Hint "That works for the first case. In the second you need `nonneg (-x)`:
    `nonneg_or_nonneg_neg x` gives it directly."
  obtain h | h := nonneg_or_nonneg_neg x
  · rw [abs_of_nonneg x h]
    exact h1
  · Hint "`rw [← abs_neg x, abs_of_nonneg (-x) {h}]`."
    rw [← abs_neg x, abs_of_nonneg (-x) h]
    exact h2

Conclusion "
`apply abs_le` turns a goal `abs x ≤ y` into two goals without `abs`.
"

TheoremTab "abs"

end MyReal
