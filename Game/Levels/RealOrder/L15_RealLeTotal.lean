import Game.Levels.RealOrder.L14_RealNonnegOr

World "RealOrder"
Level 15
Title "Comparing reals"

namespace MyReal

Introduction "
Now: any two reals can be compared.
"

/-- For reals, $x \le y$ or $y \le x$. -/
Statement le_total (x y : ℝ) : x ≤ y ∨ y ≤ x := by
  Hint "As for `ℚ`: `rw [le_iff_nonneg, le_iff_nonneg, ← neg_sub x y]`."
  rw [le_iff_nonneg, le_iff_nonneg, ← neg_sub x y]
  exact nonneg_or_nonneg_neg (y - x)

Conclusion "
`≤` on `ℝ` is a total order.
"

TheoremTab "≤ℝ"

end MyReal
