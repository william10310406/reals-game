import Game.Levels.RealOrder.L12_RatNonnegOr

World "RealOrder"
Level 13
Title "Comparing rationals"

namespace MyRat

Introduction "
`a ≤ b` or `b ≤ a`: apply the last level to `b - a`.
"

/-- For rationals, $a \le b$ or $b \le a$. -/
Statement le_total (a b : ℚ) : a ≤ b ∨ b ≤ a := by
  Hint "`rw [le_iff_nonneg, le_iff_nonneg]`. Then write `a - b` as `-(b - a)`: `rw [← neg_sub a b]`."
  rw [le_iff_nonneg, le_iff_nonneg]
  Branch
    left
    Hint "You cannot know which side is true. Use `nonneg_or_nonneg_neg (b - a)` instead."
  rw [← neg_sub a b]
  exact nonneg_or_nonneg_neg (b - a)

Conclusion "
`≤` on `ℚ` is a total order.
"

TheoremTab "ℚ"

end MyRat
