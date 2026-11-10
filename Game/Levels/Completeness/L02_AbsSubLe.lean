import Game.Levels.Completeness.L01_Choose

World "Completeness"
Level 2
Title "Triangle inequality for distances"

namespace MyReal

Introduction "
The distance from `x` to `z` is at most the distance from `x` to `y` plus from `y` to `z`.
"

/-- $|x - z| \le |x - y| + |y - z|$ for reals. -/
Statement abs_sub_le (x y z : ℝ) : abs (x - z) ≤ abs (x - y) + abs (y - z) := by
  Hint "Split `x - z` at `y`: `rw [← sub_add_sub z y x]`. Then `abs_add`."
  rw [← sub_add_sub z y x]
  exact abs_add _ _

Conclusion "
`abs_sub_le` is in your inventory.
"

TheoremTab "abs"

end MyReal
