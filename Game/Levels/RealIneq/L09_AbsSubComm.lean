import Game.Levels.RealIneq.L08_AbsNeg

World "RealIneq"
Level 9
Title "Distance is symmetric"

namespace MyReal

Introduction "
`abs (x - y)` is the distance between `x` and `y`. It does not matter which comes first.
"

/-- $|x - y| = |y - x|$ for reals. -/
Statement abs_sub_comm (x y : ℝ) : abs (x - y) = abs (y - x) := by
  Hint "Write `x - y` as `-(y - x)`: `rw [← neg_sub x y]`. Then `abs_neg`."
  Branch
    obtain ⟨s, hs, rfl⟩ := exists_ofSeq x
    Hint "No sequences needed: `rw [← neg_sub x y, abs_neg]`."
  rw [← neg_sub x y, abs_neg]

Conclusion "
The distance from `x` to `y` is the distance from `y` to `x`.
"

TheoremTab "abs"

end MyReal
