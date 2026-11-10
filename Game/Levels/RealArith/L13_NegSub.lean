import Game.Levels.RealArith.L12_SubAddSub

World "RealArith"
Level 13
Title "Turning a difference around"

namespace MyReal

Introduction "
`-(y - x) = x - y`. Only laws of `ℝ`, no sequences.
"

/-- $-(y - x) = x - y$ for reals. -/
Statement neg_sub (x y : ℝ) : -(y - x) = x - y := by
  Hint "`sub_eq_add_neg` twice, `neg_add`, `neg_neg`, `add_comm`."
  Branch
    rw [sub_eq_add_neg]
    Hint "Only the first difference became a sum. Do the same for `x - y`, then `neg_add`."
  rw [sub_eq_add_neg, sub_eq_add_neg, neg_add, neg_neg, add_comm]

Conclusion "
`neg_sub` is in your inventory.
"

TheoremTab "ℝ"

end MyReal
