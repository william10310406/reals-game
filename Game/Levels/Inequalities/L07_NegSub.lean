import Game.Levels.Inequalities.L06_EqZero

World "Inequalities"
Level 7
Title "Minus a difference"

namespace MyRat

Introduction "
`-(y - x) = x - y`.
"

/-- $-(y - x) = x - y$. -/
Statement neg_sub (x y : ℚ) : -(y - x) = x - y := by
  Hint "`sub_eq_add_neg` twice, `neg_add`, `neg_neg`, `add_comm`."
  Branch
    rw [sub_eq_add_neg]
    Hint "Only the first difference became a sum. Do the same for `x - y`, then `neg_add`."
  rw [sub_eq_add_neg, sub_eq_add_neg, neg_add, neg_neg, add_comm]

Conclusion "
`neg_sub` is in your inventory.
"

TheoremTab "ℚ"

end MyRat
