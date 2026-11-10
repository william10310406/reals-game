import Game.Levels.RealOrder.L04_LeTrans

World "RealOrder"
Level 5
Title "Adding to both sides"

namespace MyReal

Introduction "
`≤` and `+` fit together: if `a ≤ b`, then `a + c ≤ b + c`.
"

/-- If $a \le b$, then $a + c \le b + c$. -/
Statement add_le_add_right (a b c : ℝ) : a ≤ b → a + c ≤ b + c := by
  intro h
  rw [le_iff_nonneg] at h ⊢
  Hint "Show `b + c - (a + c) = b - a` with `have`. Inside: `sub_eq_add_neg` twice, `neg_add`,
  then regroup with a second `have … := by ac_rfl` so that `c + -c` appears."
  have e : b + c - (a + c) = b - a := by
    rw [sub_eq_add_neg, sub_eq_add_neg, neg_add]
    have e2 : b + c + (-a + -c) = b + -a + (c + -c) := by ac_rfl
    rw [e2, add_neg, add_zero]
  Hint "Now `rw [{e}]`."
  rw [e]
  exact h

Conclusion "
`≤` is compatible with `+`.
"

TheoremTab "≤ℝ"

end MyReal
