import Game.Levels.RealIneq.L01_NegLeNeg

World "RealIneq"
Level 2
Title "Adding inequalities"

namespace MyReal

Introduction "
If `a ≤ b` and `c ≤ d`, then `a + c ≤ b + d`.
"

/-- If $a \le b$ and $c \le d$, then $a + c \le b + d$ for reals. -/
Statement add_le_add (a b c d : ℝ) : a ≤ b → c ≤ d → a + c ≤ b + d := by
  intro h1 h2
  rw [le_iff_nonneg] at h1 h2 ⊢
  Hint "Show `b + d - (a + c) = b - a + (d - c)` first, with `have`.
  Inside: `sub_eq_add_neg` three times, `neg_add`, then `ac_rfl`."
  have h : b + d - (a + c) = b - a + (d - c) := by
    rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg, neg_add]
    ac_rfl
  rw [h]
  exact nonneg_add (b - a) (d - c) h1 h2

Conclusion "
`add_le_add` is in your inventory.
"

TheoremTab "≤ℝ"

end MyReal
