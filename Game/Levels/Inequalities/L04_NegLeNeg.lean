import Game.Levels.Inequalities.L03_NegNeg

World "Inequalities"
Level 4
Title "Flipping signs"

namespace MyRat

Introduction "
Multiplying by `-1` turns an inequality around.
"

/-- If $a \le b$, then $-b \le -a$. -/
Statement neg_le_neg (a b : ℚ) : a ≤ b → -b ≤ -a := by
  intro h
  rw [le_iff_nonneg] at h ⊢
  Hint "Make the goal look like `{h}`: `sub_eq_add_neg`, `neg_neg`, `add_comm`, then `← sub_eq_add_neg`."
  rw [sub_eq_add_neg, neg_neg, add_comm, ← sub_eq_add_neg]
  exact h

Conclusion "
`-b ≤ -a` says the same as `a ≤ b`.
"

TheoremTab "ℚ"

end MyRat
