import Game.Levels.RealOrder

World "RealIneq"
Level 1
Title "Turning an inequality around"

namespace MyReal

Introduction "
In this world you bring the rules for inequalities from `ℚ` over to `ℝ`.
Many proofs are the same as for `ℚ`: they only used laws that `ℝ` now has too.
"

/-- If $a \le b$, then $-b \le -a$ for reals. -/
Statement neg_le_neg (a b : ℝ) : a ≤ b → -b ≤ -a := by
  intro h
  rw [le_iff_nonneg] at h ⊢
  Hint "As for `ℚ`: `rw [sub_eq_add_neg, neg_neg, add_comm, ← sub_eq_add_neg]`."
  Branch
    obtain ⟨s, hs, rfl⟩ := exists_ofSeq a
    Hint "No sequences needed. Make the goal look like `{h}` with
    `rw [sub_eq_add_neg, neg_neg, add_comm, ← sub_eq_add_neg]`."
  rw [sub_eq_add_neg, neg_neg, add_comm, ← sub_eq_add_neg]
  exact h

Conclusion "
The same proof as for `ℚ`, word for word.
"

TheoremTab "≤ℝ"

end MyReal
