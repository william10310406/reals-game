import Game.Levels.Reals

World "Inequalities"
Level 1
Title "Adding to both sides"

namespace MyRat

Introduction "
In this world you prove rules for `≤` on `ℚ`.
These are the rules you use every day when you compute with inequalities.
"

/-- If $a \le b$, then $a + c \le b + c$. -/
Statement add_le_add_right (a b c : ℚ) : a ≤ b → a + c ≤ b + c := by
  intro h
  Hint "Use `add_le_add` with `{h}` and `le_refl c`."
  Branch
    rw [le_iff_nonneg] at h ⊢
    Hint "Unfolding works, but there is a shorter way: `add_le_add` with `{h}` and `le_refl c`."
  exact add_le_add a b c c h (le_refl c)

Conclusion "
Old theorems combine into new ones.
"

TheoremTab "ℚ"

end MyRat
