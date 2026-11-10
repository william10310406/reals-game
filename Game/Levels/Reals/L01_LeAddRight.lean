import Game.MyReal.Seq

World "Reals"
Level 1
Title "Big indices"

namespace MyNat

Introduction "
In this world we work with sequences `s 0, s 1, s 2, ...` of rationals.
We often need: if `n ≥ N₁ + N₂`, then `n ≥ N₁`. It starts with this.
"

/-- $a \le a + b$. -/
Statement le_add_right (a b : ℕ) : a ≤ a + b := by
  rw [le_iff_exists_add]
  Hint "Which number do you `use`?"
  use b
  Hint "The goal is the same on both sides."
  rfl

Conclusion "
With `le_trans` this gives: `N₁ + N₂ ≤ n` implies `N₁ ≤ n`.
"

TheoremTab "≤"

end MyNat
