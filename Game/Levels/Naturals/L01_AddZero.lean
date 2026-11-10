import Game.Metadata

World "Naturals"
Level 1
Title "Adding zero"

namespace MyNat

Introduction "
Here are our natural numbers `ℕ`. Every number is `0` or `succ n`,
the number after `n`.

Addition has two rules. The first is `add_zero : a + 0 = a`.
Find it in your inventory, under *Theorems*.

Use `rw [add_zero]` to remove a `+ 0`.
"

/-- $(a + 0) + (b + 0) = a + b$. -/
Statement (a b : ℕ) : a + 0 + (b + 0) = a + b := by
  Hint "`add_zero` says `x + 0 = x`. Try `rw [add_zero]`."
  rw [add_zero]
  Hint "One `+ 0` is gone. Remove the other one the same way."
  rw [add_zero]

Conclusion "
`rw [add_zero]` rewrote the first `_ + 0` it found. The second time it found the other one.
"

NewTheorem MyNat.add_zero
NewDefinition MyNat MyNat.add
TheoremTab "+"

end MyNat
