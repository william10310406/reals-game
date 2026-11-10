import Game.Levels.Logic.L12_Forall

World "Logic"
Level 13
Title "There exists"

Introduction "
`∃ x, P x` means: some `x` has `P x`.

To prove it, name the `x`: `use a` changes the goal to `P a`.
"

/-- If $P(a)$, then there is an $x$ with $P(x)$. -/
Statement (α : Type) (P : α → Prop) (a : α) (h : P a) : ∃ x, P x := by
  Hint "Which object works? Type `use {a}`."
  use a
  exact h

Conclusion "
To prove `∃`, give an example.
"

NewTactic use
