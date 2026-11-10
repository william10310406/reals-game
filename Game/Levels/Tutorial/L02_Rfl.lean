import Game.Levels.Tutorial.L01_Goal

World "Tutorial"
Level 2
Title "Equal to itself"

Introduction "
Every object is equal to itself.

The tactic `rfl` proves goals like `x = x`.
The two sides must be exactly the same.
"

/-- $x = x$. -/
Statement (α : Type) (x : α) : x = x := by
  Hint "Both sides are `{x}`. Type `rfl`."
  rfl

Conclusion "
`rfl` is short for *reflexivity*: everything equals itself.
"

NewTactic rfl
