import Game.Levels.Logic.L05_AndElim

World "Logic"
Level 6
Title "Or"

Introduction "
`P ∨ Q` means: `P` or `Q` (or both).

To prove `P ∨ Q`, prove one side:

* `left` changes the goal to `P`.
* `right` changes the goal to `Q`.
"

/-- If $Q$, then $P \lor Q$. -/
Statement (P Q : Prop) (hq : Q) : P ∨ Q := by
  Hint "You know `Q`. Which side is `Q`?"
  Branch
    left
    Hint "Now you must prove `P`. But you only know `Q`. Go back and use `right`."
  right
  exact hq

Conclusion "
Choose the side you can prove.
"

NewTactic left right
