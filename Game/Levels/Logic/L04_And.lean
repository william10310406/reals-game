import Game.Levels.Logic.L03_Chain

World "Logic"
Level 4
Title "And"

Introduction "
`P ∧ Q` means: `P` and `Q`.

To prove `P ∧ Q`, prove both. The tactic `constructor` gives you two goals.
"

/-- If $P$ and $Q$, then $P \land Q$. -/
Statement (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  Hint "Type `constructor` to split the goal in two."
  constructor
  Hint "First goal: `P`."
  exact hp
  Hint "Second goal: `Q`."
  exact hq

Conclusion "
After `constructor`, you solve the goals one by one.
"

NewTactic constructor
