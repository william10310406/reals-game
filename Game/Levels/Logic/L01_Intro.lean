import Game.Metadata

World "Logic"
Level 1
Title "If P then P"

Introduction "
`P → Q` means: if `P`, then `Q`.

To prove `P → Q`, assume `P` and prove `Q`.
The tactic `intro hp` does the assuming: it adds `hp : P` to your hypotheses.
"

/-- $P \implies P$. -/
Statement (P : Prop) : P → P := by
  Hint "The goal is an implication. Start with `intro hp`."
  intro hp
  Hint "Now `{hp} : P` is a hypothesis and the goal is `P`."
  exact hp

Conclusion "
`intro` is how you assume something.
"

NewTactic intro
