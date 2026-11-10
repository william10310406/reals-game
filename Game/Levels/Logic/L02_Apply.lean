import Game.Levels.Logic.L01_Intro

World "Logic"
Level 2
Title "Working backwards"

Introduction "
If `f : P → Q` and the goal is `Q`, you can work backwards:
`apply f` changes the goal to `P`.

You can also go forwards: `f hp` is a proof of `Q` when `hp : P`.
"

/-- If $P \implies Q$ and $P$, then $Q$. -/
Statement (P Q : Prop) (f : P → Q) (hp : P) : Q := by
  Hint "`{f}` turns a proof of `P` into a proof of `Q`. Try `apply {f}`."
  Branch
    exact f hp
  apply f
  Hint "To get `Q` from `{f}`, you need `P`. You have it."
  exact hp

Conclusion "
`apply f` and `exact f hp` are two ways to say the same thing.
"

NewTactic apply
