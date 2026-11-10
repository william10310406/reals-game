import Game.Levels.Logic.L07_OrElim

World "Logic"
Level 8
Title "Not"

Introduction "
`¬ P` means `P → False`. `False` is a statement with no proof.

So to prove `¬ P`, use `intro`: assume `P` and reach `False`.
And if `hn : ¬ P` and `hp : P`, then `hn hp` is a proof of `False`.
"

/-- If $P$, then not not $P$. -/
Statement (P : Prop) (hp : P) : ¬ ¬ P := by
  Hint "`¬ ¬ P` is `¬ P → False`. Start with `intro hn`."
  intro hn
  Hint "Now the goal is `False`, and `{hn} : ¬ P`. Feed `{hp}` to `{hn}`."
  exact hn hp

Conclusion "
`¬ P` is just an implication into `False`.
"
