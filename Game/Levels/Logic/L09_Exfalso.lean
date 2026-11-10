import Game.Levels.Logic.L08_Not

World "Logic"
Level 9
Title "From nonsense"

Introduction "
From `False`, anything follows.

If your hypotheses contradict each other, type `exfalso`.
It changes any goal to `False`. Then prove `False`.
"

/-- If $P$ and not $P$, then $Q$. -/
Statement (P Q : Prop) (hp : P) (hn : ¬ P) : Q := by
  Hint "You know nothing about `Q`. But `{hp}` and `{hn}` contradict. Type `exfalso`."
  exfalso
  Hint "Now prove `False` from `{hn}` and `{hp}`."
  exact hn hp

Conclusion "
`exfalso` is the tool for contradictions.
"

NewTactic exfalso
