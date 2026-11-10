import Game.Levels.Tutorial.L03_Rw

World "Tutorial"
Level 4
Title "Reading an error"

Introduction "
Mistakes are normal. Lean tells you what went wrong.

Try `exact hp` first, on purpose. You will see an error like:

```
type mismatch
  hp
has type
  P : Prop
but is expected to have type
  Q : Prop
```

Read it like this: you gave `hp`, which proves `P`.
But the goal is `Q`. So `hp` does not fit.

Nothing breaks. Fix the line and try again.
"

/-- If $P$ and $Q$ are true, then $Q$ is true. -/
Statement (P Q : Prop) (hp : P) (hq : Q) : Q := by
  Hint "Which hypothesis proves `Q`? Its name goes after `exact`."
  Hint (hidden := true) "`{hq}` proves `Q`. Type `exact {hq}`."
  exact hq

Conclusion "
When you see `type mismatch`, compare the two types in the message.
"
