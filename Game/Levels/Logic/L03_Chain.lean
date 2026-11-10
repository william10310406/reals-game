import Game.Levels.Logic.L02_Apply

World "Logic"
Level 3
Title "A chain"

Introduction "
`P → Q → R` means `P → (Q → R)`. Arrows group to the right.

Use `intro` several times, then work backwards.
"

/-- If $P \implies Q$ and $Q \implies R$, then $P \implies R$. -/
Statement (P Q R : Prop) : (P → Q) → (Q → R) → P → R := by
  Hint "Three arrows: use `intro` three times, one name each."
  intro f
  intro g
  intro hp
  Hint "You want `R`. Which hypothesis ends in `R`?"
  apply g
  Hint (hidden := true) "Now you need `Q`. Use `{f}`."
  apply f
  exact hp

Conclusion "
A chain of implications is just a chain of `apply`.
"
