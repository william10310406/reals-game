import Game.Levels.Logic.L09_Exfalso

World "Logic"
Level 10
Title "Contrapositive"

Introduction "
Sometimes it helps to name a fact in the middle of a proof.

`have hq : Q := f hp` adds `hq : Q` to your hypotheses.
"

/-- If $P \implies Q$, then $\lnot Q \implies \lnot P$. -/
Statement (P Q : Prop) (f : P → Q) : ¬ Q → ¬ P := by
  Hint "Introduce `hnq : ¬ Q`, then `hp : P`."
  intro hnq
  intro hp
  Hint "Get `Q` from `{f}` and `{hp}`: `have hq : Q := {f} {hp}`."
  have hq : Q := f hp
  Hint "Now `{hnq}` and `{hq}` give `False`."
  exact hnq hq

Conclusion "
This is the *contrapositive*. You will use it later.
"

NewTactic «have»
