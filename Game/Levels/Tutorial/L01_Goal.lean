import Game.Metadata

World "Tutorial"
Level 1
Title "The goal"

Introduction "
Look at the panel in the middle.

* The **goal** is what you must prove. In the editor it comes after `⊢`.
* The **hypotheses** (assumptions) are what you know.

Here `hp : P` says: `hp` is a proof of `P`.
The goal is `P`. So `hp` is exactly what you need.

Type `exact hp` and press Enter.
"

/-- If `P` is true, then `P` is true. -/
Statement (P : Prop) (hp : P) : P := by
  Hint "The goal is `P`. The hypothesis `{hp}` is a proof of `P`. Try `exact {hp}`."
  Hint (hidden := true) "`exact P` fails: `P` is the statement, not a proof. Use the proof's name."
  exact hp

Conclusion "
Well done. `exact` closes a goal with a proof that matches it exactly.
"

NewTactic exact
