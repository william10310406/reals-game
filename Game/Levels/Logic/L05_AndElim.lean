import Game.Levels.Logic.L04_And

World "Logic"
Level 5
Title "Taking And apart"

Introduction "
If `h : P ∧ Q`, you can split it:
`obtain ⟨hp, hq⟩ := h` gives `hp : P` and `hq : Q`.

Type `⟨` as `\\<` and `⟩` as `\\>`.
"

/-- If $P \land Q$, then $Q \land P$. -/
Statement (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  Hint "Take `{h}` apart: `obtain ⟨hp, hq⟩ := {h}`."
  obtain ⟨hp, hq⟩ := h
  Hint "Now build `Q ∧ P` with `constructor`."
  constructor
  exact hq
  exact hp

Conclusion "
`obtain` takes things apart, `constructor` puts them together.
"

NewTactic obtain
