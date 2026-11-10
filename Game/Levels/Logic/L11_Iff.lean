import Game.Levels.Logic.L10_Contra

World "Logic"
Level 11
Title "If and only if"

Introduction "
`P ↔ Q` means: `P → Q` and `Q → P`.

`constructor` splits `P ↔ Q` into these two goals.
"

/-- $P \land Q \iff Q \land P$. -/
Statement (P Q : Prop) : P ∧ Q ↔ Q ∧ P := by
  Hint "Use `constructor` to get two implications."
  constructor
  Hint "First direction. Introduce the hypothesis."
  intro h
  obtain ⟨hp, hq⟩ := h
  constructor
  exact hq
  exact hp
  Hint "Second direction. Same idea."
  intro h
  obtain ⟨hq, hp⟩ := h
  constructor
  exact hp
  exact hq

Conclusion "
An `↔` is two proofs in one.
"
