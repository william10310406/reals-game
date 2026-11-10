import Game.Levels.Logic.L13_Exists

World "Logic"
Level 14
Title "Using there exists"

Introduction "
If `h : ∃ x, P x`, you get an object and a proof:
`obtain ⟨x, hx⟩ := h` gives `x` and `hx : P x`.

For `h : ∃ x, P x ∧ Q x` you can split everything at once:
`obtain ⟨x, hp, hq⟩ := h`.
"

/-- If some $x$ has $P(x)$ and $Q(x)$, then some $x$ has $Q(x)$. -/
Statement (α : Type) (P Q : α → Prop) (h : ∃ x, P x ∧ Q x) : ∃ x, Q x := by
  Hint "Take `{h}` apart: `obtain ⟨x, hp, hq⟩ := {h}`."
  obtain ⟨x, hp, hq⟩ := h
  Hint "Now `{x}` is your example."
  use x
  exact hq

Conclusion "
`obtain` works for `∧`, `∨` and `∃`.
"
