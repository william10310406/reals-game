import Game.Levels.Logic.L14_ExistsElim

World "Logic"
Level 15
Title "Swap the quantifiers"

Introduction "
Boss level. Use everything from this world.

If one `x` works for every `y`, then for every `y` some `x` works.
"

/-- If $\exists x, \forall y, R(x, y)$, then $\forall y, \exists x, R(x, y)$. -/
Statement (α β : Type) (R : α → β → Prop) : (∃ x, ∀ y, R x y) → ∀ y, ∃ x, R x y := by
  Hint "Introduce the hypothesis, and then `y`."
  intro h
  intro y
  Hint "Take `{h}` apart with `obtain`."
  obtain ⟨x, hx⟩ := h
  Hint "Which object do you `use`?"
  use x
  Hint (hidden := true) "`{hx} {y}` is a proof of `R {x} {y}`."
  exact hx y

Conclusion "
You finished Logic. Next you build the natural numbers.
"
