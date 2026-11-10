import Game.Levels.RealOrder.L06_LeAntisymm

World "RealOrder"
Level 7
Title "Nothing exists"

namespace MyLogic

Introduction "
Next we want: for any two reals, `x ≤ y` or `y ≤ x`. The proof argues
*if not, then …*. So first some logic about `¬`.
"

/-- If there is no $x$ with $P(x)$, then $P(x)$ fails for every $x$. -/
Statement not_exists (α : Type) (P : α → Prop) : ¬ (∃ x, P x) → ∀ x, ¬ P x := by
  Hint "Introduce everything: `intro h x hx`."
  intro h x hx
  Hint "`{h}` says there is no such `x`. But `{x}` is one. `apply {h}`."
  Branch
    exfalso
    Hint "Good: now `apply {h}`."
  apply h
  use x
  exact hx

Conclusion "
`¬ ∃` becomes `∀ ¬`.
"

TheoremTab "logic"

end MyLogic
