import Game.Levels.Logic.L11_Iff

World "Logic"
Level 12
Title "For all"

Introduction "
`∀ x, P x` means: `P x` is true for every `x`.

* To prove it: `intro x`, then prove `P x`.
* To use `h : ∀ x, P x`: `h a` is a proof of `P a`.
"

/-- If every $x$ with $P(x)$ has $Q(x)$, and every $x$ has $P(x)$, then every $x$ has $Q(x)$. -/
Statement (α : Type) (P Q : α → Prop) (h : ∀ x, P x → Q x) (hp : ∀ x, P x) :
    ∀ x, Q x := by
  Hint "Start with `intro x`."
  intro x
  Hint "Now prove `Q {x}`. `{h} {x}` is a proof of `P {x} → Q {x}`."
  apply h x
  Hint "And `{hp} {x}` proves `P {x}`."
  exact hp x

Conclusion "
A `∀` works like a function: give it an object, get a proof.
"
