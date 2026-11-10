import Game.Levels.RealOrder.L07_NotExists

World "RealOrder"
Level 8
Title "Not for all"

namespace MyLogic

Introduction "
If `P x` is not true for all `x`, then some `x` fails.
This needs a new tool: `by_cases h : P` splits into the case `h : P` and the case `h : ¬ P`.
(It uses that every statement is true or false.)
"

/-- If not every $x$ has $P(x)$, then some $x$ has $\neg P(x)$. -/
Statement not_forall (α : Type) (P : α → Prop) : ¬ (∀ x, P x) → ∃ x, ¬ P x := by
  intro h
  Hint "Is there an `x` with `¬ P x`? Ask: `by_cases h2 : ∃ x, ¬ P x`."
  Branch
    by_cases h2 : ∀ x, P x
    Hint "That case split only repeats `{h}`. Ask about the goal instead:
    `by_cases h2 : ∃ x, ¬ P x`."
  by_cases h2 : ∃ x, ¬ P x
  · exact h2
  · Hint "Now there is none. Then every `x` has `P x`, against `{h}`. Start with `exfalso` and `apply {h}`."
    exfalso
    apply h
    intro x
    Hint "Ask again: `by_cases hx : P x`."
    by_cases hx : P x
    · exact hx
    · exfalso
      apply h2
      use x
      exact hx

Conclusion "
`¬ ∀` becomes `∃ ¬`. Here `by_cases` was needed.
"

NewTactic by_cases
TheoremTab "logic"

end MyLogic
