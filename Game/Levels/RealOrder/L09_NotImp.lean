import Game.Levels.RealOrder.L08_NotForall

World "RealOrder"
Level 9
Title "Not implies"

namespace MyLogic

Introduction "
If `P → Q` is false, then `P` is true and `Q` is false.
"

/-- If $P \to Q$ fails, then $P$ holds and $Q$ fails. -/
Statement not_imp (P Q : Prop) : ¬ (P → Q) → P ∧ ¬ Q := by
  intro h
  Hint "Ask whether `P` is true: `by_cases hp : P`."
  by_cases hp : P
  · constructor
    · exact hp
    · intro hq
      apply h
      intro hp2
      exact hq
  · Hint "If `P` is false, then `P → Q` is true. That contradicts `{h}`."
    exfalso
    apply h
    intro hp2
    exfalso
    exact hp hp2

Conclusion "
These three rules let you push `¬` inside: `¬ ∃` → `∀ ¬`, `¬ ∀` → `∃ ¬`, `¬ (P → Q)` → `P ∧ ¬ Q`.
"

TheoremTab "logic"

end MyLogic
