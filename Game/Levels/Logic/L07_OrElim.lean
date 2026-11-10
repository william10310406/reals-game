import Game.Levels.Logic.L06_Or

World "Logic"
Level 7
Title "Using Or"

Introduction "
If `h : P ∨ Q`, you do not know which side is true. So you check both cases.

`obtain hp | hq := h` gives two goals:
one with `hp : P`, one with `hq : Q`.
"

/-- If $P \lor Q$, then $Q \lor P$. -/
Statement (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  Hint "Split `{h}` into two cases: `obtain hp | hq := {h}`."
  Branch
    left
    Hint "Careful: you do not know `Q` yet. First split `{h}` with `obtain`."
  obtain hp | hq := h
  Hint "Case 1: you have `{hp} : P`."
  right
  exact hp
  Hint "Case 2: you have `{hq} : Q`."
  left
  exact hq

Conclusion "
With `∨` in a hypothesis, always split into cases first.
"
