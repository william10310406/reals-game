import Game.Levels.Rationals.L01_OneNeZero

World "Rationals"
Level 2
Title "Products are not zero"

namespace MyNat

Introduction "
When we add fractions, the new denominator is `b * d`. It must not be `0` either.

You proved `eq_zero_of_add_eq_zero` in the Naturals world. It helps here.
"

/-- If $a \ne 0$ and $b \ne 0$, then $ab \ne 0$. -/
Statement mul_ne_zero (a b : ℕ) : a ≠ 0 → b ≠ 0 → a * b ≠ 0 := by
  intro ha hb
  Hint "Split `b` with `cases b with d`."
  Branch
    cases a with d
    Hint "Splitting `a` works too, but `mul_succ` works on the right factor. The hints follow `cases b with d`."
  cases b with d
  · Hint "`{hb} : 0 ≠ 0` is absurd. Use `exfalso`, then `apply {hb}`."
    exfalso
    apply hb
    rfl
  · Hint "Use `mul_succ`. Then the goal is `a * {d} + a ≠ 0`."
    rw [mul_succ]
    intro h
    Hint "From `{h}`, the summand `a` must be `0`. Use `apply {ha}`."
    apply ha
    exact eq_zero_of_add_eq_zero (a * d) a h

Conclusion "
Old theorems keep paying off.
"

TheoremTab "ℕ"

end MyNat
