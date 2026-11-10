import Game.MyRat.Basic

World "Rationals"
Level 1
Title "One is not zero"

namespace MyNat

Introduction "
In `ℤ` you cannot divide. So we build fractions `a / b`.

A denominator must not be `0`. We will often need facts like `1 ≠ 0`.
Recall: `x ≠ y` means `x = y → False`.
"

/-- $1 \ne 0$ in $\mathbb{N}$. -/
Statement one_ne_zero : (1 : ℕ) ≠ 0 := by
  Hint "Start with `intro h`."
  Branch
    rw [one_eq_succ_zero]
    Hint "Good. Now `≠` means `→ False`: `intro h`."
  intro h
  Hint "Write `1` as `succ 0` in `{h}`."
  rw [one_eq_succ_zero] at h
  Hint "Now `{h} : succ 0 = 0`. Use `apply zero_ne_succ 0`, then `rw [{h}]`."
  apply zero_ne_succ 0
  rw [h]

Conclusion "
`MyNat.one_ne_zero` is in your inventory.
"

TheoremTab "ℕ"

end MyNat
