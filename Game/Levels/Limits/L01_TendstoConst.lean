import Game.MyReal.Limit

World "Limits"
Level 1
Title "Limits"

namespace MyRat

open MyNat (succ)

Introduction "
`Tendsto s L` means: the sequence `s` tends to `L`. For every `k` there is an `N`
such that for all `n ≥ N`: `s n - L ≤ frac 1 (succ k)` and `L - s n ≤ frac 1 (succ k)`.

This is the same as `Close s (const L)`: theorem `tendsto_iff_close`.
"

/-- The constant sequence $c, c, c, \dots$ tends to $c$. -/
Statement tendsto_const (c : ℚ) : Tendsto (const c) c := by
  Hint "Use `rw [tendsto_iff_close]`, then a theorem from the Reals world."
  Branch
    intro k
    Hint "That works, but the Reals world already did this. Use `rw [tendsto_iff_close]`, then `close_refl`."
  rw [tendsto_iff_close]
  exact close_refl (const c)

Conclusion "
Limits are a special case of closeness.
"

NewTheorem MyRat.tendsto_iff_close
NewDefinition MyRat.Tendsto
TheoremTab "lim"

end MyRat
