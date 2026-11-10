import Game.Levels.Reals.L06_ConstCauchy

World "Reals"
Level 7
Title "Close sequences"

namespace MyRat

open MyNat (succ)

Introduction "
Two sequences are **close** when their terms get close together:

`Close s t` means: for every `k` there is an `N` such that for all `n ≥ N`,
`s n - t n ≤ frac 1 (succ k)` and `t n - s n ≤ frac 1 (succ k)`.

Close Cauchy sequences will be the **same real number**. First: every sequence is close to itself.
"

/-- Every sequence is close to itself. -/
Statement close_refl (s : ℕ → ℚ) : Close s s := by
  intro k
  use 0
  intro n hn
  Hint "`rw [sub_eq_add_neg, add_neg]` changes both parts at once."
  rw [sub_eq_add_neg, add_neg]
  constructor
  exact eps_nonneg k
  exact eps_nonneg k

Conclusion "
`Close` is reflexive.
"

NewDefinition MyRat.Close
TheoremTab "ℚ"

end MyRat
