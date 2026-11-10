import Game.Levels.Reals.L05_Half

World "Reals"
Level 6
Title "Cauchy sequences"

namespace MyRat

open MyNat (succ)

Introduction "
A sequence `s : ℕ → ℚ` is **Cauchy** when its terms get close together:

`IsCauchy s` means: for every `k` there is an `N` such that
`s m - s n ≤ frac 1 (succ k)` for all `m n` with `N ≤ m` and `N ≤ n`.

It is a `∀`, so start with `intro`. `const c` is the sequence `c, c, c, ...`;
`const_apply` says `const c n = c`.
"

/-- The constant sequence is Cauchy. -/
Statement const_cauchy (c : ℚ) : IsCauchy (const c) := by
  Hint "Start with `intro k`."
  intro k
  Hint "Any `N` works here. Try `use 0`."
  use 0
  intro m n hm hn
  Hint "Compute the terms with `const_apply`, then `sub_eq_add_neg` and `add_neg`."
  Branch
    rw [sub_eq_add_neg]
    Hint "Compute `const c m` and `const c n` first with `const_apply`, so that `add_neg` fits."
  rw [const_apply, const_apply, sub_eq_add_neg, add_neg]
  exact eps_nonneg k

Conclusion "
Constant sequences are the simplest Cauchy sequences.
"

NewTheorem MyRat.const_apply
NewDefinition MyRat.const MyRat.IsCauchy
TheoremTab "ℚ"

end MyRat
