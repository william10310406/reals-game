import Game.Levels.Limits.L01_TendstoConst

World "Limits"
Level 2
Title "Constants add up"

namespace MyRat

open MyNat (succ)

Introduction "
The sum of the constant sequences `a` and `b` is close to the constant sequence `a + b`.
"

/-- $(a, a, \dots) + (b, b, \dots)$ is close to $(a + b, a + b, \dots)$. -/
Statement close_const_add (a b : ℚ) : Close (addSeq (const a) (const b)) (const (a + b)) := by
  intro k
  use 0
  intro n hn
  Hint "Compute: `addSeq_apply`, then `const_apply` three times, then `sub_eq_add_neg` and `add_neg`."
  rw [addSeq_apply, const_apply, const_apply, const_apply, sub_eq_add_neg, add_neg]
  constructor
  exact eps_nonneg k
  exact eps_nonneg k

Conclusion "
Term by term, the two sequences are equal.
"

TheoremTab "lim"

end MyRat
