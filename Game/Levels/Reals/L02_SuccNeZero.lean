import Game.Levels.Reals.L01_LeAddRight

World "Reals"
Level 2
Title "succ is not zero"

namespace MyNat

Introduction "
We measure smallness with `1/(k+1)`, written `frac 1 (succ k)`.
Its denominator must not be `0`.
"

/-- $\operatorname{succ}(n) \ne 0$. -/
Statement succ_ne_zero (n : ℕ) : succ n ≠ 0 := by
  intro h
  Hint "Use `apply zero_ne_succ n`, then `rw [{h}]`."
  apply zero_ne_succ n
  rw [h]

Conclusion "
So `frac 1 (succ k)` is a real fraction for every `k`.
"

TheoremTab "ℕ"

end MyNat
