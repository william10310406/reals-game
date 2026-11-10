import Game.Levels.Limits.L05_CauchyOfTendsto

World "Limits"
Level 6
Title "The real number of a limit"

namespace MyRat

open MyNat (succ)

Introduction "
If `s → L`, then the real number of `s` is the real number of the constant sequence `L`.
"

/-- If $s \to L$, then $s$ and the constant sequence $L$ are the same real number. -/
Statement ofSeq_eq_of_tendsto (s : ℕ → ℚ) (L : ℚ) (hs : IsCauchy s) :
    Tendsto s L → MyReal.ofSeq s hs = MyReal.ofSeq (const L) (const_cauchy L) := by
  intro h
  Hint "Use `MyReal.ofSeq_eq`, then `← tendsto_iff_close`."
  rw [MyReal.ofSeq_eq, ← tendsto_iff_close]
  exact h

Conclusion "
A sequence that converges to a rational `L` *is* the real number `L`.
"

TheoremTab "lim"

end MyRat
