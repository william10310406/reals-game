import Game.Levels.RealLimits.L01_EpsNonneg

World "RealLimits"
Level 2
Title "Two halves"

namespace MyReal

open MyNat (succ)

Introduction "
Two halves make a whole, now in `ℝ`: `eps (succ k + k)` is half of `eps k`.
"

/-- $\frac{1}{2(k+1)} + \frac{1}{2(k+1)} = \frac{1}{k+1}$ in $\mathbb{R}$. -/
Statement eps_half (k : ℕ) : eps (succ k + k) + eps (succ k + k) = eps k := by
  Hint "`rw [eps_def (succ k + k), eps_def k, ← ofRat_add]`."
  rw [eps_def (succ k + k), eps_def k, ← ofRat_add]
  Hint "Now write `succ (succ k + k)` as `succ k + succ k` with `← MyNat.add_succ`,
  then use `MyRat.half (succ k) (MyNat.succ_ne_zero k)`."
  rw [← MyNat.add_succ, MyRat.half (succ k) (MyNat.succ_ne_zero k)]

Conclusion "
`eps_half` is the tool for every `ε/2` argument in `ℝ`.
"

TheoremTab "limℝ"

end MyReal
