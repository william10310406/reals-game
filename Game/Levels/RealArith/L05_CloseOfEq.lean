import Game.Levels.RealArith.L04_RatMulAdd

World "RealArith"
Level 5
Title "Equal terms are close"

namespace MyRat

Introduction "
Most laws of `ℝ` will come from laws of `ℚ`, term by term.
This tool turns *equal terms* into *close sequences*.
"

/-- If $s_n = t_n$ for every $n$, then $s$ and $t$ are close. -/
Statement close_of_eq (s t : ℕ → ℚ) : (∀ n, s n = t n) → Close s t := by
  Hint "Introduce the hypothesis and `k`: `intro h k`."
  intro h k
  Hint "Any `N` works. Try `use 0`."
  use 0
  intro n hn
  Hint "Replace `s n` by `t n`: `rw [{h} n]`."
  Branch
    constructor
    Hint "First replace `s n` by `t n` with `rw [{h} n]` (before `constructor`, so both parts change)."
  rw [h n, sub_eq_add_neg, add_neg]
  constructor
  exact eps_nonneg k
  exact eps_nonneg k

Conclusion "
From now on, a law of `ℝ` is: write the reals as sequences, then `apply MyRat.close_of_eq`,
then prove the law of `ℚ` for the terms.
"

TheoremTab "ℚ"

end MyRat
