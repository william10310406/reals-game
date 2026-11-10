import Game.Levels.Reals.L03_NegZero

World "Reals"
Level 4
Title "Small but not negative"

namespace MyRat

open MyNat (succ)

Introduction "
The number `frac 1 (succ k)` is `1/(k+1)`. It is our measure of *small*.
Show that it is `≥ 0`.
"

/-- $0 \le \frac{1}{k+1}$. -/
Statement eps_nonneg (k : ℕ) : 0 ≤ frac 1 (succ k) := by
  Hint "Unfold `≤`, and simplify `x - 0` with `sub_eq_add_neg`, `neg_zero`, `add_zero`."
  rw [le_iff_nonneg, sub_eq_add_neg, neg_zero, add_zero]
  Hint "Use `nonneg_frac` with the proof `MyNat.succ_ne_zero k`."
  rw [nonneg_frac (MyNat.succ_ne_zero k)]
  Hint "Now `0 ≤ 1` in `ℤ`. Use `MyInt.nonneg_iff`."
  Branch
    rw [MyInt.le_iff]
    Hint "That works too, but `MyInt.nonneg_iff` is shorter: `0 ≤ x ↔ ∃ c, x = mk c 0`."
  rw [MyInt.nonneg_iff]
  use 1
  rw [MyInt.one_def]

Conclusion "
`eps_nonneg k` will be used many times.
"

TheoremTab "ℚ"

end MyRat
