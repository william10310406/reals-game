import Game.Levels.Rationals.L04_AddComm

World "Rationals"
Level 5
Title "Adding zero"

namespace MyRat

open MyInt (mk)

Introduction "
The rational `0` is `frac 0 1` (theorem `zero_def`).
"

/-- $x + 0 = x$ for rationals. -/
Statement add_zero (x : ℚ) : x + 0 = x := by
  obtain ⟨a, b, hb, rfl⟩ := exists_frac x
  Hint "Write `0` as `frac 0 1`, then add. The proof of `1 ≠ 0` is `MyNat.one_ne_zero`."
  Branch
    rw [add_comm]
    Hint "Swapping does not help: `0` is still not a fraction. Use `rw [zero_def]`."
  rw [zero_def, frac_add_frac hb MyNat.one_ne_zero]
  Hint "Clean up: `← MyInt.one_def`, `MyInt.mul_one`, `MyInt.zero_mul`, `MyInt.add_zero`, `MyNat.mul_one`."
  rw [← MyInt.one_def, MyInt.mul_one, MyInt.zero_mul, MyInt.add_zero, MyNat.mul_one]

Conclusion "
Your theorems about `ℤ` and `ℕ` do the work.
"

NewTheorem MyRat.zero_def
TheoremTab "ℚ"

end MyRat
