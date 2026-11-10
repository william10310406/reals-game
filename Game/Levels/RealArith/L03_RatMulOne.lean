import Game.Levels.RealArith.L02_RatMulAssoc

World "RealArith"
Level 3
Title "One in ℚ"

namespace MyRat

Introduction "
The rational `1` is `frac 1 1` (theorem `one_def`).
"

/-- $x \cdot 1 = x$ for rationals. -/
Statement mul_one (x : ℚ) : x * 1 = x := by
  obtain ⟨a, b, hb, rfl⟩ := exists_frac x
  Hint "Write `1` as a fraction: `rw [one_def]`."
  Branch
    rw [mul_comm]
    Hint "Swapping does not help: `1` is still not a fraction.
    `frac_mul_frac` needs two fractions, so first write `1` as `frac 1 1` with `rw [one_def]`."
  rw [one_def]
  Hint "Multiply: `rw [frac_mul_frac {hb} MyNat.one_ne_zero]`."
  rw [frac_mul_frac hb MyNat.one_ne_zero]
  Hint "Now `MyInt.mul_one` and `MyNat.mul_one`."
  rw [MyInt.mul_one, MyNat.mul_one]

Conclusion "
`1` changes nothing, in `ℚ` as in `ℤ` and `ℕ`.
"

NewTheorem MyRat.one_def
TheoremTab "ℚ"

end MyRat
