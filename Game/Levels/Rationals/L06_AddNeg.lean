import Game.Levels.Rationals.L05_AddZero

World "Rationals"
Level 6
Title "Negatives"

namespace MyRat

open MyInt (mk)

Introduction "
`neg_frac : -frac a b = frac (-a) b`.
"

/-- $x + (-x) = 0$ for rationals. -/
Statement add_neg (x : ℚ) : x + -x = 0 := by
  obtain ⟨a, b, hb, rfl⟩ := exists_frac x
  Branch
    rw [zero_def]
    Hint "Good. `-frac a b` must become a fraction too: `neg_frac`."
  rw [neg_frac, frac_add_frac hb hb, zero_def]
  Hint "Cross-multiply with `frac_eq`. The denominators are `b * b` and `1`."
  rw [frac_eq (MyNat.mul_ne_zero b b hb hb) MyNat.one_ne_zero]
  Hint "`← MyInt.one_def`, `MyInt.mul_one`, `MyInt.zero_mul`, then `MyInt.neg_mul` and `MyInt.add_neg`."
  rw [← MyInt.one_def, MyInt.mul_one, MyInt.zero_mul, MyInt.neg_mul, MyInt.add_neg]

Conclusion "
Every rational has a negative.
"

NewTheorem MyRat.neg_frac
TheoremTab "ℚ"

end MyRat
