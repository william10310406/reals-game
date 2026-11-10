import Game.Levels.Rationals.L06_AddNeg

World "Rationals"
Level 7
Title "Minus a sum"

namespace MyRat

open MyInt (mk)

Introduction "
Show that `-(x + y) = -x + -y` for rationals.
"

/-- $-(x + y) = -x + (-y)$ for rationals. -/
Statement neg_add (x y : ℚ) : -(x + y) = -x + -y := by
  obtain ⟨a, b, hb, rfl⟩ := exists_frac x
  obtain ⟨c, d, hd, rfl⟩ := exists_frac y
  Hint "Compute: `frac_add_frac`, `neg_frac` three times, `frac_add_frac` again."
  Branch
    rw [neg_frac]
    Hint "The left side is `-(sum)`. Add the fractions first with `frac_add_frac {hb} {hd}`."
  rw [frac_add_frac hb hd, neg_frac, neg_frac, neg_frac, frac_add_frac hb hd]
  Hint "Both sides have the same denominator. Fix the numerators with
  `MyInt.neg_add` and `MyInt.neg_mul` twice."
  rw [MyInt.neg_add, MyInt.neg_mul, MyInt.neg_mul]

Conclusion "
Same rule as in `ℤ`.
"

TheoremTab "ℚ"

end MyRat
