import Game.Levels.Rationals.L03_FracScale

World "Rationals"
Level 4
Title "Adding fractions"

namespace MyRat

open MyInt (mk)

Introduction "
`frac_add_frac hb hd : frac a b + frac c d = frac (a * mk d 0 + c * mk b 0) (b * d)`.

To prove something for every rational `x`, write it as a fraction:
`obtain ⟨a, b, hb, rfl⟩ := exists_frac x`.
"

/-- $x + y = y + x$ for rationals. -/
Statement add_comm (x y : ℚ) : x + y = y + x := by
  Hint "Write `x` as a fraction: `obtain ⟨a, b, hb, rfl⟩ := exists_frac x`."
  obtain ⟨a, b, hb, rfl⟩ := exists_frac x
  obtain ⟨c, d, hd, rfl⟩ := exists_frac y
  Hint "Add on both sides: `rw [frac_add_frac {hb} {hd}, frac_add_frac {hd} {hb}]`."
  rw [frac_add_frac hb hd, frac_add_frac hd hb]
  Hint "Make the denominators equal with `MyNat.mul_comm d b`, then `ac_rfl`."
  rw [MyNat.mul_comm d b]
  ac_rfl

Conclusion "
Addition of rationals is commutative.
"

NewTheorem MyRat.exists_frac MyRat.frac_add_frac
TheoremTab "ℚ"

end MyRat
