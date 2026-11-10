import Game.MyReal.Ops

World "RealArith"
Level 1
Title "Products in ℚ commute"

namespace MyRat

Introduction "
`ℝ` computes term by term on sequences of rationals.
So before we multiply reals, we need the rules for `*` on `ℚ`.

Recall `frac_mul_frac hb hd : frac a b * frac c d = frac (a * c) (b * d)`.
"

/-- $xy = yx$ for rationals. -/
Statement mul_comm (x y : ℚ) : x * y = y * x := by
  Hint "Write both numbers as fractions: `obtain ⟨a, b, hb, rfl⟩ := exists_frac x`,
  and the same for `y`."
  obtain ⟨a, b, hb, rfl⟩ := exists_frac x
  obtain ⟨c, d, hd, rfl⟩ := exists_frac y
  Hint "Multiply out both sides: `rw [frac_mul_frac {hb} {hd}, frac_mul_frac {hd} {hb}]`."
  Branch
    rw [frac_mul_frac hb hd]
    rw [MyInt.mul_comm a c]
    Hint "The right side is still a product of two fractions.
    Multiply it out too: `rw [frac_mul_frac {hd} {hb}]`."
  rw [frac_mul_frac hb hd, frac_mul_frac hd hb]
  Hint "Swap the products: `rw [MyInt.mul_comm a c, MyNat.mul_comm b d]`."
  rw [MyInt.mul_comm a c, MyNat.mul_comm b d]

Conclusion "
Products of fractions commute because products in `ℤ` and `ℕ` do.
"

TheoremTab "ℚ"

end MyRat
