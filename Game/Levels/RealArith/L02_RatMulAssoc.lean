import Game.Levels.RealArith.L01_RatMulComm

World "RealArith"
Level 2
Title "Products in ℚ are associative"

namespace MyRat

Introduction "
Three fractions, two ways to multiply them.
Every `frac_mul_frac` needs the proof that the denominator is not `0`.
For `b * d` that proof is `MyNat.mul_ne_zero b d hb hd`.
"

/-- $(xy)z = x(yz)$ for rationals. -/
Statement mul_assoc (x y z : ℚ) : x * y * z = x * (y * z) := by
  obtain ⟨a, b, hb, rfl⟩ := exists_frac x
  obtain ⟨c, d, hd, rfl⟩ := exists_frac y
  obtain ⟨e, f, hf, rfl⟩ := exists_frac z
  Hint "Left side: `rw [frac_mul_frac {hb} {hd}, frac_mul_frac (MyNat.mul_ne_zero b d {hb} {hd}) {hf}]`."
  Branch
    rw [mul_comm]
    Hint "Swapping does not help here. Multiply the fractions out with `frac_mul_frac`."
  rw [frac_mul_frac hb hd, frac_mul_frac (MyNat.mul_ne_zero b d hb hd) hf]
  Hint "Right side: `rw [frac_mul_frac {hd} {hf}, frac_mul_frac {hb} (MyNat.mul_ne_zero d f {hd} {hf})]`."
  rw [frac_mul_frac hd hf, frac_mul_frac hb (MyNat.mul_ne_zero d f hd hf)]
  Hint "Now `MyInt.mul_assoc` and `MyNat.mul_assoc`."
  rw [MyInt.mul_assoc, MyNat.mul_assoc]

Conclusion "
Again the work was done in `ℤ` and `ℕ`.
"

TheoremTab "ℚ"

-- `ac_rfl` may now use the laws the player proved for `*` on `ℚ`.
instance : Std.Associative (α := MyRat) (· * ·) := ⟨MyRat.mul_assoc⟩
instance : Std.Commutative (α := MyRat) (· * ·) := ⟨MyRat.mul_comm⟩

end MyRat
