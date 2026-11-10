import Game.Levels.Rationals.L07_NegAdd

World "Rationals"
Level 8
Title "Brackets"

namespace MyRat

open MyInt (mk)

Introduction "
The longest computation of this world. Plan:

1. three fractions;
2. `frac_add_frac` four times;
3. make the denominators equal with `MyNat.mul_assoc`;
4. split `mk (b * d) 0` and `mk (d * f) 0`;
5. multiply out, then `ac_rfl`.
"

/-- $(x + y) + z = x + (y + z)$ for rationals. -/
Statement add_assoc (x y z : ℚ) : x + y + z = x + (y + z) := by
  obtain ⟨a, b, hb, rfl⟩ := exists_frac x
  obtain ⟨c, d, hd, rfl⟩ := exists_frac y
  obtain ⟨e, f, hf, rfl⟩ := exists_frac z
  Hint "Left side first: `rw [frac_add_frac {hb} {hd}, frac_add_frac (MyNat.mul_ne_zero b d {hb} {hd}) {hf}]`."
  Branch
    rw [add_comm]
    Hint "Swapping does not help. Add the fractions with `frac_add_frac`."
  rw [frac_add_frac hb hd, frac_add_frac (MyNat.mul_ne_zero b d hb hd) hf]
  Hint "Now the right side: `rw [frac_add_frac {hd} {hf}, frac_add_frac {hb} (MyNat.mul_ne_zero d f {hd} {hf})]`."
  rw [frac_add_frac hd hf, frac_add_frac hb (MyNat.mul_ne_zero d f hd hf)]
  Hint "Denominators: `MyNat.mul_assoc`. Then split with `MyInt.mk_mul_mk_zero` twice."
  rw [MyNat.mul_assoc, MyInt.mk_mul_mk_zero, MyInt.mk_mul_mk_zero]
  Hint "Two brackets are left, `(…) * mk f 0` and `(…) * mk b 0`.
  Turn each around with `MyInt.mul_comm` and multiply out with `MyInt.mul_add`."
  rw [MyInt.mul_comm (a * mk d 0 + c * mk b 0), MyInt.mul_add]
  rw [MyInt.mul_comm (c * mk f 0 + e * mk d 0), MyInt.mul_add]
  ac_rfl

Conclusion "
From now on `ac_rfl` also works for `+` on `ℚ`.
"

TheoremTab "ℚ"

-- `ac_rfl` may now use the laws the player proved for `+` on `ℚ`.
instance : Std.Associative (α := MyRat) (· + ·) := ⟨MyRat.add_assoc⟩
instance : Std.Commutative (α := MyRat) (· + ·) := ⟨MyRat.add_comm⟩

end MyRat
