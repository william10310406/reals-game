import Game.Levels.RealArith.L03_RatMulOne

World "RealArith"
Level 4
Title "Distributivity in ℚ"

namespace MyRat

open MyInt (mk)

Introduction "
Boss level for `ℚ`: `x * (y + z) = x * y + x * z`.

After multiplying out, you compare two fractions with `frac_eq` (cross-multiplication).
Then it is a computation in `ℤ`. Remember:

* `MyInt.mk_mul_mk_zero b d : mk (b * d) 0 = mk b 0 * mk d 0`
* `MyInt.mul_add : x * (y + z) = x * y + x * z` (there is no `add_mul`; turn the product around
  with `MyInt.mul_comm` first)
* `ac_rfl` reorders sums and products.
"

/-- $x(y + z) = xy + xz$ for rationals. -/
Statement mul_add (x y z : ℚ) : x * (y + z) = x * y + x * z := by
  obtain ⟨a, b, hb, rfl⟩ := exists_frac x
  obtain ⟨c, d, hd, rfl⟩ := exists_frac y
  obtain ⟨e, f, hf, rfl⟩ := exists_frac z
  Hint "Left side: `rw [frac_add_frac {hd} {hf}, frac_mul_frac {hb} (MyNat.mul_ne_zero d f {hd} {hf})]`."
  rw [frac_add_frac hd hf, frac_mul_frac hb (MyNat.mul_ne_zero d f hd hf)]
  Hint "Right side: `rw [frac_mul_frac {hb} {hd}, frac_mul_frac {hb} {hf}]`, then add with
  `frac_add_frac (MyNat.mul_ne_zero b d {hb} {hd}) (MyNat.mul_ne_zero b f {hb} {hf})`."
  rw [frac_mul_frac hb hd, frac_mul_frac hb hf]
  rw [frac_add_frac (MyNat.mul_ne_zero b d hb hd) (MyNat.mul_ne_zero b f hb hf)]
  Hint "Cross-multiply with `frac_eq`. It needs both denominators:
  `rw [frac_eq (MyNat.mul_ne_zero b (d * f) {hb} (MyNat.mul_ne_zero d f {hd} {hf}))
    (MyNat.mul_ne_zero (b * d) (b * f) (MyNat.mul_ne_zero b d {hb} {hd}) (MyNat.mul_ne_zero b f {hb} {hf}))]`."
  Branch
    rw [MyInt.mul_add]
    Hint "First compare the two fractions with `frac_eq`. Then compute in `ℤ`."
  rw [frac_eq (MyNat.mul_ne_zero b (d * f) hb (MyNat.mul_ne_zero d f hd hf))
    (MyNat.mul_ne_zero (b * d) (b * f) (MyNat.mul_ne_zero b d hb hd) (MyNat.mul_ne_zero b f hb hf))]
  Hint "Split every `mk (… * …) 0` into a product: use `MyInt.mk_mul_mk_zero` until none is left
  (`rw [MyInt.mk_mul_mk_zero, MyInt.mk_mul_mk_zero, …]`)."
  rw [MyInt.mk_mul_mk_zero, MyInt.mk_mul_mk_zero, MyInt.mk_mul_mk_zero, MyInt.mk_mul_mk_zero,
    MyInt.mk_mul_mk_zero]
  Hint "Multiply out the bracket `a * (…)` with `MyInt.mul_add`.
  Then turn the two brackets `(…) * (…)` around with `MyInt.mul_comm` and use `MyInt.mul_add` again."
  rw [MyInt.mul_add]
  rw [MyInt.mul_comm (a * (c * mk f 0) + a * (e * mk d 0)), MyInt.mul_add]
  rw [MyInt.mul_comm (a * c * (mk b 0 * mk f 0) + a * e * (mk b 0 * mk d 0)), MyInt.mul_add]
  Hint "Both sides have the same terms. `ac_rfl`."
  ac_rfl

Conclusion "
`ℚ` now has all the ring rules we need: `+` and `*` are commutative and associative,
`0` and `1` are neutral, `-x` cancels `x`, and `*` distributes over `+`.
"

TheoremTab "ℚ"

end MyRat
