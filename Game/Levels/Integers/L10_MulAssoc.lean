import Game.Levels.Integers.L09_MulAdd

World "Integers"
Level 10
Title "Brackets for products"

namespace MyInt

Introduction "
A long one. The plan is the same:

1. write `x`, `y`, `z` as pairs;
2. compute with `mk_mul_mk`;
3. `mk_eq`;
4. multiply out with `MyNat.add_mul` and `MyNat.mul_add`;
5. `ac_rfl`.
"

/-- $(xy)z = x(yz)$ for integers. -/
Statement mul_assoc (x y z : ℤ) : x * y * z = x * (y * z) := by
  obtain ⟨a, b, rfl⟩ := exists_mk x
  obtain ⟨c, d, rfl⟩ := exists_mk y
  obtain ⟨e, f, rfl⟩ := exists_mk z
  Hint "Use `mk_mul_mk` four times."
  Branch
    rw [mul_comm]
    Hint "Swapping does not help here. Multiply out with `mk_mul_mk`."
  rw [mk_mul_mk, mk_mul_mk, mk_mul_mk, mk_mul_mk]
  rw [mk_eq]
  Hint "Four brackets like `(a * c + b * d) * e` need `MyNat.add_mul`,
  and four like `a * (c * e + d * f)` need `MyNat.mul_add`."
  rw [MyNat.add_mul, MyNat.add_mul, MyNat.add_mul, MyNat.add_mul]
  rw [MyNat.mul_add, MyNat.mul_add, MyNat.mul_add, MyNat.mul_add]
  ac_rfl

Conclusion "
`ℤ` now has all the ring rules you need.
"

TheoremTab "ℤ"

end MyInt
