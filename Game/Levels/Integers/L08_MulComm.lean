import Game.Levels.Integers.L07_AddNeg

World "Integers"
Level 8
Title "Multiplying integers"

namespace MyInt

Introduction "
Multiplication follows `(a - b)(c - d) = (ac + bd) - (ad + bc)`:

`mk_mul_mk : mk a b * mk c d = mk (a * c + b * d) (a * d + b * c)`.
"

/-- $xy = yx$ for integers. -/
Statement mul_comm (x y : ℤ) : x * y = y * x := by
  obtain ⟨a, b, rfl⟩ := exists_mk x
  obtain ⟨c, d, rfl⟩ := exists_mk y
  Hint "Multiply both sides out with `mk_mul_mk`."
  Branch
    rw [mk_mul_mk]
    Hint "Only the left side was multiplied out. Use `mk_mul_mk` again for the right side."
  rw [mk_mul_mk, mk_mul_mk]
  Hint "Then `rw [mk_eq]` and `ac_rfl`."
  rw [mk_eq]
  ac_rfl

Conclusion "
Integer multiplication is commutative.
"

NewTheorem MyInt.mk_mul_mk
TheoremTab "ℤ"

end MyInt
