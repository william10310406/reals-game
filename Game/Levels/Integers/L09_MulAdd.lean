import Game.Levels.Integers.L08_MulComm

World "Integers"
Level 9
Title "Distributivity"

namespace MyInt

Introduction "
`ac_rfl` cannot multiply out brackets. You have to do that with `MyNat.mul_add`.
"

/-- $x(y + z) = xy + xz$ for integers. -/
Statement mul_add (x y z : ℤ) : x * (y + z) = x * y + x * z := by
  obtain ⟨a, b, rfl⟩ := exists_mk x
  obtain ⟨c, d, rfl⟩ := exists_mk y
  obtain ⟨e, f, rfl⟩ := exists_mk z
  Hint "Compute everything: `mk_add_mk`, then `mk_mul_mk` three times, then `mk_add_mk`."
  Branch
    rw [mk_mul_mk]
    Hint "Compute the sum `mk c d + mk e f` first with `mk_add_mk`, so that the left side is one product of pairs."
  rw [mk_add_mk, mk_mul_mk, mk_mul_mk, mk_mul_mk, mk_add_mk]
  rw [mk_eq]
  Hint "Four brackets of the form `a * (c + e)` are left. Use `MyNat.mul_add` four times, then `ac_rfl`."
  rw [MyNat.mul_add, MyNat.mul_add, MyNat.mul_add, MyNat.mul_add]
  ac_rfl

Conclusion "
Distributivity for `ℤ` comes from distributivity for `ℕ`.
"

TheoremTab "ℤ"

end MyInt
