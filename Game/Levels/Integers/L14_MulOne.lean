import Game.Levels.Integers.L13_NatMulOne

World "Integers"
Level 14
Title "Times one in ℤ"

namespace MyInt

Introduction "
The integer `1` is `mk 1 0` (theorem `one_def`).
"

/-- $x \cdot 1 = x$ for integers. -/
Statement mul_one (x : ℤ) : x * 1 = x := by
  obtain ⟨a, b, rfl⟩ := exists_mk x
  Hint "Write `1` as a pair with `one_def`, then multiply with `mk_mul_mk`."
  rw [one_def, mk_mul_mk]
  Hint "Clean up in `ℕ`: `MyNat.mul_one` twice, `MyNat.mul_zero` twice, then `MyNat.add_zero` and `MyNat.zero_add`."
  rw [MyNat.mul_one, MyNat.mul_one, MyNat.mul_zero, MyNat.mul_zero, MyNat.add_zero, MyNat.zero_add]

Conclusion "
`1` is the neutral element of `*`.
"

NewTheorem MyInt.one_def
TheoremTab "ℤ"

end MyInt
