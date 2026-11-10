import Game.Levels.Integers.L14_MulOne

World "Integers"
Level 15
Title "Zero times anything"

namespace MyInt

Introduction "
Note: `rw [h]` rewrites **every** copy of the pattern it found. Watch how many copies go at once.
"

/-- $0 \cdot x = 0$ for integers. -/
Statement zero_mul (x : ℤ) : 0 * x = 0 := by
  obtain ⟨a, b, rfl⟩ := exists_mk x
  Hint "`rw [zero_def]` changes both `0`s."
  rw [zero_def, mk_mul_mk]
  Hint "Use `MyNat.zero_mul`. Each use removes all copies of one product."
  rw [MyNat.zero_mul, MyNat.zero_mul, MyNat.add_zero]

Conclusion "
`rw` rewrites all copies of the first match. That is why two `MyNat.zero_mul` were enough.
"

TheoremTab "ℤ"

end MyInt
