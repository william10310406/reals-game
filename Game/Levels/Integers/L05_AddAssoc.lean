import Game.Levels.Integers.L04_AddComm

World "Integers"
Level 5
Title "Brackets"

namespace MyInt

Introduction "
Same plan: write every integer as a pair, compute, compare.
"

/-- $(x + y) + z = x + (y + z)$ for integers. -/
Statement add_assoc (x y z : ℤ) : x + y + z = x + (y + z) := by
  obtain ⟨a, b, rfl⟩ := exists_mk x
  obtain ⟨c, d, rfl⟩ := exists_mk y
  obtain ⟨e, f, rfl⟩ := exists_mk z
  Hint "Use `mk_add_mk` four times."
  rw [mk_add_mk, mk_add_mk, mk_add_mk, mk_add_mk]
  Hint "Now `rw [mk_eq]` and finish with `ac_rfl`."
  rw [mk_eq]
  ac_rfl

Conclusion "
`mk_eq` followed by `ac_rfl` is a strong pair.
"

TheoremTab "ℤ"

end MyInt
