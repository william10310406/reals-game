import Game.Levels.Integers.L03_Zero

World "Integers"
Level 4
Title "Adding integers"

namespace MyInt

Introduction "
Addition adds the pairs: `mk_add_mk : mk a b + mk c d = mk (a + c) (b + d)`.

To prove something for **every** integer `x`, write `x` as a pair first:
`obtain ⟨a, b, rfl⟩ := exists_mk x` replaces `x` by `mk a b`.
"

/-- $x + y = y + x$ for integers. -/
Statement add_comm (x y : ℤ) : x + y = y + x := by
  Hint "Write `x` as a pair: `obtain ⟨a, b, rfl⟩ := exists_mk x`."
  obtain ⟨a, b, rfl⟩ := exists_mk x
  Hint "Now `y`: `obtain ⟨c, d, rfl⟩ := exists_mk y`."
  obtain ⟨c, d, rfl⟩ := exists_mk y
  Hint "Add the pairs on both sides: `rw [mk_add_mk, mk_add_mk]`."
  Branch
    rw [mk_add_mk]
    Hint "That computed only the left side. The right side needs `mk_add_mk` too."
  rw [mk_add_mk, mk_add_mk]
  Hint "Swap the sums in `ℕ` with `MyNat.add_comm`."
  rw [MyNat.add_comm a c, MyNat.add_comm b d]

Conclusion "
Integer addition is commutative because natural addition is.
"

NewTheorem MyInt.exists_mk MyInt.mk_add_mk
TheoremTab "ℤ"

end MyInt
