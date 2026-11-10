import Game.Levels.Integers.L05_AddAssoc

World "Integers"
Level 6
Title "Adding zero"

namespace MyInt

Introduction "
Show that `0` changes nothing.
"

/-- $x + 0 = x$ for integers. -/
Statement add_zero (x : ℤ) : x + 0 = x := by
  obtain ⟨a, b, rfl⟩ := exists_mk x
  Hint "Write `0` as `mk 0 0`."
  Branch
    rw [add_comm]
    Hint "Swapping does not help: `0` is still not a pair. Write it as `mk 0 0` with `rw [zero_def]`."
  rw [zero_def]
  rw [mk_add_mk]
  Hint "Remove the two `+ 0` with `MyNat.add_zero`."
  rw [MyNat.add_zero, MyNat.add_zero]

Conclusion "
`0` is the neutral element of `+` on `ℤ`.
"

TheoremTab "ℤ"

end MyInt
