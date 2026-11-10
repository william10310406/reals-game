import Game.Levels.Integers.L06_AddZero

World "Integers"
Level 7
Title "Negatives"

namespace MyInt

Introduction "
Negation swaps the pair: `neg_mk : -mk a b = mk b a`.

This is new: in `ℕ` you could not undo `+`. In `ℤ` you can.
"

/-- $x + (-x) = 0$. -/
Statement add_neg (x : ℤ) : x + -x = 0 := by
  obtain ⟨a, b, rfl⟩ := exists_mk x
  Hint "Compute `-mk a b` with `neg_mk`."
  rw [neg_mk]
  rw [mk_add_mk]
  Hint "Write `0` as a pair and use `mk_eq`."
  rw [zero_def, mk_eq]
  Hint (hidden := true) "`MyNat.add_zero`, `MyNat.zero_add`, then `MyNat.add_comm`."
  rw [MyNat.add_zero, MyNat.zero_add, MyNat.add_comm]

Conclusion "
Every integer has a negative. That is why we built `ℤ`.
"

NewTheorem MyInt.neg_mk
TheoremTab "ℤ"

end MyInt
