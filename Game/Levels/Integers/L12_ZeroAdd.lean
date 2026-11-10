import Game.Levels.Integers.L11_LeRefl

World "Integers"
Level 12
Title "Zero on the left"

namespace MyInt

Introduction "
No pairs needed. Use theorems about `ℤ` you already have.
"

/-- $0 + x = x$ for integers. -/
Statement zero_add (x : ℤ) : 0 + x = x := by
  Hint "Swap the sum with `add_comm`, then use `add_zero`."
  rw [add_comm, add_zero]

Conclusion "
Short proofs come from good theorems.
"

TheoremTab "ℤ"

end MyInt
