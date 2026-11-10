import Game.Levels.Integers.L01_Pairs

World "Integers"
Level 2
Title "A reward"

namespace MyInt

Introduction "
You proved `add_comm`, `add_assoc`, `mul_comm` and `mul_assoc` for `ℕ`.
So you may now let Lean shuffle sums and products for you.

`ac_rfl` proves an equation when both sides only differ by order and brackets.
It does not multiply out brackets.
"

/-- $a + b + (c + d) = d + (b + a) + c$. -/
Statement (a b c d : ℕ) : a + b + (c + d) = d + (b + a) + c := by
  Hint "Type `ac_rfl`."
  Branch
    rw [MyNat.add_comm a b]
    Hint "You can reorder by hand, but `ac_rfl` does all of it at once."
  ac_rfl

Conclusion "
`ac_rfl` saves many `rw [add_comm]` steps. Use it when only order and brackets differ.
"

NewTactic ac_rfl

end MyInt
