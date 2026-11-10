import Game.Levels.Integers.L02_AcRfl

World "Integers"
Level 3
Title "Zero"

namespace MyInt

Introduction "
The integer `0` is `mk 0 0`. The theorem `zero_def` says so.

Show that `a - a` is zero.
"

/-- $a - a = 0$. -/
Statement mk_self (a : ℕ) : mk a a = 0 := by
  Hint "Write `0` as a pair: `rw [zero_def]`."
  rw [zero_def]
  rw [mk_eq]
  Hint "Now `a + 0 = 0 + a` in `ℕ`. Use `MyNat.add_zero` and `MyNat.zero_add`, or `ac_rfl`."
  Branch
    rw [MyNat.zero_add]
    Hint "Good. One `+ 0` is left: `MyNat.add_zero`."
  rw [MyNat.add_zero, MyNat.zero_add]

Conclusion "
`mk_self` is in your inventory now.
"

NewTheorem MyInt.zero_def
TheoremTab "ℤ"

end MyInt
