import Game.Levels.Naturals.L01_AddZero

World "Naturals"
Level 2
Title "Adding one"

namespace MyNat

Introduction "
The second rule of addition is `add_succ : a + succ b = succ (a + b)`.

The number `1` is `succ 0`. The theorem `one_eq_succ_zero` says so.

Prove that adding one gives the next number.
"

/-- $a + 1 = \operatorname{succ}(a)$. -/
Statement add_one_eq_succ (a : ℕ) : a + 1 = succ a := by
  Hint "First turn `1` into `succ 0` with `rw [one_eq_succ_zero]`."
  rw [one_eq_succ_zero]
  Hint "Now use the second rule, `add_succ`."
  rw [add_succ]
  Hint (hidden := true) "Finally remove `+ 0`."
  rw [add_zero]

Conclusion "
This theorem is now in your inventory as `add_one_eq_succ`.
"

NewTheorem MyNat.one_eq_succ_zero MyNat.add_succ
NewDefinition MyNat.succ
TheoremTab "+"

end MyNat
