import Game.Levels.Integers.L12_ZeroAdd

World "Integers"
Level 13
Title "Times one in ℕ"

namespace MyNat

Introduction "
A small fact about `ℕ` that we skipped: `a * 1 = a`.
"

/-- $a \cdot 1 = a$ for natural numbers. -/
Statement mul_one (a : ℕ) : a * 1 = a := by
  Hint "Write `1` as `succ 0`, then use the rules of `*`."
  rw [one_eq_succ_zero]
  rw [mul_succ, mul_zero, zero_add]

Conclusion "
`MyNat.mul_one` is now in your inventory.
"

TheoremTab "*"

end MyNat
