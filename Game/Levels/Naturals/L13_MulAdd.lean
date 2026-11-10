import Game.Levels.Naturals.L12_MulComm

World "Naturals"
Level 13
Title "Distributivity"

namespace MyNat

Introduction "
Multiply out a bracket: `a * (b + c) = a * b + a * c`.
"

/-- $a (b + c) = ab + ac$. -/
Statement mul_add (a b c : ℕ) : a * (b + c) = a * b + a * c := by
  Hint "Induction on `c`."
  induction c with d hd
  · rw [add_zero, mul_zero, add_zero]
  · Hint "First `add_succ`, then `mul_succ` twice, then `{hd}`, then `add_assoc`."
    rw [add_succ, mul_succ, mul_succ, hd, add_assoc]

Conclusion "
This is the *distributive law*.
"

TheoremTab "*"

end MyNat
