import Game.Levels.Naturals.L03_ZeroAdd

World "Naturals"
Level 4
Title "succ on the left"

namespace MyNat

Introduction "
`add_succ` moves a `succ` out of the right summand.
Now show the same for the left summand.
"

/-- $\operatorname{succ}(a) + b = \operatorname{succ}(a + b)$. -/
Statement succ_add (a b : ℕ) : succ a + b = succ (a + b) := by
  Hint "Do induction on `b`."
  induction b with d hd
  · Hint "There are two `+ 0` to remove."
    rw [add_zero, add_zero]
  · Hint "Use `add_succ` twice, then `{hd}`."
    rw [add_succ, add_succ, hd]

Conclusion "
Now you know how `succ` moves out of both sides of a sum.
"

TheoremTab "+"

end MyNat
