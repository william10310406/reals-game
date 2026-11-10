import Game.Levels.Naturals.L04_SuccAdd

World "Naturals"
Level 5
Title "Addition is commutative"

namespace MyNat

Introduction "
Is `a + b = b + a`? Use induction on `b`, and the theorems you proved.
"

/-- $a + b = b + a$. -/
Statement add_comm (a b : ℕ) : a + b = b + a := by
  Hint (hidden := true) "Start with `induction b with d hd`."
  Branch
    induction a with d hd
    Hint "Induction on `a` also works. You need `zero_add` and `add_zero` here."
  induction b with d hd
  · Hint "`a + 0 = 0 + a`. You have a theorem for each side."
    rw [add_zero, zero_add]
  · Hint "Move the `succ` out on both sides: `add_succ` and `succ_add`. Then use `{hd}`."
    rw [add_succ, succ_add, hd]

Conclusion "
`add_comm a b` is now yours. Write `rw [add_comm a b]` to swap exactly `a + b`.
"

TheoremTab "+"

end MyNat
