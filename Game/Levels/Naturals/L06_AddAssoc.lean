import Game.Levels.Naturals.L05_AddComm

World "Naturals"
Level 6
Title "Brackets"

namespace MyNat

Introduction "
`a + b + c` means `(a + b) + c`. Show that the brackets do not matter.
"

/-- $(a + b) + c = a + (b + c)$. -/
Statement add_assoc (a b c : ℕ) : a + b + c = a + (b + c) := by
  Hint "Induction on `c`."
  induction c with d hd
  · rw [add_zero, add_zero]
  · Hint "Use `add_succ` until every `succ` is outside. Then use `{hd}`."
    rw [add_succ, add_succ, add_succ, hd]

Conclusion "
With `add_comm` and `add_assoc` you can reorder any sum.
"

TheoremTab "+"

end MyNat
