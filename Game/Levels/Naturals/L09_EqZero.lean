import Game.Levels.Naturals.L08_AddLeftCancel

World "Naturals"
Level 9
Title "Zero is not a successor"

namespace MyNat

Introduction "
The last rule about `succ`: `zero_ne_succ a : 0 ≠ succ a`.
`x ≠ y` means `x = y → False`.

Sometimes induction is too much. `cases b with d` only splits `b` into `0` and `succ d`.
"

/-- If $a + b = 0$, then $b = 0$. -/
Statement eq_zero_of_add_eq_zero (a b : ℕ) : a + b = 0 → b = 0 := by
  Hint "Split `b` into its two cases: `cases b with d`."
  cases b with d
  · intro h
    Hint "The goal is `0 = 0`."
    rfl
  · intro h
    Hint "`{h}` says `a + succ {d} = 0`. That is impossible. Use `add_succ` at `{h}`."
    rw [add_succ] at h
    Hint "Now `{h} : succ (a + {d}) = 0`. Use `exfalso`: the goal becomes `False`."
    exfalso
    Hint "Use `apply zero_ne_succ (a + {d})`."
    apply zero_ne_succ (a + d)
    Hint (hidden := true) "The goal is `0 = succ (a + {d})`. Rewrite with `{h}`."
    rw [h]

Conclusion "
Zero is not the next number of anything. This is why sums of naturals can only be `0` if each part is.
"

NewTactic cases
NewTheorem MyNat.zero_ne_succ
TheoremTab "+"

end MyNat
