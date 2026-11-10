import Game.Levels.Naturals.L02_AddOne

World "Naturals"
Level 3
Title "Induction"

namespace MyNat

Introduction "
Is `0 + n = n`? Our rules only talk about `_ + 0` and `_ + succ _`.
So we need a new idea: **induction**.

To prove a statement for every `n`, prove two things:

1. it holds for `0`;
2. if it holds for `d`, it holds for `succ d`.

`induction n with d hd` gives you these two goals.
In the second one, `hd` is the statement for `d`.
"

/-- $0 + n = n$. -/
Statement zero_add (n : ℕ) : 0 + n = n := by
  Hint "Type `induction n with d hd`."
  induction n with d hd
  · Hint "The base case: `0 + 0 = 0`. Which rule removes `+ 0`?"
    rw [add_zero]
  · Hint "The step. You know `{hd} : 0 + {d} = {d}`. Use `add_succ` first, then `{hd}`."
    rw [add_succ]
    Hint (hidden := true) "Now `rw [{hd}]`."
    rw [hd]

Conclusion "
Induction is the main tool for natural numbers. You will use it a lot.
"

NewTactic induction
TheoremTab "+"

end MyNat
