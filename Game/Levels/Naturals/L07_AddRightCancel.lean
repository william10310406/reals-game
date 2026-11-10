import Game.Levels.Naturals.L06_AddAssoc

World "Naturals"
Level 7
Title "Cancelling"

namespace MyNat

Introduction "
One more rule about `succ`: `succ_inj a b : succ a = succ b → a = b`.

Use it to cancel a number on the right.

Tip: do the induction **before** `intro`. Then the induction hypothesis is an implication you can use.
"

/-- If $a + n = b + n$, then $a = b$. -/
Statement add_right_cancel (a b n : ℕ) : a + n = b + n → a = b := by
  Hint "Start with `induction n with d hd`, before `intro`."
  Branch
    intro h
    Hint "This works, but after `intro` the induction hypothesis is weaker. Better: induction first."
  induction n with d hd
  · intro h
    Hint "Remove the `+ 0` in `{h}`: `rw [add_zero, add_zero] at {h}`."
    rw [add_zero, add_zero] at h
    exact h
  · intro h
    Hint "Move the `succ` out in `{h}` with `add_succ`."
    rw [add_succ, add_succ] at h
    Hint "Now `{h} : succ (a + {d}) = succ (b + {d})`. Use `apply {hd}`."
    apply hd
    Hint "Use `apply succ_inj` and then `{h}`."
    apply succ_inj
    exact h

Conclusion "
You can now cancel on the right.
"

NewTheorem MyNat.succ_inj
TheoremTab "+"

end MyNat
