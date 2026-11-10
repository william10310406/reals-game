import Game.Levels.Naturals.L07_AddRightCancel

World "Naturals"
Level 8
Title "Cancelling on the left"

namespace MyNat

Introduction "
No induction needed: turn the sums around with `add_comm` and use the last level.

`rw [add_comm n a] at h` swaps exactly `n + a` in `h`.
"

/-- If $n + a = n + b$, then $a = b$. -/
Statement add_left_cancel (a b n : ℕ) : n + a = n + b → a = b := by
  intro h
  Hint "Swap both sums in `{h}`: `rw [add_comm n a, add_comm n b] at {h}`."
  rw [add_comm n a, add_comm n b] at h
  Hint "Now use `add_right_cancel a b n {h}`."
  exact add_right_cancel a b n h

Conclusion "
A theorem is a function: `add_right_cancel a b n h` proves `a = b`.
"

TheoremTab "+"

end MyNat
