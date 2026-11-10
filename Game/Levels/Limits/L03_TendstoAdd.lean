import Game.Levels.Limits.L02_CloseConstAdd

World "Limits"
Level 3
Title "Limit of a sum"

namespace MyRat

open MyNat (succ)

Introduction "
If `s → a` and `t → b`, then `s + t → a + b`.
You already did the hard work in the Reals world (`close_add`, `close_trans`).
"

/-- If $s \to a$ and $t \to b$, then $s + t \to a + b$. -/
Statement tendsto_add (s t : ℕ → ℚ) (a b : ℚ) :
    Tendsto s a → Tendsto t b → Tendsto (addSeq s t) (a + b) := by
  intro hs ht
  rw [tendsto_iff_close] at hs ht ⊢
  Hint "Chain two facts with `close_trans`:
  `close_add s (const a) t (const b) {hs} {ht}` and `close_const_add a b`."
  exact close_trans _ _ _ (close_add s (const a) t (const b) hs ht) (close_const_add a b)

Conclusion "
The limit of a sum is the sum of the limits.
"

TheoremTab "lim"

end MyRat
