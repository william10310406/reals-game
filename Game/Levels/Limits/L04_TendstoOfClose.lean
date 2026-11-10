import Game.Levels.Limits.L03_TendstoAdd

World "Limits"
Level 4
Title "Close sequences, same limit"

namespace MyRat

open MyNat (succ)

Introduction "
Changing a sequence to a close one does not change its limit.
"

/-- If $t$ is close to $s$ and $s \to L$, then $t \to L$. -/
Statement tendsto_of_close (s t : ℕ → ℚ) (L : ℚ) : Close t s → Tendsto s L → Tendsto t L := by
  intro h1 h2
  Branch
    intro k
    Hint "No need to unfold by hand: `rw [tendsto_iff_close] at {h2} ⊢`, then `close_trans`."
  rw [tendsto_iff_close] at h2 ⊢
  exact close_trans t s (const L) h1 h2

Conclusion "
So the limit belongs to the *real number*, not to one sequence.
"

TheoremTab "lim"

end MyRat
