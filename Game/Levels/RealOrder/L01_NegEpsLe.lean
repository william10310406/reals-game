import Game.MyReal.Nonneg

World "RealOrder"
Level 1
Title "Below zero"

namespace MyRat

open MyNat (succ)

Introduction "
In this world `ℝ` gets its order `≤`.
For rationals, `x ≤ y` means `nonneg (y - x)`. We do the same for reals.

A real `x = ofSeq s hs` is `≥ 0` when its terms are, in the end, above every negative bound:

`nonneg_ofSeq : nonneg (ofSeq s hs) ↔ ∀ k, ∃ N, ∀ n, N ≤ n → -frac 1 (succ k) ≤ s n`

So `-frac 1 (succ k)` will show up a lot. First a small fact about it in `ℚ`.
"

/-- $-\frac{1}{k+1} \le 0$. -/
Statement neg_eps_le (k : ℕ) : -frac 1 (succ k) ≤ 0 := by
  Hint "Write `0` as `-0`: `rw [← neg_zero]`. Then use `neg_le_neg` and `eps_nonneg k`."
  Branch
    rw [le_iff_nonneg]
    Hint "That works, but it is long. Shorter: `rw [← neg_zero]`, then
    `exact neg_le_neg 0 (frac 1 (succ k)) (eps_nonneg k)`."
  rw [← neg_zero]
  exact neg_le_neg 0 (frac 1 (succ k)) (eps_nonneg k)

Conclusion "
`neg_eps_le k` is in your inventory.
"

TheoremTab "ℚ"

end MyRat
