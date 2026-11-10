import Game.Levels.Completeness.L07_RatCauchy

World "Completeness"
Level 8
Title "Near sequences have the same limit"

namespace MyReal

open MyNat (succ)

Introduction "
If `b → L` and `abs (a n - b n) ≤ eps n` for every `n`, then `a → L` too.
"

/-- If $b_n \to L$ and $|a_n - b_n| \le \frac{1}{n+1}$, then $a_n \to L$. -/
Statement tendsto_of_near (a b : ℕ → ℝ) (L : ℝ) :
    Tendsto b L → (∀ n, abs (a n - b n) ≤ eps n) → Tendsto a L := by
  intro hb h k
  obtain ⟨N, hN⟩ := hb (succ k + k)
  Hint "`n` must also be big for `eps n` to be small: `use N + (succ k + k)`."
  use N + (succ k + k)
  intro n hn
  have hn1 : N ≤ n := MyNat.le_trans _ _ _ (MyNat.le_add_right _ _) hn
  rw [MyNat.add_comm] at hn
  have hn2 := MyNat.le_trans _ _ _ (MyNat.le_add_right _ _) hn
  have t := abs_sub_le (a n) (b n) L
  have b1 := le_trans _ _ _ (h n) (eps_le _ _ hn2)
  Hint "`rw [← eps_half k]`, then `le_trans` with `t` and `add_le_add`."
  rw [← eps_half k]
  exact le_trans _ _ _ t (add_le_add _ _ _ _ b1 (hN n hn1))

Conclusion "
All pieces are ready.
"

TheoremTab "limℝ"

end MyReal
