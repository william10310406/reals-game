import Game.Levels.RealLimits.L04_TendstoConst

World "RealLimits"
Level 5
Title "Limit of a sum"

namespace MyReal

open MyNat (succ)

Introduction "
If `a → L` and `b → M`, then `a + b → L + M`.
`addSeq a b` is the sequence `a 0 + b 0, a 1 + b 1, …` (`addSeq_apply`).

The textbook proof: ask both for `ε/2`, use the triangle inequality.
"

/-- If $a_n \to L$ and $b_n \to M$, then $a_n + b_n \to L + M$. -/
Statement tendsto_add (a b : ℕ → ℝ) (L M : ℝ) :
    Tendsto a L → Tendsto b M → Tendsto (addSeq a b) (L + M) := by
  intro ha hb k
  Hint "Ask for half: `obtain ⟨N1, h1⟩ := {ha} (succ k + k)`, and the same with `{hb}`."
  Branch
    obtain ⟨N1, h1⟩ := ha k
    Hint "With `k` the two errors add up to `2/(k+1)`. Ask for half: `{ha} (succ k + k)`."
  obtain ⟨N1, h1⟩ := ha (succ k + k)
  obtain ⟨N2, h2⟩ := hb (succ k + k)
  use N1 + N2
  intro n hn
  have hn1 : N1 ≤ n := MyNat.le_trans N1 (N1 + N2) n (MyNat.le_add_right N1 N2) hn
  rw [MyNat.add_comm] at hn
  have hn2 : N2 ≤ n := MyNat.le_trans N2 (N2 + N1) n (MyNat.le_add_right N2 N1) hn
  rw [addSeq_apply]
  Hint "Regroup: `have e : a n + b n - (L + M) = a n - L + (b n - M) := by …`
  (`sub_eq_add_neg` three times, `neg_add`, `ac_rfl`)."
  have e : a n + b n - (L + M) = a n - L + (b n - M) := by
    rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg, neg_add]
    ac_rfl
  Hint "`rw [{e}, ← eps_half k]`. Then the triangle inequality `abs_add`, `le_trans` and `add_le_add`."
  rw [e, ← eps_half k]
  exact le_trans _ _ _ (abs_add _ _) (add_le_add _ _ _ _ (h1 n hn1) (h2 n hn2))

Conclusion "
The limit of a sum is the sum of the limits.
"

NewTheorem MyReal.addSeq_apply
NewDefinition MyReal.addSeq
TheoremTab "limℝ"

end MyReal
