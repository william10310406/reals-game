import Game.Levels.RealLimits.L08_TendstoUnique

World "RealLimits"
Level 9
Title "Squeeze theorem"

namespace MyReal

Introduction "
Boss level. **Squeeze theorem**: if `a n ≤ b n ≤ c n` for all `n`, and `a → L` and `c → L`,
then `b → L`.

Use `abs_le`: show `b n - L ≤ eps k` (since `b n ≤ c n`) and `-(b n - L) ≤ eps k`
(since `a n ≤ b n`).
"

/-- If $a_n \le b_n \le c_n$, $a_n \to L$ and $c_n \to L$, then $b_n \to L$. -/
Statement squeeze (a b c : ℕ → ℝ) (L : ℝ) :
    (∀ n, a n ≤ b n) → (∀ n, b n ≤ c n) → Tendsto a L → Tendsto c L → Tendsto b L := by
  intro hab hbc ha hc k
  obtain ⟨N1, h1⟩ := ha k
  obtain ⟨N2, h2⟩ := hc k
  use N1 + N2
  intro n hn
  have hn1 : N1 ≤ n := MyNat.le_trans N1 (N1 + N2) n (MyNat.le_add_right N1 N2) hn
  rw [MyNat.add_comm] at hn
  have hn2 : N2 ≤ n := MyNat.le_trans N2 (N2 + N1) n (MyNat.le_add_right N2 N1) hn
  Hint "`apply abs_le`."
  Branch
    obtain ⟨c1, c2⟩ := abs_bounds (b n - L)
    Hint "These bounds go the wrong way: they bound `b n - L` by `abs (b n - L)`, not by `eps k`.
    Use `apply abs_le` instead."
  apply abs_le
  · Hint "Upper bound through `c n - L`. First `have e := add_le_add_right _ _ (-L) (hbc n)` and
    `rw [← sub_eq_add_neg, ← sub_eq_add_neg] at e`."
    obtain ⟨c1, c2⟩ := abs_bounds (c n - L)
    have e := add_le_add_right _ _ (-L) (hbc n)
    rw [← sub_eq_add_neg, ← sub_eq_add_neg] at e
    exact le_trans _ _ _ e (le_trans _ _ _ c1 (h2 n hn2))
  · Hint "Lower bound through `a n - L`. `rw [neg_sub]` makes the goal `L - b n ≤ eps k`."
    obtain ⟨a1, a2⟩ := abs_bounds (a n - L)
    rw [neg_sub] at a2 ⊢
    Hint "From `hab n`: `have e := add_le_add_right _ _ L (neg_le_neg _ _ (hab n))`,
    then `rw [add_comm (-b n), add_comm (-a n), ← sub_eq_add_neg, ← sub_eq_add_neg] at e`."
    have e := add_le_add_right _ _ L (neg_le_neg _ _ (hab n))
    rw [add_comm (-b n), add_comm (-a n), ← sub_eq_add_neg, ← sub_eq_add_neg] at e
    exact le_trans _ _ _ e (le_trans _ _ _ a2 (h1 n hn1))

Conclusion "
The squeeze theorem, for sequences of reals.
"

TheoremTab "limℝ"

end MyReal
