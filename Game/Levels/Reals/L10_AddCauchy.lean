import Game.MyReal.Basic

World "Reals"
Level 10
Title "Adding Cauchy sequences"

namespace MyRat

open MyNat (succ)

Introduction "
Now we have the real numbers `ℝ`: Cauchy sequences, where close ones are the same.

To add two reals we add their sequences term by term: `addSeq s t n = s n + t n`
(theorem `addSeq_apply`). First we must check that the sum is again Cauchy.

Same idea as the last boss: ask for half, take `N₁ + N₂`.
"

/-- The sum of two Cauchy sequences is Cauchy. -/
Statement add_cauchy (s t : ℕ → ℚ) : IsCauchy s → IsCauchy t → IsCauchy (addSeq s t) := by
  intro hs ht k
  Branch
    obtain ⟨N1, h1⟩ := hs k
    Hint "With `k` the two errors add up to `2/(k+1)`: too much. Ask for half: `{hs} (succ k + k)`."
  obtain ⟨N1, h1⟩ := hs (succ k + k)
  obtain ⟨N2, h2⟩ := ht (succ k + k)
  use N1 + N2
  intro m n hm hn
  Hint "You need `N1 ≤ m`, `N1 ≤ n`, `N2 ≤ m`, `N2 ≤ n`. Use `MyNat.le_trans` and `MyNat.le_add_right`, as in the last boss."
  have hm1 : N1 ≤ m := MyNat.le_trans N1 (N1 + N2) m (MyNat.le_add_right N1 N2) hm
  have hn1 : N1 ≤ n := MyNat.le_trans N1 (N1 + N2) n (MyNat.le_add_right N1 N2) hn
  rw [MyNat.add_comm] at hm hn
  have hm2 : N2 ≤ m := MyNat.le_trans N2 (N2 + N1) m (MyNat.le_add_right N2 N1) hm
  have hn2 : N2 ≤ n := MyNat.le_trans N2 (N2 + N1) n (MyNat.le_add_right N2 N1) hn
  Hint "Compute the terms with `addSeq_apply`, then split `1/(k+1)` into halves."
  rw [addSeq_apply, addSeq_apply, ← half (succ k) (MyNat.succ_ne_zero k), MyNat.add_succ]
  Hint "Regroup the difference:
  `have e : s m + t m - (s n + t n) = s m - s n + (t m - t n) := by` …
  (inside: `sub_eq_add_neg` three times, `neg_add`, `ac_rfl`)."
  have e : s m + t m - (s n + t n) = s m - s n + (t m - t n) := by
    rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg, neg_add]
    ac_rfl
  rw [e]
  exact add_le_add _ _ _ _ (h1 m n hm1 hn1) (h2 m n hm2 hn2)

Conclusion "
Sums of Cauchy sequences are Cauchy.
"

NewTheorem MyRat.addSeq_apply
NewDefinition MyRat.addSeq
TheoremTab "ℚ"

end MyRat
