import Game.Levels.Reals.L10_AddCauchy

World "Reals"
Level 11
Title "Addition is well defined"

namespace MyRat

open MyNat (succ)

Introduction "
A real number has many sequences. If we change `s` to a close `s'`, and `t` to a close `t'`,
the sum must stay the same real. That is: the sums are close.
"

/-- If $s \approx s'$ and $t \approx t'$, then $s + t \approx s' + t'$. -/
Statement close_add (s s' t t' : ℕ → ℚ) :
    Close s s' → Close t t' → Close (addSeq s t) (addSeq s' t') := by
  intro hs ht k
  Branch
    obtain ⟨N1, h1⟩ := hs k
    Hint "With `k` the two errors add up to `2/(k+1)`: too much. Ask for half: `{hs} (succ k + k)`."
  obtain ⟨N1, h1⟩ := hs (succ k + k)
  obtain ⟨N2, h2⟩ := ht (succ k + k)
  use N1 + N2
  intro n hn
  have hn1 : N1 ≤ n := MyNat.le_trans N1 (N1 + N2) n (MyNat.le_add_right N1 N2) hn
  rw [MyNat.add_comm] at hn
  have hn2 : N2 ≤ n := MyNat.le_trans N2 (N2 + N1) n (MyNat.le_add_right N2 N1) hn
  obtain ⟨a1, a2⟩ := h1 n hn1
  obtain ⟨b1, b2⟩ := h2 n hn2
  rw [addSeq_apply, addSeq_apply, ← half (succ k) (MyNat.succ_ne_zero k), MyNat.add_succ]
  constructor
  · Hint "Regroup with `have`, as in the last level."
    have e : s n + t n - (s' n + t' n) = s n - s' n + (t n - t' n) := by
      rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg, neg_add]
      ac_rfl
    rw [e]
    exact add_le_add _ _ _ _ a1 b1
  · have e : s' n + t' n - (s n + t n) = s' n - s n + (t' n - t n) := by
      rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg, neg_add]
      ac_rfl
    rw [e]
    exact add_le_add _ _ _ _ a2 b2

Conclusion "
Now `x + y` for reals does not depend on which sequences we pick.
"

TheoremTab "ℚ"

end MyRat
