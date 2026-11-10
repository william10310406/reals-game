import Game.Levels.Completeness.L05_LeOfOfRatLe

World "Completeness"
Level 6
Title "The chosen rationals are Cauchy (in ℝ)"

namespace MyReal

open MyNat (succ)

Introduction "
`IsCauchy a` for a sequence of reals: for every `k` there is `N` with
`abs (a m - a n) ≤ eps k` for all `m, n ≥ N`.

Suppose `a` is Cauchy and `abs (a n - ofRat (q n)) ≤ eps n` for every `n`.
Then `ratSeq q` is Cauchy too:

`|q m - q n| ≤ |q m - a m| + |a m - a n| + |a n - q n|`.

Make `|a m - a n|` at most half of `eps K`, and the two other terms at most a quarter each
(for this, `m` and `n` must be at least `K2 = succ K1 + K1`, where `K1 = succ K + K`).
"

/-- If $a$ is Cauchy and $|a_n - q_n| \le \frac{1}{n+1}$, then $(q_n)$ is Cauchy in $\mathbb{R}$. -/
Statement cauchy_ratSeq (a : ℕ → ℝ) (q : ℕ → ℚ) :
    IsCauchy a → (∀ n, abs (a n - ofRat (q n)) ≤ eps n) → IsCauchy (ratSeq q) := by
  intro ha hq K
  Hint "Half for `a`: `obtain ⟨N, hN⟩ := {ha} (succ K + K)`."
  obtain ⟨N, hN⟩ := ha (succ K + K)
  Hint "Take `N` plus the quarter index: `use N + (succ (succ K + K) + (succ K + K))`."
  use N + (succ (succ K + K) + (succ K + K))
  intro m n hm hn
  rw [ratSeq_apply, ratSeq_apply]
  have hm1 : N ≤ m := MyNat.le_trans _ _ _ (MyNat.le_add_right _ _) hm
  have hn1 : N ≤ n := MyNat.le_trans _ _ _ (MyNat.le_add_right _ _) hn
  rw [MyNat.add_comm] at hm hn
  have hm2 := MyNat.le_trans _ _ _ (MyNat.le_add_right _ _) hm
  have hn2 := MyNat.le_trans _ _ _ (MyNat.le_add_right _ _) hn
  Hint "Two triangle inequalities:
  `have t1 := abs_sub_le (ofRat (q m)) (a m) (ofRat (q n))` and
  `have t2 := abs_sub_le (a m) (a n) (ofRat (q n))`."
  have t1 := abs_sub_le (ofRat (q m)) (a m) (ofRat (q n))
  have t2 := abs_sub_le (a m) (a n) (ofRat (q n))
  Hint "The three pieces. For `q m` near `a m`: `abs_sub_comm`, then `{hq} m` and `eps_le`."
  have b1 : abs (ofRat (q m) - a m) ≤ eps (succ (succ K + K) + (succ K + K)) := by
    rw [abs_sub_comm]
    exact le_trans _ _ _ (hq m) (eps_le _ _ hm2)
  have b2 := hN m n hm1 hn1
  have b3 : abs (a n - ofRat (q n)) ≤ eps (succ (succ K + K) + (succ K + K)) :=
    le_trans _ _ _ (hq n) (eps_le _ _ hn2)
  Hint "Add them up: `have s1 := add_le_add _ _ _ _ b2 b3` and
  `have s2 := add_le_add _ _ _ _ b1 (le_trans _ _ _ t2 s1)`."
  have s1 := add_le_add _ _ _ _ b2 b3
  have s2 := add_le_add _ _ _ _ b1 (le_trans _ _ _ t2 s1)
  Hint "A quarter, a half and a quarter make `eps K`. Show it with `have e : … := by`
  (`ac_rfl`, then `eps_half` twice)."
  have e : eps (succ (succ K + K) + (succ K + K)) +
      (eps (succ K + K) + eps (succ (succ K + K) + (succ K + K))) = eps K := by
    have e2 : eps (succ (succ K + K) + (succ K + K)) +
        (eps (succ K + K) + eps (succ (succ K + K) + (succ K + K)))
        = eps (succ K + K) + (eps (succ (succ K + K) + (succ K + K)) +
          eps (succ (succ K + K) + (succ K + K))) := by ac_rfl
    rw [e2, eps_half, eps_half]
  rw [e] at s2
  exact le_trans _ _ _ t1 s2

Conclusion "
The chosen rationals are a Cauchy sequence, in `ℝ`. Next: in `ℚ`.
"

NewDefinition MyReal.IsCauchy
TheoremTab "limℝ"

end MyReal
