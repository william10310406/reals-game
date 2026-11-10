import Game.Levels.Completeness.L06_CauchyRatSeq

World "Completeness"
Level 7
Title "The chosen rationals are Cauchy (in ℚ)"

namespace MyReal

open MyNat (succ)

Introduction "
If `ratSeq q` is Cauchy in `ℝ`, then `q` is Cauchy in `ℚ`.
Ask for half of `eps K`, then bring the inequality back to `ℚ` with `le_of_ofRat_le`,
paying the other half.
"

/-- If $(q_n)$ is Cauchy in $\mathbb{R}$, then it is Cauchy in $\mathbb{Q}$. -/
Statement rat_cauchy (q : ℕ → ℚ) : IsCauchy (ratSeq q) → MyRat.IsCauchy q := by
  intro h K
  obtain ⟨N, hN⟩ := h (succ K + K)
  use N
  intro m n hm hn
  have b := hN m n hm hn
  rw [ratSeq_apply, ratSeq_apply] at b
  Hint "Remove the `abs`: `obtain ⟨b1, b2⟩ := abs_bounds (ofRat (q m) - ofRat (q n))` and
  `have c := le_trans _ _ _ b1 {b}`."
  obtain ⟨b1, b2⟩ := abs_bounds (ofRat (q m) - ofRat (q n))
  have c := le_trans _ _ _ b1 b
  Hint "Add `ofRat (q n)` on both sides and write the right side as one `ofRat`:
  `have d := add_le_add_right _ _ (ofRat (q n)) c`, then
  `rw [sub_eq_add_neg, add_assoc, add_comm (-ofRat (q n)), add_neg, add_zero, add_comm, eps_def,
  ← ofRat_add] at d`."
  have d := add_le_add_right _ _ (ofRat (q n)) c
  rw [sub_eq_add_neg, add_assoc, add_comm (-ofRat (q n)), add_neg, add_zero, add_comm, eps_def,
    ← ofRat_add] at d
  Hint "Back to `ℚ`, paying the other half: `have r := le_of_ofRat_le _ _ {d} (succ K + K)`."
  have r := le_of_ofRat_le _ _ d (succ K + K)
  Hint "Put the halves together:
  `rw [MyRat.add_assoc, ← MyNat.add_succ, MyRat.half (succ K) (MyNat.succ_ne_zero K)] at {r}`."
  rw [MyRat.add_assoc, ← MyNat.add_succ, MyRat.half (succ K) (MyNat.succ_ne_zero K)] at r
  Hint "Now subtract `q n`: `have r2 := MyRat.add_le_add_right _ _ (-q n) {r}`, and simplify."
  have r2 := MyRat.add_le_add_right _ _ (-q n) r
  rw [← MyRat.sub_eq_add_neg, MyRat.add_comm (q n), MyRat.add_assoc, MyRat.add_neg,
    MyRat.add_zero] at r2
  exact r2

Conclusion "
So the chosen rationals are a Cauchy sequence of rationals: a real number.
"

TheoremTab "limℝ"

end MyReal
