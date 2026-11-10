import Game.Levels.RealOrder.L21_LeOfEventually

World "RealOrder"
Level 22
Title "Absolute value in ℝ"

namespace MyReal

open MyNat (succ)

Introduction "
The absolute value of a real takes `abs` term by term:

* `ofSeq_abs : abs (ofSeq s hs) = ofSeq (MyRat.absSeq s) _`
* `MyRat.absSeq_apply s n : MyRat.absSeq s n = MyRat.abs (s n)`

Show: if `x ≥ 0`, then `abs x = x`. Careful: the terms of `x` may be a little negative.
"

/-- If $x \ge 0$, then $|x| = x$. -/
Statement abs_of_nonneg (x : ℝ) : nonneg x → abs x = x := by
  obtain ⟨s, hs, rfl⟩ := exists_ofSeq x
  intro h
  rw [nonneg_ofSeq] at h
  rw [ofSeq_abs, ofSeq_eq]
  intro k
  Hint "Ask for half: `obtain ⟨N, hN⟩ := {h} (succ k + k)`."
  obtain ⟨N, hN⟩ := h (succ k + k)
  use N
  intro n hn
  rw [MyRat.absSeq_apply]
  obtain ⟨b1, b2⟩ := MyRat.abs_bounds (s n)
  constructor
  · Hint "`by_cases hs0 : MyRat.nonneg (s n)`."
    by_cases hs0 : MyRat.nonneg (s n)
    · rw [MyRat.abs_of_nonneg hs0, MyRat.sub_eq_add_neg, MyRat.add_neg]
      exact MyRat.eps_nonneg k
    · rw [MyRat.abs_of_not_nonneg hs0]
      Hint "From `hN n {hn}` get `-s n ≤ frac 1 (succ (succ k + k))`:
      `have a := MyRat.neg_le_neg _ _ (hN n {hn})` and `rw [MyRat.neg_neg] at a`."
      have a := MyRat.neg_le_neg _ _ (hN n hn)
      rw [MyRat.neg_neg] at a
      Hint "Split the bound into halves:
      `rw [MyRat.sub_eq_add_neg, ← MyRat.half (succ k) (MyNat.succ_ne_zero k), MyNat.add_succ]`."
      rw [MyRat.sub_eq_add_neg, ← MyRat.half (succ k) (MyNat.succ_ne_zero k), MyNat.add_succ]
      exact MyRat.add_le_add _ _ _ _ a a
  · Hint "`s n - abs (s n) ≤ 0`. From `{b1}`:
    `have c := MyRat.add_le_add_right _ _ (-MyRat.abs (s n)) {b1}`."
    have c := MyRat.add_le_add_right _ _ (-MyRat.abs (s n)) b1
    rw [MyRat.add_neg, ← MyRat.sub_eq_add_neg] at c
    exact MyRat.le_trans _ 0 _ c (MyRat.eps_nonneg k)

Conclusion "
Nonnegative reals are their own absolute value.
"

NewTheorem MyReal.ofSeq_abs MyRat.absSeq_apply
NewDefinition MyReal.abs MyRat.absSeq
TheoremTab "abs"

end MyReal
