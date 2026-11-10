import Game.Levels.RealIneq.L12_RatArchimedes

World "RealIneq"
Level 13
Title "Archimedes in ℝ"

namespace MyReal

open MyNat (succ)
open MyInt (mk)

Introduction "
Boss level. **Archimedean property** for `ℝ`: every real is below some natural number.

The idea: a Cauchy sequence stays close to one of its terms. Take `N` for `k = 0`:
then `s n ≤ s N + 1` for `n ≥ N`. And `s N + 1` is a rational, below some natural `p`.
"

/-- For every real $x$ there is a natural $n$ with $x \le n$. -/
Statement archimedean (x : ℝ) : ∃ n : ℕ, x ≤ ofRat (MyRat.frac (mk n 0) 1) := by
  obtain ⟨s, hs, rfl⟩ := exists_ofSeq x
  Hint "Use the Cauchy property with `k = 0`: `obtain ⟨N, hN⟩ := hs 0`."
  obtain ⟨N, hN⟩ := hs 0
  Hint "Now a natural above `s N + frac 1 (succ 0)`:
  `obtain ⟨p, hp⟩ := MyRat.archimedean (s N + MyRat.frac 1 (succ 0))`."
  Branch
    obtain ⟨p, hp⟩ := MyRat.archimedean (s N)
    Hint "`s N` is not enough: the later terms can be up to `1` bigger.
    Use `MyRat.archimedean (s N + MyRat.frac 1 (succ 0))`."
  obtain ⟨p, hp⟩ := MyRat.archimedean (s N + MyRat.frac 1 (succ 0))
  use p
  rw [ofRat_def]
  apply le_of_eventually
  use N
  intro n hn
  rw [MyRat.const_apply]
  Hint "From `hN n N {hn} (MyNat.le_refl N)` get `s n ≤ s N + frac 1 (succ 0)`.
  Add `s N` on both sides with `MyRat.add_le_add_right`, then simplify."
  have h1 := MyRat.add_le_add_right _ _ (s N) (hN n N hn (MyNat.le_refl N))
  rw [MyRat.sub_eq_add_neg, MyRat.add_assoc, MyRat.add_comm (-s N), MyRat.add_neg, MyRat.add_zero,
    MyRat.add_comm] at h1
  exact MyRat.le_trans _ _ _ h1 hp

Conclusion "
`ℝ` is archimedean: there are no infinitely large reals.
"

TheoremTab "≤ℝ"

end MyReal
