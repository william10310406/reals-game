import Game.Levels.RealArith

/-!
# Order on `ℝ`

A real `x = ofSeq s hs` is `≥ 0` (`nonneg x`) when its terms are eventually above every
negative bound:

`∀ k, ∃ N, ∀ n ≥ N, -1/(k+1) ≤ s n`

(rule `nonneg_ofSeq`). Then `x ≤ y` means `nonneg (y - x)`, as for `ℚ` (rule `le_iff_nonneg`).

## Plumbing

That `nonneg` does not depend on the chosen sequence is checked here with Lean's `Rat`.
-/

namespace MyRat

/-- The terms of `s` are eventually `≥ -1/(k+1)`, for every `k`. -/
def SeqNonneg (s : MyNat → ℚ) : Prop :=
  ∀ k : MyNat, ∃ N : MyNat, ∀ n : MyNat, N ≤ n → -frac 1 (MyNat.succ k) ≤ s n

theorem seqNonneg_iff (s : MyNat → ℚ) :
    SeqNonneg s ↔ ∀ ε : Rat, 0 < ε → ∃ N : MyNat, ∀ n, N ≤ n → -ε ≤ toRat (s n) := by
  constructor
  · intro h ε hε
    obtain ⟨k, hk⟩ := exists_eps_le ε hε
    obtain ⟨N, hN⟩ := h k
    refine ⟨N, fun n hn => ?_⟩
    have := (le_iff_toRat _ _).1 (hN n hn)
    rw [toRat_neg] at this
    grind
  · intro h k
    obtain ⟨N, hN⟩ := h _ (eps_pos k)
    refine ⟨N, fun n hn => ?_⟩
    rw [le_iff_toRat, toRat_neg]
    exact hN n hn

theorem seqNonneg_close (s t : MyNat → ℚ) (h : Close s t) (hs : SeqNonneg s) : SeqNonneg t := by
  rw [seqNonneg_iff] at hs ⊢
  rw [close_iff] at h
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := exists_small ε 1 hε (by decide)
  obtain ⟨N1, hN1⟩ := hs δ hδ
  obtain ⟨N2, hN2⟩ := h δ hδ
  refine ⟨N1 + N2, fun n hn => ?_⟩
  have hn1 := MyNat.le_trans' (MyNat.le_add_right' N1 N2) hn
  have hn2 := MyNat.le_trans' (MyNat.le_add_left' N1 N2) hn
  have a := hN1 n hn1
  have b := (hN2 n hn2).1
  grind

end MyRat

namespace MyReal

/-- `nonneg x` means `x ≥ 0`: the terms of its sequence are eventually `≥ -1/(k+1)`, for every `k`. -/
def nonneg (x : MyReal) : Prop :=
  Quotient.lift (fun s : CauchySeq => MyRat.SeqNonneg s.1)
    (fun s t h => propext ⟨MyRat.seqNonneg_close _ _ h,
      MyRat.seqNonneg_close _ _ (MyRat.close_symm _ _ h)⟩) x

theorem nonneg_ofSeq {s : MyNat → MyRat} {hs : MyRat.IsCauchy s} :
    nonneg (ofSeq s hs) ↔
      ∀ k : MyNat, ∃ N : MyNat, ∀ n : MyNat, N ≤ n → -MyRat.frac 1 (MyNat.succ k) ≤ s n :=
  Iff.rfl

attribute [pp_nodot] nonneg

instance : LE MyReal := ⟨fun x y => nonneg (y - x)⟩

theorem le_iff_nonneg (x y : MyReal) : x ≤ y ↔ nonneg (y - x) := Iff.rfl

attribute [irreducible] nonneg

end MyReal
