import Game.Levels.RealOrder.L15_RealLeTotal

/-!
# Absolute value on `ℚ` and `ℝ`

* On `ℚ`: `abs a = a` if `nonneg a`, and `abs a = -a` otherwise (rules `abs_of_nonneg`,
  `abs_of_not_nonneg`). This is the textbook definition.
* On `ℝ`: take the absolute value term by term, `abs (ofSeq s hs) = ofSeq (absSeq s) _`.

## Plumbing

That `absSeq s` is Cauchy and does not depend on the chosen sequence is checked here with
Lean's `Rat` and `grind`.
-/

namespace MyRat

open Classical in
/-- The absolute value `|a|`: `a` if `a ≥ 0`, else `-a`. -/
noncomputable def abs (a : ℚ) : ℚ := if nonneg a then a else -a

attribute [pp_nodot] abs

theorem abs_of_nonneg {a : ℚ} (h : nonneg a) : abs a = a := if_pos h

theorem abs_of_not_nonneg {a : ℚ} (h : ¬ nonneg a) : abs a = -a := if_neg h

/-- The sequence `|s 0|, |s 1|, …`. -/
noncomputable def absSeq (s : MyNat → ℚ) : MyNat → ℚ := fun n => abs (s n)

theorem absSeq_apply (s : MyNat → ℚ) (n : MyNat) : absSeq s n = abs (s n) := rfl

/-! ### Plumbing -/

theorem toRat_abs (a : ℚ) : toRat (abs a) = Rat.abs (toRat a) := by
  unfold Rat.abs
  by_cases h : nonneg a
  · rw [abs_of_nonneg h, if_pos ((nonneg_iff_toRat a).1 h)]
  · rw [abs_of_not_nonneg h, toRat_neg, if_neg (fun h' => h ((nonneg_iff_toRat a).2 h'))]

theorem RCauchy.abs {f : MyNat → Rat} (h : RCauchy f) : RCauchy (fun n => Rat.abs (f n)) := by
  intro ε hε
  obtain ⟨N, hN⟩ := h.symm hε
  refine ⟨N, fun m n hm hn => ?_⟩
  obtain ⟨h1, h2⟩ := hN m n hm hn
  show Rat.abs (f m) - Rat.abs (f n) ≤ ε
  unfold Rat.abs
  grind

theorem RClose.abs {f g : MyNat → Rat} (h : RClose f g) :
    RClose (fun n => Rat.abs (f n)) (fun n => Rat.abs (g n)) := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨h1, h2⟩ := hN n hn
  show Rat.abs (f n) - Rat.abs (g n) ≤ ε ∧ Rat.abs (g n) - Rat.abs (f n) ≤ ε
  unfold Rat.abs
  grind

theorem abs_cauchy (s : MyNat → ℚ) (hs : IsCauchy s) : IsCauchy (absSeq s) := by
  rw [isCauchy_iff] at hs ⊢
  have := hs.abs
  simp only [absSeq, toRat_abs]
  exact this

theorem close_abs (s s' : MyNat → ℚ) (h : Close s s') : Close (absSeq s) (absSeq s') := by
  rw [close_iff] at h ⊢
  have := h.abs
  simp only [absSeq, toRat_abs]
  exact this

attribute [irreducible] abs

end MyRat

namespace MyReal

/-- The absolute value of a real: take `|·|` term by term. -/
noncomputable def abs (x : MyReal) : MyReal :=
  Quotient.lift (fun s : CauchySeq => ofSeq (MyRat.absSeq s.1) (MyRat.abs_cauchy s.1 s.2))
    (fun s s' h => Quotient.sound (MyRat.close_abs s.1 s'.1 h)) x

attribute [pp_nodot] abs

theorem ofSeq_abs {s : MyNat → MyRat} {hs : MyRat.IsCauchy s} :
    abs (ofSeq s hs) = ofSeq (MyRat.absSeq s) (MyRat.abs_cauchy s hs) := rfl

attribute [irreducible] abs

end MyReal
