import Game.MyReal.Seq

/-!
# Plumbing: our `ℚ` inside Lean's `Rat`

Only used to check well-definedness proofs behind the scenes (that `-`, `*`, `abs` and `≤`
on `ℝ` do not depend on the chosen Cauchy sequences). The player never sees or uses it.

`toRat` sends our rational `frac a b` to Lean's rational `a / b`. It respects `+`, `-`, `*`
and `≤`, so facts about Lean's `Rat` (checked with `grind`) carry over.
-/

namespace MyNat

theorem le_iff_toNat (a b : MyNat) : a ≤ b ↔ toNat a ≤ toNat b := by
  constructor
  · rintro ⟨c, rfl⟩
    rw [toNat_add]
    omega
  · intro h
    refine ⟨ofNat (toNat b - toNat a), ?_⟩
    apply toNat_inj
    rw [toNat_add, toNat_ofNat]
    omega

theorem ofNat_toNat : ∀ n : MyNat, ofNat (toNat n) = n
  | .zero => rfl
  | .succ n => by
      show succ (ofNat (toNat n)) = succ n
      rw [ofNat_toNat n]

/-- An upper bound for two naturals. -/
theorem le_add_left' (a b : MyNat) : b ≤ a + b := by
  rw [le_iff_toNat, toNat_add]
  omega

theorem le_add_right' (a b : MyNat) : a ≤ a + b := by
  rw [le_iff_toNat, toNat_add]
  omega

theorem le_trans' {a b c : MyNat} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  rw [le_iff_toNat] at *
  omega

end MyNat

namespace MyRat

open MyNat (toNat toNat_ne_zero)
open MyInt (toInt toInt_add toInt_neg toInt_mul toInt_mk_zero toInt_inj)

/-- Lean's rational for a pair `(a, b)`: `a / b`. -/
def toRatP (p : MyInt × Den) : Rat := (toInt p.1 : Rat) / (toNat p.2.1 : Rat)

theorem den_ne' {b : MyNat} (hb : b ≠ 0) : (toNat b : Rat) ≠ 0 := by
  have := toNat_ne_zero hb
  intro h
  rw [Rat.natCast_eq_zero_iff] at h
  omega

theorem den_pos' {b : MyNat} (hb : b ≠ 0) : (0 : Rat) < (toNat b : Rat) := by
  have := toNat_ne_zero hb
  rw [Rat.natCast_pos]
  omega

theorem div_nonneg' {a b : Rat} (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ a / b := by
  rw [Rat.div_def]
  exact Rat.mul_nonneg ha (Rat.le_of_lt (Rat.inv_pos.mpr hb))

theorem div_pos' {a b : Rat} (ha : 0 < a) (hb : 0 < b) : 0 < a / b := by
  rw [Rat.div_def]
  exact Rat.mul_pos ha (Rat.inv_pos.mpr hb)

theorem den_ne (b : Den) : (toNat b.1 : Rat) ≠ 0 := den_ne' b.2

theorem cast_eq {a c : Int} {b d : Nat} (h : a * (d : Int) = c * (b : Int)) :
    (a : Rat) * (d : Rat) = (c : Rat) * (b : Rat) := by
  have h2 := congrArg (fun z : Int => (z : Rat)) h
  simp only [Rat.intCast_mul, Rat.intCast_natCast] at h2
  exact h2

theorem toRatP_respects (p q : MyInt × Den) (h : Rel p q) : toRatP p = toRatP q := by
  rw [rel_iff] at h
  unfold toRatP
  have hp := den_ne p.2
  have hq := den_ne q.2
  have h' := cast_eq h
  grind

/-- Lean's rational number for our rational `x`. -/
def toRat (x : MyRat) : Rat := Quotient.lift toRatP toRatP_respects x

theorem toRat_frac {a : MyInt} {b : MyNat} (hb : b ≠ 0) :
    toRat (frac a b) = (toInt a : Rat) / (toNat b : Rat) := by
  rw [frac_of_ne hb]
  rfl

theorem toRat_inj {x y : MyRat} (h : toRat x = toRat y) : x = y := by
  obtain ⟨a, b, hb, rfl⟩ := exists_frac x
  obtain ⟨c, d, hd, rfl⟩ := exists_frac y
  rw [frac_eq hb hd]
  rw [toRat_frac hb, toRat_frac hd] at h
  have hb' := den_ne' hb
  have hd' := den_ne' hd
  apply toInt_inj
  rw [toInt_mul, toInt_mul, toInt_mk_zero, toInt_mk_zero]
  have h2 : ((toInt a * (toNat d : Int) : Int) : Rat) = ((toInt c * (toNat b : Int) : Int) : Rat) := by
    simp only [Rat.intCast_mul, Rat.intCast_natCast]
    grind
  exact Rat.intCast_inj.mp h2

theorem toRat_add (x y : MyRat) : toRat (x + y) = toRat x + toRat y := by
  obtain ⟨a, b, hb, rfl⟩ := exists_frac x
  obtain ⟨c, d, hd, rfl⟩ := exists_frac y
  rw [frac_add_frac hb hd, toRat_frac hb, toRat_frac hd, toRat_frac (MyNat.mul_ne_zero_aux hb hd)]
  rw [toInt_add, toInt_mul, toInt_mul, toInt_mk_zero, toInt_mk_zero, MyNat.toNat_mul]
  have hb' := den_ne' hb
  have hd' := den_ne' hd
  simp only [Rat.intCast_add, Rat.intCast_mul, Rat.intCast_natCast, Rat.natCast_mul]
  grind

theorem toRat_neg (x : MyRat) : toRat (-x) = - toRat x := by
  obtain ⟨a, b, hb, rfl⟩ := exists_frac x
  rw [neg_frac, toRat_frac hb, toRat_frac hb, toInt_neg, Rat.intCast_neg]
  grind

theorem toRat_sub (x y : MyRat) : toRat (x - y) = toRat x - toRat y := by
  rw [sub_eq_add_neg, toRat_add, toRat_neg]
  grind

theorem toRat_mul (x y : MyRat) : toRat (x * y) = toRat x * toRat y := by
  obtain ⟨a, b, hb, rfl⟩ := exists_frac x
  obtain ⟨c, d, hd, rfl⟩ := exists_frac y
  rw [frac_mul_frac hb hd, toRat_frac hb, toRat_frac hd, toRat_frac (MyNat.mul_ne_zero_aux hb hd)]
  rw [toInt_mul, MyNat.toNat_mul]
  have hb' := den_ne' hb
  have hd' := den_ne' hd
  simp only [Rat.intCast_add, Rat.intCast_mul, Rat.intCast_natCast, Rat.natCast_mul]
  grind

theorem nonneg_iff_toRat (x : MyRat) : nonneg x ↔ 0 ≤ toRat x := by
  obtain ⟨a, b, hb, rfl⟩ := exists_frac x
  rw [nonneg_frac hb, toRat_frac hb, MyInt.le_iff_toInt, MyInt.toInt_zero]
  have hb' := den_pos' hb
  constructor
  · intro h
    exact div_nonneg' (Rat.intCast_nonneg.mpr h) hb'
  · intro h
    have h2 : (0 : Rat) ≤ (toInt a : Rat) := by
      have := Rat.mul_nonneg h (Rat.le_of_lt hb')
      rw [Rat.div_mul_cancel (Rat.ne_of_gt hb')] at this
      exact this
    exact Rat.intCast_nonneg.mp h2

theorem le_iff_toRat (x y : MyRat) : x ≤ y ↔ toRat x ≤ toRat y := by
  rw [le_iff_nonneg, nonneg_iff_toRat, toRat_sub]
  grind

theorem toRat_zero : toRat 0 = 0 := by
  rw [zero_def, toRat_frac MyNat.one_ne_zero_aux, MyInt.toInt_zero, Rat.div_def]
  simp

/-- `1/(k+1)` in Lean's `Rat`. -/
theorem toRat_eps (k : MyNat) :
    toRat (frac 1 (MyNat.succ k)) = 1 / ((toNat k : Rat) + 1) := by
  rw [toRat_frac (fun h => MyNat.zero_ne_succ k h.symm)]
  show ((toInt (MyInt.mk 1 0) : Int) : Rat) / ((toNat k + 1 : Nat) : Rat) = _
  rw [MyInt.toInt_mk_zero]
  simp only [Rat.intCast_natCast, Rat.natCast_add]
  rfl

theorem eps_pos (k : MyNat) : (0 : Rat) < toRat (frac 1 (MyNat.succ k)) := by
  rw [toRat_eps]
  have : (0 : Rat) < (toNat k : Rat) + 1 := by
    have := @Rat.natCast_nonneg (toNat k)
    grind
  exact div_pos' (by decide) this

/-- Lean's `Rat` is archimedean: every `ε > 0` is above some `1/(k+1)`. -/
theorem exists_eps_le (ε : Rat) (h : 0 < ε) : ∃ k : MyNat, toRat (frac 1 (MyNat.succ k)) ≤ ε := by
  refine ⟨MyNat.ofNat ((1 / ε).ceil.toNat), ?_⟩
  rw [toRat_eps, MyNat.toNat_ofNat]
  have h1 : 1 / ε ≤ (((1 / ε).ceil.toNat : Int) : Rat) := by
    have := Rat.le_ceil (x := 1 / ε)
    have h2 : (1 / ε).ceil ≤ ((1 / ε).ceil.toNat : Int) := Int.self_le_toNat _
    exact Rat.le_trans this (Rat.intCast_le_intCast.mpr h2)
  rw [Rat.intCast_natCast] at h1
  generalize ((1 / ε).ceil.toNat : Rat) = n at h1 ⊢
  have hn : 0 < n + 1 := by
    have : 0 ≤ 1 / ε := Rat.le_of_lt (div_pos' (by decide) h)
    grind
  have he : ε * (1 / ε) = 1 := by
    rw [Rat.div_def, Rat.one_mul, Rat.mul_inv_cancel _ (Rat.ne_of_gt h)]
  have h3 : 1 ≤ ε * (n + 1) := by
    have := Rat.mul_le_mul_of_nonneg_left h1 (Rat.le_of_lt h)
    rw [he] at this
    have h4 : ε * n ≤ ε * (n + 1) := Rat.mul_le_mul_of_nonneg_left (by grind) (Rat.le_of_lt h)
    grind
  rw [Rat.div_def, Rat.one_mul]
  have := Rat.mul_le_mul_of_nonneg_right h3 (Rat.le_of_lt (Rat.inv_pos.mpr hn))
  rw [Rat.one_mul, Rat.mul_assoc, Rat.mul_inv_cancel _ (Rat.ne_of_gt hn), Rat.mul_one] at this
  exact this

/-! ## Sequences in Lean's `Rat` -/

/-- Cauchy, with `ε > 0` in Lean's `Rat`. -/
def RCauchy (f : MyNat → Rat) : Prop :=
  ∀ ε, 0 < ε → ∃ N : MyNat, ∀ m n, N ≤ m → N ≤ n → f m - f n ≤ ε

/-- Close, with `ε > 0` in Lean's `Rat`. -/
def RClose (f g : MyNat → Rat) : Prop :=
  ∀ ε, 0 < ε → ∃ N : MyNat, ∀ n, N ≤ n → f n - g n ≤ ε ∧ g n - f n ≤ ε

theorem isCauchy_iff (s : MyNat → MyRat) : IsCauchy s ↔ RCauchy (fun n => toRat (s n)) := by
  constructor
  · intro h ε hε
    obtain ⟨k, hk⟩ := exists_eps_le ε hε
    obtain ⟨N, hN⟩ := h k
    refine ⟨N, fun m n hm hn => ?_⟩
    have := (le_iff_toRat _ _).1 (hN m n hm hn)
    rw [toRat_sub] at this
    exact Rat.le_trans this hk
  · intro h k
    obtain ⟨N, hN⟩ := h _ (eps_pos k)
    refine ⟨N, fun m n hm hn => ?_⟩
    rw [le_iff_toRat, toRat_sub]
    exact hN m n hm hn

theorem close_iff (s t : MyNat → MyRat) : Close s t ↔ RClose (fun n => toRat (s n)) (fun n => toRat (t n)) := by
  constructor
  · intro h ε hε
    obtain ⟨k, hk⟩ := exists_eps_le ε hε
    obtain ⟨N, hN⟩ := h k
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨h1, h2⟩ := hN n hn
    rw [le_iff_toRat, toRat_sub] at h1 h2
    exact ⟨Rat.le_trans h1 hk, Rat.le_trans h2 hk⟩
  · intro h k
    obtain ⟨N, hN⟩ := h _ (eps_pos k)
    refine ⟨N, fun n hn => ?_⟩
    rw [le_iff_toRat, toRat_sub, le_iff_toRat, toRat_sub]
    exact hN n hn

/-- A Cauchy sequence is bounded. -/
theorem RCauchy.bounded {f : MyNat → Rat} (h : RCauchy f) : ∃ B : Rat, 0 < B ∧ ∀ n, f n ≤ B ∧ -B ≤ f n := by
  obtain ⟨N, hN⟩ := h 1 (by decide)
  -- bound for the first `N` terms
  have first : ∀ M : Nat, ∃ B : Rat, 0 < B ∧ ∀ n : MyNat, toNat n < M → f n ≤ B ∧ -B ≤ f n := by
    intro M
    induction M with
    | zero => exact ⟨1, by decide, fun n hn => absurd hn (Nat.not_lt_zero _)⟩
    | succ M ih =>
      obtain ⟨B, hB, hB'⟩ := ih
      refine ⟨B + Rat.abs (f (MyNat.ofNat M)), ?_, ?_⟩
      · have := Rat.abs_nonneg (x := f (MyNat.ofNat M))
        grind
      · intro n hn
        by_cases hM : toNat n < M
        · have := hB' n hM
          have := Rat.abs_nonneg (x := f (MyNat.ofNat M))
          grind
        · have hn' : n = MyNat.ofNat M := by
            rw [← MyNat.ofNat_toNat n]
            congr 1
            omega
          subst hn'
          have hB0 := Rat.le_of_lt hB
          unfold Rat.abs
          split <;> grind
  obtain ⟨B, hB, hB'⟩ := first (toNat N)
  refine ⟨B + Rat.abs (f N) + 1, ?_, ?_⟩
  · have := Rat.abs_nonneg (x := f N)
    grind
  · intro n
    have ha := Rat.abs_nonneg (x := f N)
    by_cases hn : toNat n < toNat N
    · have := hB' n hn
      grind
    · have hNn : N ≤ n := by
        rw [MyNat.le_iff_toNat]
        omega
      have h1 := hN n N hNn ((MyNat.le_iff_toNat _ _).2 (Nat.le_refl _))
      have h2 := hN N n ((MyNat.le_iff_toNat _ _).2 (Nat.le_refl _)) hNn
      have hB0 := Rat.le_of_lt hB
      unfold Rat.abs at ha ⊢
      split <;> grind

/-- If `-B ≤ x ≤ B` and `-e ≤ y ≤ e`, then `-(B e) ≤ x y ≤ B e`. -/
theorem mul_bound {x y B e : Rat} (h1 : x ≤ B) (h2 : -B ≤ x) (h3 : y ≤ e) (h4 : -e ≤ y) :
    x * y ≤ B * e ∧ -(B * e) ≤ x * y := by
  have a1 : 0 ≤ (B - x) * (e + y) := Rat.mul_nonneg (by grind) (by grind)
  have a2 : 0 ≤ (B + x) * (e - y) := Rat.mul_nonneg (by grind) (by grind)
  have a3 : 0 ≤ (B - x) * (e - y) := Rat.mul_nonneg (by grind) (by grind)
  have a4 : 0 ≤ (B + x) * (e + y) := Rat.mul_nonneg (by grind) (by grind)
  constructor <;> grind

end MyRat
