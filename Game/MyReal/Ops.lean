import Game.Levels.Limits
import Game.MyRat.ToRat
import Game.MyReal.Add

/-!
# Negation, multiplication, `0`, `1` and `ℚ` inside `ℝ`

All operations work term by term on Cauchy sequences:

* `-ofSeq s hs = ofSeq (negSeq s) _`
* `ofSeq s hs * ofSeq t ht = ofSeq (mulSeq s t) _`
* `ofRat q = ofSeq (const q) _`, `0 = ofRat 0`, `1 = ofRat 1`

## Plumbing

That `negSeq s` and `mulSeq s t` are Cauchy, and that the results do not depend on the chosen
sequences, is checked here with Lean's `Rat` (through `MyRat.toRat`) and `grind`.
For `*` this needs that Cauchy sequences are bounded. The player only uses the rules
`ofSeq_neg`, `ofSeq_mul`, `negSeq_apply`, `mulSeq_apply`, `ofRat_def`, `zero_def`, `one_def`.
-/

namespace MyRat

/-- The sequence `-s 0, -s 1, ...`. -/
def negSeq (s : MyNat → ℚ) : MyNat → ℚ := fun n => -s n

theorem negSeq_apply (s : MyNat → ℚ) (n : MyNat) : negSeq s n = -s n := rfl

/-- The sequence `s 0 * t 0, s 1 * t 1, ...`. -/
def mulSeq (s t : MyNat → ℚ) : MyNat → ℚ := fun n => s n * t n

theorem mulSeq_apply (s t : MyNat → ℚ) (n : MyNat) : mulSeq s t n = s n * t n := rfl

/-! ### Plumbing in Lean's `Rat` -/

theorem RCauchy.neg {f : MyNat → Rat} (h : RCauchy f) : RCauchy (fun n => - f n) := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  exact ⟨N, fun m n hm hn => by have := hN n m hn hm; grind⟩

theorem RClose.neg {f g : MyNat → Rat} (h : RClose f g) : RClose (fun n => - f n) (fun n => - g n) := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  exact ⟨N, fun n hn => by have := hN n hn; grind⟩

theorem RCauchy.symm {f : MyNat → Rat} (h : RCauchy f) {ε : Rat} (hε : 0 < ε) :
    ∃ N : MyNat, ∀ m n, N ≤ m → N ≤ n → f m - f n ≤ ε ∧ f n - f m ≤ ε := by
  obtain ⟨N, hN⟩ := h ε hε
  exact ⟨N, fun m n hm hn => ⟨hN m n hm hn, hN n m hn hm⟩⟩

/-- A small number `δ` with `B * δ * 2 = ε`. -/
theorem exists_small (ε B : Rat) (hε : 0 < ε) (hB : 0 < B) :
    ∃ δ : Rat, 0 < δ ∧ B * δ + B * δ = ε := by
  refine ⟨ε / (B + B), div_pos' hε (by grind), ?_⟩
  have h2 : B + B ≠ 0 := by grind
  have hinv := Rat.mul_inv_cancel _ h2
  rw [Rat.div_def]
  grind

theorem RCauchy.mul {f g : MyNat → Rat} (hf : RCauchy f) (hg : RCauchy g) :
    RCauchy (fun n => f n * g n) := by
  intro ε hε
  obtain ⟨B1, hB1, hb1⟩ := hf.bounded
  obtain ⟨B2, hB2, hb2⟩ := hg.bounded
  obtain ⟨δ, hδ, hδε⟩ := exists_small ε (B1 + B2) hε (by grind)
  obtain ⟨N1, hN1⟩ := hf.symm hδ
  obtain ⟨N2, hN2⟩ := hg.symm hδ
  refine ⟨N1 + N2, fun m n hm hn => ?_⟩
  have hm1 := MyNat.le_trans' (MyNat.le_add_right' N1 N2) hm
  have hn1 := MyNat.le_trans' (MyNat.le_add_right' N1 N2) hn
  have hm2 := MyNat.le_trans' (MyNat.le_add_left' N1 N2) hm
  have hn2 := MyNat.le_trans' (MyNat.le_add_left' N1 N2) hn
  obtain ⟨a1, a2⟩ := hN2 m n hm2 hn2
  obtain ⟨b1, b2⟩ := hN1 m n hm1 hn1
  obtain ⟨c1, c2⟩ := hb1 m
  obtain ⟨d1, d2⟩ := hb2 n
  have e1 := (mul_bound (x := f m) (y := g m - g n) (B := B1 + B2) (e := δ)
    (by grind) (by grind) a1 (by grind)).1
  have e2 := (mul_bound (x := g n) (y := f m - f n) (B := B1 + B2) (e := δ)
    (by grind) (by grind) b1 (by grind)).1
  have : f m * g m - f n * g n = f m * (g m - g n) + g n * (f m - f n) := by grind
  grind

theorem RClose.mul {f f' g g' : MyNat → Rat} (hf : RCauchy f) (hg' : RCauchy g')
    (h1 : RClose f f') (h2 : RClose g g') :
    RClose (fun n => f n * g n) (fun n => f' n * g' n) := by
  intro ε hε
  obtain ⟨B1, hB1, hb1⟩ := hf.bounded
  obtain ⟨B2, hB2, hb2⟩ := hg'.bounded
  obtain ⟨δ, hδ, hδε⟩ := exists_small ε (B1 + B2) hε (by grind)
  obtain ⟨N1, hN1⟩ := h1 δ hδ
  obtain ⟨N2, hN2⟩ := h2 δ hδ
  refine ⟨N1 + N2, fun n hn => ?_⟩
  have hn1 := MyNat.le_trans' (MyNat.le_add_right' N1 N2) hn
  have hn2 := MyNat.le_trans' (MyNat.le_add_left' N1 N2) hn
  obtain ⟨a1, a2⟩ := hN2 n hn2
  obtain ⟨b1, b2⟩ := hN1 n hn1
  obtain ⟨c1, c2⟩ := hb1 n
  obtain ⟨d1, d2⟩ := hb2 n
  have e1 := mul_bound (x := f n) (y := g n - g' n) (B := B1 + B2) (e := δ)
    (by grind) (by grind) a1 (by grind)
  have e2 := mul_bound (x := g' n) (y := f n - f' n) (B := B1 + B2) (e := δ)
    (by grind) (by grind) b1 (by grind)
  have : f n * g n - f' n * g' n = f n * (g n - g' n) + g' n * (f n - f' n) := by grind
  constructor <;> grind

/-! ### Back to our `ℚ` -/

theorem neg_cauchy (s : MyNat → ℚ) (hs : IsCauchy s) : IsCauchy (negSeq s) := by
  rw [isCauchy_iff] at hs ⊢
  have := hs.neg
  simp only [negSeq, toRat_neg]
  exact this

theorem close_neg (s s' : MyNat → ℚ) (h : Close s s') : Close (negSeq s) (negSeq s') := by
  rw [close_iff] at h ⊢
  have := h.neg
  simp only [negSeq, toRat_neg]
  exact this

theorem mul_cauchy (s t : MyNat → ℚ) (hs : IsCauchy s) (ht : IsCauchy t) : IsCauchy (mulSeq s t) := by
  rw [isCauchy_iff] at hs ht ⊢
  have := hs.mul ht
  simp only [mulSeq, toRat_mul]
  exact this

theorem close_mul (s s' t t' : MyNat → ℚ) (hs : IsCauchy s) (ht' : IsCauchy t')
    (h1 : Close s s') (h2 : Close t t') : Close (mulSeq s t) (mulSeq s' t') := by
  rw [isCauchy_iff] at hs ht'
  rw [close_iff] at h1 h2 ⊢
  have := RClose.mul hs ht' h1 h2
  simp only [mulSeq, toRat_mul]
  exact this

end MyRat

namespace MyReal

/-- Negation of reals: negate the sequence term by term. -/
def neg (x : MyReal) : MyReal :=
  Quotient.lift (fun s : CauchySeq => ofSeq (MyRat.negSeq s.1) (MyRat.neg_cauchy s.1 s.2))
    (fun s s' h => Quotient.sound (MyRat.close_neg s.1 s'.1 h)) x

/-- Multiplication of reals: multiply the sequences term by term. -/
def mul (x y : MyReal) : MyReal :=
  Quotient.lift₂
    (fun s t : CauchySeq => ofSeq (MyRat.mulSeq s.1 t.1) (MyRat.mul_cauchy s.1 t.1 s.2 t.2))
    (fun s t s' t' hs ht => Quotient.sound (MyRat.close_mul s.1 s'.1 t.1 t'.1 s.2 t'.2 hs ht)) x y

instance : Neg MyReal := ⟨neg⟩
instance : Mul MyReal := ⟨mul⟩
instance : Sub MyReal := ⟨fun x y => x + -y⟩

theorem ofSeq_neg {s : MyNat → MyRat} {hs : MyRat.IsCauchy s} :
    -ofSeq s hs = ofSeq (MyRat.negSeq s) (MyRat.neg_cauchy s hs) := rfl

theorem ofSeq_mul {s t : MyNat → MyRat} {hs : MyRat.IsCauchy s} {ht : MyRat.IsCauchy t} :
    ofSeq s hs * ofSeq t ht = ofSeq (MyRat.mulSeq s t) (MyRat.mul_cauchy s t hs ht) := rfl

theorem sub_eq_add_neg (x y : MyReal) : x - y = x + -y := rfl

/-- The rational `q` as a real number: the constant sequence `q, q, q, ...`. -/
noncomputable def ofRat (q : MyRat) : MyReal := ofSeq (MyRat.const q) (MyRat.const_cauchy q)

theorem ofRat_def (q : MyRat) : ofRat q = ofSeq (MyRat.const q) (MyRat.const_cauchy q) := rfl

noncomputable instance : OfNat MyReal 0 := ⟨ofRat 0⟩
noncomputable instance : OfNat MyReal 1 := ⟨ofRat 1⟩

theorem zero_def : (0 : MyReal) = ofRat 0 := rfl

theorem one_def : (1 : MyReal) = ofRat 1 := rfl

attribute [irreducible] neg mul ofRat

end MyReal
