import Game.Levels.Integers

/-!
# The rationals `MyRat`

A rational number is a pair `(a, b)` with `a : ℤ` and `b : ℕ`, `b ≠ 0`, read as `a / b`.
Two pairs `(a, b)` and `(c, d)` are the same rational when `a * d = c * b`
(with `b` and `d` seen in `ℤ` as `mk b 0` and `mk d 0`).

The player writes `frac a b`. For `b = 0` it is defined as `0`, so `frac` is total;
all the computation rules ask for `b ≠ 0`.

`x ≤ y` means `nonneg (y - x)`, and `nonneg (frac a b)` means `0 ≤ a`.

## Plumbing

As for `ℤ`: that the relation is an equivalence and that the formulas respect it is checked
with Lean's `Int` (through `MyInt.toInt`). Players only use the computation rules
(`frac_eq`, `frac_add_frac`, ...) and their own theorems.
-/

/-! `ac_rfl` may use the laws the player proved in the Integers world. -/
instance : Std.Associative (α := MyInt) (· + ·) := ⟨MyInt.add_assoc⟩
instance : Std.Commutative (α := MyInt) (· + ·) := ⟨MyInt.add_comm⟩
instance : Std.Associative (α := MyInt) (· * ·) := ⟨MyInt.mul_assoc⟩
instance : Std.Commutative (α := MyInt) (· * ·) := ⟨MyInt.mul_comm⟩

namespace MyNat

theorem toNat_ofNat : ∀ n : Nat, toNat (ofNat n) = n
  | 0 => rfl
  | n + 1 => by
      show toNat (ofNat n) + 1 = n + 1
      rw [toNat_ofNat n]

theorem toNat_ne_zero {n : MyNat} (h : n ≠ 0) : toNat n ≠ 0 :=
  fun h' => h (toNat_inj (h'.trans toNat_zero.symm))

theorem mul_ne_zero_aux {a b : MyNat} (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by
  intro h
  have h3 := congrArg toNat h
  rw [toNat_mul, toNat_zero] at h3
  exact Nat.mul_ne_zero (toNat_ne_zero ha) (toNat_ne_zero hb) h3

theorem one_ne_zero_aux : (1 : MyNat) ≠ 0 := fun h => zero_ne_succ 0 h.symm

end MyNat

namespace MyInt

open MyNat (toNat toNat_add toNat_mul toNat_inj toNat_zero)

/-- Lean's own integer for `x`. Only used to check plumbing proofs. -/
def toInt (x : MyInt) : Int := Quotient.lift val (fun p q h => (rel_iff p q).1 h) x

theorem toInt_mk (a b : MyNat) : toInt (mk a b) = (toNat a : Int) - (toNat b : Int) := rfl

theorem toInt_inj {x y : MyInt} (h : toInt x = toInt y) : x = y := by
  obtain ⟨a, b, rfl⟩ := exists_mk x
  obtain ⟨c, d, rfl⟩ := exists_mk y
  exact sound h

theorem toInt_add (x y : MyInt) : toInt (x + y) = toInt x + toInt y := by
  obtain ⟨a, b, rfl⟩ := exists_mk x
  obtain ⟨c, d, rfl⟩ := exists_mk y
  rw [mk_add_mk]
  exact val_add (a, b) (c, d)

theorem toInt_neg (x : MyInt) : toInt (-x) = - toInt x := by
  obtain ⟨a, b, rfl⟩ := exists_mk x
  rw [neg_mk]
  exact val_neg (a, b)

theorem toInt_mul (x y : MyInt) : toInt (x * y) = toInt x * toInt y := by
  obtain ⟨a, b, rfl⟩ := exists_mk x
  obtain ⟨c, d, rfl⟩ := exists_mk y
  rw [mk_mul_mk]
  exact val_mul (a, b) (c, d)

theorem toInt_mk_zero (n : MyNat) : toInt (mk n 0) = (toNat n : Int) := by
  rw [toInt_mk, toNat_zero] <;> omega

theorem toInt_zero : toInt 0 = 0 := rfl

theorem le_iff_toInt (x y : MyInt) : x ≤ y ↔ toInt x ≤ toInt y := by
  rw [le_iff]
  constructor
  · rintro ⟨c, rfl⟩
    rw [toInt_add, toInt_mk_zero]
    omega
  · intro h
    refine ⟨MyNat.ofNat (toInt y - toInt x).toNat, ?_⟩
    apply toInt_inj
    rw [toInt_add, toInt_mk_zero, MyNat.toNat_ofNat]
    omega

end MyInt

/-- Nonzero naturals, used as denominators. -/
abbrev Den : Type := {n : MyNat // n ≠ 0}

namespace MyRat

open MyNat (toNat toNat_ne_zero)
open MyInt (toInt toInt_add toInt_neg toInt_mul toInt_mk_zero toInt_inj)

/-- `(a, b)` and `(c, d)` are the same rational when `a * d = c * b`. -/
def Rel (p q : MyInt × Den) : Prop := p.1 * MyInt.mk q.2.1 0 = q.1 * MyInt.mk p.2.1 0

theorem rel_iff (p q : MyInt × Den) :
    Rel p q ↔ toInt p.1 * (toNat q.2.1 : Int) = toInt q.1 * (toNat p.2.1 : Int) := by
  unfold Rel
  constructor
  · intro h
    have h' := congrArg toInt h
    rw [toInt_mul, toInt_mul, toInt_mk_zero, toInt_mk_zero] at h'
    exact h'
  · intro h
    apply toInt_inj
    rw [toInt_mul, toInt_mul, toInt_mk_zero, toInt_mk_zero]
    exact h

theorem rel_trans {p q r : MyInt × Den} (h1 : Rel p q) (h2 : Rel q r) : Rel p r := by
  rw [rel_iff] at h1 h2 ⊢
  have hq : (toNat q.2.1 : Int) ≠ 0 := by
    have := toNat_ne_zero q.2.2
    omega
  apply Int.eq_of_mul_eq_mul_right hq
  calc toInt p.1 * (toNat r.2.1 : Int) * (toNat q.2.1 : Int)
      = toInt p.1 * (toNat q.2.1 : Int) * (toNat r.2.1 : Int) := Int.mul_right_comm _ _ _
    _ = toInt q.1 * (toNat p.2.1 : Int) * (toNat r.2.1 : Int) := by rw [h1]
    _ = toInt q.1 * (toNat r.2.1 : Int) * (toNat p.2.1 : Int) := Int.mul_right_comm _ _ _
    _ = toInt r.1 * (toNat q.2.1 : Int) * (toNat p.2.1 : Int) := by rw [h2]
    _ = toInt r.1 * (toNat p.2.1 : Int) * (toNat q.2.1 : Int) := Int.mul_right_comm _ _ _

instance setoid : Setoid (MyInt × Den) where
  r := Rel
  iseqv := ⟨fun _ => rfl, fun h => Eq.symm h, rel_trans⟩

end MyRat

/-- Our rationals: pairs `(a, b)` with `b ≠ 0`, read as `a / b`, up to `a * d = c * b`. -/
def MyRat : Type := Quotient MyRat.setoid

/-- `ℚ` is our `MyRat`. -/
notation (name := MyRatNotation) (priority := 1000000) "ℚ" => MyRat

namespace MyRat

open MyNat (toNat toNat_ne_zero)
open MyInt (toInt toInt_add toInt_neg toInt_mul toInt_mk_zero toInt_inj)

def mkQ (a : MyInt) (b : Den) : MyRat := Quotient.mk setoid (a, b)

def oneDen : Den := ⟨1, MyNat.one_ne_zero_aux⟩

open Classical in
/-- `frac a b` is the rational `a / b`. For `b = 0` it is `0`. -/
noncomputable def frac (a : MyInt) (b : MyNat) : MyRat :=
  if h : b = 0 then mkQ 0 oneDen else mkQ a ⟨b, h⟩

theorem frac_of_ne {a : MyInt} {b : MyNat} (hb : b ≠ 0) : frac a b = mkQ a ⟨b, hb⟩ :=
  dif_neg hb

theorem frac_zero_den (a : MyInt) : frac a 0 = mkQ 0 oneDen := dif_pos rfl

theorem exists_frac (x : MyRat) : ∃ (a : MyInt) (b : MyNat), b ≠ 0 ∧ x = frac a b :=
  Quotient.ind (motive := fun x => ∃ (a : MyInt) (b : MyNat), b ≠ 0 ∧ x = frac a b)
    (fun p => ⟨p.1, p.2.1, p.2.2, (frac_of_ne (a := p.1) p.2.2).symm⟩) x

theorem frac_eq {a c : MyInt} {b d : MyNat} (hb : b ≠ 0) (hd : d ≠ 0) :
    frac a b = frac c d ↔ a * MyInt.mk d 0 = c * MyInt.mk b 0 := by
  rw [frac_of_ne hb, frac_of_ne hd]
  exact ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

noncomputable instance : OfNat MyRat 0 := ⟨frac 0 1⟩
noncomputable instance : OfNat MyRat 1 := ⟨frac 1 1⟩

theorem zero_def : (0 : MyRat) = frac 0 1 := rfl

theorem one_def : (1 : MyRat) = frac 1 1 := rfl

/-- Den of a product. -/
def mulDen (b d : Den) : Den := ⟨b.1 * d.1, MyNat.mul_ne_zero_aux b.2 d.2⟩

theorem add_respects (p q p' q' : MyInt × Den) (hp : Rel p p') (hq : Rel q q') :
    Rel (p.1 * MyInt.mk q.2.1 0 + q.1 * MyInt.mk p.2.1 0, mulDen p.2 q.2)
        (p'.1 * MyInt.mk q'.2.1 0 + q'.1 * MyInt.mk p'.2.1 0, mulDen p'.2 q'.2) := by
  rw [rel_iff] at hp hq ⊢
  simp only [mulDen, toInt_add, toInt_mul, toInt_mk_zero, MyNat.toNat_mul, Int.natCast_mul]
  grind

theorem mul_respects (p q p' q' : MyInt × Den) (hp : Rel p p') (hq : Rel q q') :
    Rel (p.1 * q.1, mulDen p.2 q.2) (p'.1 * q'.1, mulDen p'.2 q'.2) := by
  rw [rel_iff] at hp hq ⊢
  simp only [mulDen, toInt_mul, MyNat.toNat_mul, Int.natCast_mul]
  grind

theorem neg_respects (p q : MyInt × Den) (h : Rel p q) : Rel (-p.1, p.2) (-q.1, q.2) := by
  rw [rel_iff] at h ⊢
  simp only [toInt_neg]
  rw [Int.neg_mul, Int.neg_mul, h]

/-- Addition: `a/b + c/d = (a d + c b) / (b d)`. -/
def add (x y : MyRat) : MyRat :=
  Quotient.lift₂ (fun p q => mkQ (p.1 * MyInt.mk q.2.1 0 + q.1 * MyInt.mk p.2.1 0) (mulDen p.2 q.2))
    (fun p q p' q' hp hq => Quotient.sound (add_respects p q p' q' hp hq)) x y

/-- Negation: `-(a/b) = (-a)/b`. -/
def neg (x : MyRat) : MyRat :=
  Quotient.lift (fun p => mkQ (-p.1) p.2) (fun p q h => Quotient.sound (neg_respects p q h)) x

/-- Multiplication: `(a/b)(c/d) = (a c)/(b d)`. -/
def mul (x y : MyRat) : MyRat :=
  Quotient.lift₂ (fun p q => mkQ (p.1 * q.1) (mulDen p.2 q.2))
    (fun p q p' q' hp hq => Quotient.sound (mul_respects p q p' q' hp hq)) x y

instance : Add MyRat := ⟨add⟩
instance : Neg MyRat := ⟨neg⟩
instance : Mul MyRat := ⟨mul⟩
instance : Sub MyRat := ⟨fun x y => x + -y⟩

theorem frac_add_frac {a c : MyInt} {b d : MyNat} (hb : b ≠ 0) (hd : d ≠ 0) :
    frac a b + frac c d = frac (a * MyInt.mk d 0 + c * MyInt.mk b 0) (b * d) := by
  rw [frac_of_ne hb, frac_of_ne hd, frac_of_ne (MyNat.mul_ne_zero_aux hb hd)] <;> rfl

theorem frac_mul_frac {a c : MyInt} {b d : MyNat} (hb : b ≠ 0) (hd : d ≠ 0) :
    frac a b * frac c d = frac (a * c) (b * d) := by
  rw [frac_of_ne hb, frac_of_ne hd, frac_of_ne (MyNat.mul_ne_zero_aux hb hd)] <;> rfl

theorem neg_frac (a : MyInt) (b : MyNat) : -frac a b = frac (-a) b := by
  by_cases hb : b = 0
  · subst hb
    rw [frac_zero_den, frac_zero_den]
    apply Quotient.sound
    show Rel _ _
    rw [rel_iff]
    simp only [toInt_neg, MyInt.toInt_zero]
    omega
  · rw [frac_of_ne hb, frac_of_ne hb] <;> rfl

theorem sub_eq_add_neg (x y : MyRat) : x - y = x + -y := rfl

theorem nonneg_respects (p q : MyInt × Den) (h : Rel p q) (hp : (0 : MyInt) ≤ p.1) :
    (0 : MyInt) ≤ q.1 := by
  rw [rel_iff] at h
  rw [MyInt.le_iff_toInt, MyInt.toInt_zero] at hp ⊢
  have hP : (0 : Int) < toNat p.2.1 := by
    have := toNat_ne_zero p.2.2
    omega
  have hQ : (0 : Int) ≤ toNat q.2.1 := by omega
  have h1 : 0 ≤ toInt p.1 * (toNat q.2.1 : Int) := Int.mul_nonneg hp hQ
  rw [h] at h1
  refine Int.le_of_mul_le_mul_right ?_ hP
  rw [Int.zero_mul]
  exact h1

/-- `nonneg x` means `x ≥ 0`. For `frac a b` with `b ≠ 0` it means `0 ≤ a`. -/
def nonneg (x : MyRat) : Prop :=
  Quotient.lift (fun p => (0 : MyInt) ≤ p.1)
    (fun p q h => propext ⟨nonneg_respects p q h, nonneg_respects q p (Setoid.symm h)⟩) x

attribute [pp_nodot] nonneg

instance : LE MyRat := ⟨fun x y => nonneg (y - x)⟩

theorem le_iff_nonneg (x y : MyRat) : x ≤ y ↔ nonneg (y - x) := Iff.rfl

theorem nonneg_frac {a : MyInt} {b : MyNat} (hb : b ≠ 0) : nonneg (frac a b) ↔ 0 ≤ a := by
  rw [frac_of_ne hb]
  exact Iff.rfl

attribute [irreducible] add neg mul nonneg frac

end MyRat
