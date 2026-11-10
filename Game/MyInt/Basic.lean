import Game.Levels.Naturals

/-!
# The integers `MyInt`

An integer is a pair `(a, b)` of natural numbers, read as `a - b`.
Two pairs `(a, b)` and `(c, d)` are the same integer when `a + d = c + b`.
So `MyInt` is the quotient of `ℕ × ℕ` by this relation.

Addition, negation and multiplication are defined on pairs by the usual formulas
and lifted to the quotient.

## Plumbing

Lifting needs a proof that the formulas respect the relation, and the relation must be an
equivalence. These plumbing proofs are checked with the help of Lean's own `Nat` and `Int`
(through `toNat` and `val`). The player never sees or uses them: in the levels only the
computation rules (`mk_eq`, `mk_add_mk`, ...) and the theorems proved by the player are available.
-/

namespace MyNat

/-- Lean's own number for `n`. Only used to check plumbing proofs. -/
def toNat : MyNat → Nat
  | .zero => 0
  | .succ n => toNat n + 1

theorem toNat_zero : toNat 0 = 0 := rfl

theorem toNat_succ (n : MyNat) : toNat (succ n) = toNat n + 1 := rfl

theorem toNat_add (a b : MyNat) : toNat (a + b) = toNat a + toNat b := by
  induction b with
  | zero => rw [add_zero, toNat_zero, Nat.add_zero]
  | succ n ih => rw [add_succ, toNat_succ, toNat_succ, ih, Nat.add_assoc]

theorem toNat_mul (a b : MyNat) : toNat (a * b) = toNat a * toNat b := by
  induction b with
  | zero => rw [mul_zero, toNat_zero, Nat.mul_zero]
  | succ n ih => rw [mul_succ, toNat_add, ih, toNat_succ, Nat.mul_add_one]

theorem toNat_inj : ∀ {a b : MyNat}, toNat a = toNat b → a = b
  | .zero, .zero, _ => rfl
  | .zero, .succ b, h => by
      change 0 = toNat b + 1 at h
      omega
  | .succ a, .zero, h => by
      change toNat a + 1 = 0 at h
      omega
  | .succ a, .succ b, h => by
      change toNat a + 1 = toNat b + 1 at h
      rw [toNat_inj (a := a) (b := b) (by omega)]

end MyNat

/-! `ac_rfl` may use the laws the player proved in the Naturals world. -/
instance : Std.Associative (α := MyNat) (· + ·) := ⟨MyNat.add_assoc⟩
instance : Std.Commutative (α := MyNat) (· + ·) := ⟨MyNat.add_comm⟩
instance : Std.Associative (α := MyNat) (· * ·) := ⟨MyNat.mul_assoc⟩
instance : Std.Commutative (α := MyNat) (· * ·) := ⟨MyNat.mul_comm⟩

namespace MyInt

open MyNat (toNat toNat_add toNat_mul toNat_inj)

/-- `(a, b)` and `(c, d)` are the same integer when `a + d = c + b`. -/
def Rel (p q : MyNat × MyNat) : Prop := p.1 + q.2 = q.1 + p.2

/-- The value `a - b` in Lean's `Int`. Only used to check plumbing proofs. -/
def val (p : MyNat × MyNat) : Int := (toNat p.1 : Int) - (toNat p.2 : Int)

theorem rel_iff (p q : MyNat × MyNat) : Rel p q ↔ val p = val q := by
  unfold Rel val
  constructor
  · intro h
    have h' := congrArg toNat h
    rw [toNat_add, toNat_add] at h'
    omega
  · intro h
    apply toNat_inj
    rw [toNat_add, toNat_add]
    omega

instance setoid : Setoid (MyNat × MyNat) where
  r := Rel
  iseqv := {
    refl := fun p => (rel_iff p p).2 rfl
    symm := fun {p q} h => (rel_iff q p).2 ((rel_iff p q).1 h).symm
    trans := fun {p q r} h₁ h₂ => (rel_iff p r).2 (((rel_iff p q).1 h₁).trans ((rel_iff q r).1 h₂)) }

end MyInt

/-- Our integers: pairs of naturals `(a, b)`, read as `a - b`, up to `a + d = c + b`. -/
def MyInt : Type := Quotient MyInt.setoid

/-- `ℤ` is our `MyInt`. -/
notation (name := MyIntNotation) (priority := 1000000) "ℤ" => MyInt

namespace MyInt

open MyNat (toNat toNat_add toNat_mul toNat_inj)

/-- `mk a b` is the integer `a - b`. -/
def mk (a b : MyNat) : MyInt := Quotient.mk setoid (a, b)

theorem sound {a b c d : MyNat} (h : val (a, b) = val (c, d)) : mk a b = mk c d :=
  Quotient.sound ((rel_iff (a, b) (c, d)).2 h)

theorem ind {P : MyInt → Prop} (h : ∀ a b : MyNat, P (mk a b)) (x : MyInt) : P x :=
  Quotient.ind (fun p => h p.1 p.2) x

theorem exists_mk (x : MyInt) : ∃ a b : MyNat, x = mk a b :=
  ind (P := fun x => ∃ a b : MyNat, x = mk a b) (fun a b => ⟨a, b, rfl⟩) x

theorem mk_eq (a b c d : MyNat) : mk a b = mk c d ↔ a + d = c + b :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

instance instOfNat (n : Nat) : OfNat MyInt n := ⟨mk (MyNat.ofNat n) 0⟩

theorem zero_def : (0 : MyInt) = mk 0 0 := rfl

theorem one_def : (1 : MyInt) = mk 1 0 := rfl

theorem val_add (p q : MyNat × MyNat) : val (p.1 + q.1, p.2 + q.2) = val p + val q := by
  simp only [val, toNat_add, Int.natCast_add]
  omega

theorem val_neg (p : MyNat × MyNat) : val (p.2, p.1) = - val p := by
  simp only [val]
  omega

theorem val_mul (p q : MyNat × MyNat) :
    val (p.1 * q.1 + p.2 * q.2, p.1 * q.2 + p.2 * q.1) = val p * val q := by
  simp only [val, toNat_add, toNat_mul, Int.natCast_add, Int.natCast_mul]
  rw [Int.sub_mul, Int.mul_sub, Int.mul_sub]
  omega

/-- Addition: `(a - b) + (c - d) = (a + c) - (b + d)`. -/
def add (x y : MyInt) : MyInt :=
  Quotient.lift₂ (fun p q => mk (p.1 + q.1) (p.2 + q.2))
    (fun p q p' q' hp hq => sound (by
      rw [val_add, val_add, (rel_iff p p').1 hp, (rel_iff q q').1 hq])) x y

/-- Negation: `-(a - b) = b - a`. -/
def neg (x : MyInt) : MyInt :=
  Quotient.lift (fun p => mk p.2 p.1)
    (fun p q h => sound (by rw [val_neg, val_neg, (rel_iff p q).1 h])) x

/-- Multiplication: `(a - b)(c - d) = (ac + bd) - (ad + bc)`. -/
def mul (x y : MyInt) : MyInt :=
  Quotient.lift₂ (fun p q => mk (p.1 * q.1 + p.2 * q.2) (p.1 * q.2 + p.2 * q.1))
    (fun p q p' q' hp hq => sound (by
      rw [val_mul, val_mul, (rel_iff p p').1 hp, (rel_iff q q').1 hq])) x y

instance : Add MyInt := ⟨add⟩
instance : Neg MyInt := ⟨neg⟩
instance : Mul MyInt := ⟨mul⟩
instance : Sub MyInt := ⟨fun x y => x + -y⟩

theorem mk_add_mk (a b c d : MyNat) : mk a b + mk c d = mk (a + c) (b + d) := rfl

theorem neg_mk (a b : MyNat) : -mk a b = mk b a := rfl

theorem mk_mul_mk (a b c d : MyNat) :
    mk a b * mk c d = mk (a * c + b * d) (a * d + b * c) := rfl

theorem sub_eq_add_neg (x y : MyInt) : x - y = x + -y := rfl

attribute [irreducible] add neg mul

/-- `x ≤ y` means: `y = x + c` for some natural number `c`. -/
def le (x y : MyInt) : Prop := ∃ c : MyNat, y = x + mk c 0

instance : LE MyInt := ⟨le⟩

theorem le_iff (x y : MyInt) : x ≤ y ↔ ∃ c : MyNat, y = x + mk c 0 := Iff.rfl

end MyInt
