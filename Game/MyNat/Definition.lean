/-!
# The natural numbers `MyNat`

We build our own natural numbers. We do not use Lean's `Nat` lemmas.

Addition and multiplication are defined by recursion on the second argument.
The defining equations (`add_zero`, `add_succ`, `mul_zero`, `mul_succ`) are theorems.
After that, `add` and `mul` are made irreducible, so `rfl` cannot do the work for you.
-/

universe u

/-- Our natural numbers: `0`, `succ 0`, `succ (succ 0)`, ... -/
inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat

attribute [pp_nodot] MyNat.succ

/-- `ℕ` is our `MyNat`. (Notation as in NNG4.) -/
notation (name := MyNatNotation) (priority := 1000000) "ℕ" => MyNat

namespace MyNat

instance : Inhabited MyNat := ⟨zero⟩

/-- Turn a numeral like `3` into `succ (succ (succ zero))`. -/
def ofNat : Nat → MyNat
  | 0 => zero
  | n + 1 => succ (ofNat n)

instance instOfNat (n : Nat) : OfNat MyNat n := ⟨ofNat n⟩

/-- Induction for `MyNat`, stated with `0` instead of `zero`. -/
@[elab_as_elim, induction_eliminator]
def rec' {motive : MyNat → Sort u} (zero : motive 0)
    (succ : (n : MyNat) → motive n → motive (MyNat.succ n)) : (t : MyNat) → motive t
  | .zero => zero
  | .succ n => succ n (rec' zero succ n)

/-- Case split for `MyNat`, stated with `0` instead of `zero`. -/
@[elab_as_elim, cases_eliminator]
def casesOn' {motive : MyNat → Sort u} (zero : motive 0)
    (succ : (n : MyNat) → motive (MyNat.succ n)) : (t : MyNat) → motive t
  | .zero => zero
  | .succ n => succ n

theorem zero_eq_0 : MyNat.zero = 0 := rfl

theorem one_eq_succ_zero : (1 : MyNat) = succ 0 := rfl

theorem succ_inj (a b : MyNat) : succ a = succ b → a = b := fun h => MyNat.succ.inj h

/-- `True` at `0`, `False` at a successor. Used to tell `0` and `succ a` apart. -/
def isZero : MyNat → Prop
  | .zero => True
  | .succ _ => False

theorem zero_ne_succ (a : MyNat) : (0 : MyNat) ≠ succ a :=
  fun h => Eq.mp (congrArg isZero h) trivial

/-- Addition, by recursion on the second argument. -/
def add : MyNat → MyNat → MyNat
  | a, .zero => a
  | a, .succ b => succ (add a b)

instance : Add MyNat := ⟨add⟩

theorem add_zero (a : MyNat) : a + 0 = a := rfl

theorem add_succ (a b : MyNat) : a + succ b = succ (a + b) := rfl

/-- Multiplication, by recursion on the second argument. -/
def mul : MyNat → MyNat → MyNat
  | _, .zero => zero
  | a, .succ b => add (mul a b) a

instance : Mul MyNat := ⟨mul⟩

theorem mul_zero (a : MyNat) : a * 0 = 0 := rfl

theorem mul_succ (a b : MyNat) : a * succ b = a * b + a := rfl

attribute [irreducible] add mul

/-- `a ≤ b` means: some `c` with `b = a + c`. -/
def le (a b : MyNat) : Prop := ∃ c : MyNat, b = a + c

instance : LE MyNat := ⟨le⟩

theorem le_iff_exists_add (a b : MyNat) : a ≤ b ↔ ∃ c : MyNat, b = a + c := Iff.rfl

end MyNat
