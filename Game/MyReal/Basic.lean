import Game.Levels.Reals.L09_CloseTrans

/-!
# The real numbers `MyReal`

A real number is a Cauchy sequence of rationals, where close sequences count as the same.
That `Close` is an equivalence relation was proved by the player
(`close_refl`, `close_symm`, `close_trans`), so we can use those theorems here.
-/

/-- Cauchy sequences of rationals. -/
abbrev CauchySeq : Type := {s : MyNat → MyRat // MyRat.IsCauchy s}

namespace MyReal

instance setoid : Setoid CauchySeq where
  r s t := MyRat.Close s.1 t.1
  iseqv := ⟨fun s => MyRat.close_refl s.1, fun h => MyRat.close_symm _ _ h,
    fun h₁ h₂ => MyRat.close_trans _ _ _ h₁ h₂⟩

end MyReal

/-- Our real numbers: Cauchy sequences of rationals, up to `Close`. -/
def MyReal : Type := Quotient MyReal.setoid

/-- `ℝ` is our `MyReal`. -/
notation (name := MyRealNotation) (priority := 1000000) "ℝ" => MyReal

namespace MyReal

/-- The real number given by the Cauchy sequence `s`. -/
def ofSeq (s : MyNat → MyRat) (hs : MyRat.IsCauchy s) : MyReal := Quotient.mk setoid ⟨s, hs⟩

theorem ofSeq_eq {s t : MyNat → MyRat} {hs : MyRat.IsCauchy s} {ht : MyRat.IsCauchy t} :
    ofSeq s hs = ofSeq t ht ↔ MyRat.Close s t :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

theorem exists_ofSeq (x : MyReal) : ∃ (s : MyNat → MyRat) (hs : MyRat.IsCauchy s), x = ofSeq s hs :=
  Quotient.ind (motive := fun x => ∃ (s : MyNat → MyRat) (hs : MyRat.IsCauchy s), x = ofSeq s hs)
    (fun p => ⟨p.1, p.2, rfl⟩) x

end MyReal
