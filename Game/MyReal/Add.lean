import Game.Levels.Reals.L11_CloseAdd

/-!
# Addition of real numbers

Defined term by term on sequences. The player proved that the sum is Cauchy (`add_cauchy`)
and does not depend on the chosen sequences (`close_add`).
-/

namespace MyReal

/-- Addition of reals: add the sequences term by term. -/
def add (x y : MyReal) : MyReal :=
  Quotient.lift₂ (fun s t => ofSeq (MyRat.addSeq s.1 t.1) (MyRat.add_cauchy s.1 t.1 s.2 t.2))
    (fun s t s' t' hs ht => Quotient.sound (MyRat.close_add s.1 s'.1 t.1 t'.1 hs ht)) x y

instance : Add MyReal := ⟨add⟩

theorem ofSeq_add {s t : MyNat → MyRat} {hs : MyRat.IsCauchy s} {ht : MyRat.IsCauchy t} :
    ofSeq s hs + ofSeq t ht = ofSeq (MyRat.addSeq s t) (MyRat.add_cauchy s t hs ht) := rfl

attribute [irreducible] add

end MyReal
