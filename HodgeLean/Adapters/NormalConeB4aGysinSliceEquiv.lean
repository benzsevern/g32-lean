import HodgeLean.Adapters.NormalConeB2Cycle
import HodgeLean.Adapters.NormalConeB4aGysinBridgeDefs

noncomputable section
namespace HodgeLean.Adapters

/-- A ring equivalence preserves the length of a quotient by a finite list,
including its module structure over the original ring. -/
theorem a3b4a_gysin_slice_length_ringEquiv
    {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) (xs : List R) :
    Module.length R (R ⧸ Ideal.ofList xs) =
      Module.length S (S ⧸ Ideal.ofList (xs.map e)) := by
  let I := Ideal.ofList xs
  let J := Ideal.ofList (xs.map e)
  let E : (R ⧸ I) ≃+* (S ⧸ J) := Ideal.quotientEquiv I J e (by
    rw [Ideal.map_ofList]
    rfl)
  calc
    Module.length R (R ⧸ I) = Module.length (R ⧸ I) (R ⧸ I) :=
      Module.length_eq_of_surjective Ideal.Quotient.mk_surjective
    _ = Module.length (S ⧸ J) (S ⧸ J) := a3b2_length_eq_of_ringEquiv E
    _ = Module.length S (S ⧸ J) :=
      (Module.length_eq_of_surjective Ideal.Quotient.mk_surjective).symm

end HodgeLean.Adapters
