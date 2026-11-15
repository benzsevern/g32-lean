import HodgeLean.Foundations.Program.SchoenCycleMappedCotangentEquiv

/-! # Quotient-scalar transport of the original ideal cotangent module -/
noncomputable section
set_option maxHeartbeats 200000
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- A ring equivalence transports the actual ideal cotangent module
semilinearly over its induced equivalence of quotient coefficient rings. -/
def pairedC3CotangentRingEquiv {A B : Type*} [CommRing A] [CommRing B]
    (I : Ideal A) (e : A ≃+* B) :
    let q := Ideal.quotientEquiv I (I.map e.toRingHom) e rfl
    haveI := RingHomInvPair.of_ringEquiv q
    haveI := RingHomInvPair.of_ringEquiv_symm q
    I.Cotangent ≃ₛₗ[(q : A ⧸ I →+* B ⧸ I.map e.toRingHom)]
      (I.map e.toRingHom).Cotangent := by
  let q := Ideal.quotientEquiv I (I.map e.toRingHom) e rfl
  letI := RingHomInvPair.of_ringEquiv q
  letI := RingHomInvPair.of_ringEquiv_symm q
  letI : Algebra A B := e.toRingHom.toAlgebra
  let ea : A ≃ₐ[A] B := AlgEquiv.ofRingEquiv (f := e) (by intro a; rfl)
  let f := s2e_mapped_ideal_cotangent_equiv (R := A) I ea
  refine { f.toEquiv with map_add' := f.map_add, map_smul' := ?_ }
  intro c x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
  change f (a • x) = a • f x
  exact f.map_smul a x


/-- The quotient-scalar transport preserves each original represented ideal class. -/
theorem paired_c3_cotangent_ring_equiv_toCotangent
    {A B : Type*} [CommRing A] [CommRing B] (I : Ideal A) (e : A ≃+* B) (x : I) :
    pairedC3CotangentRingEquiv I e (I.toCotangent x) =
      (I.map e.toRingHom).toCotangent
        ⟨e x.val, Ideal.mem_map_of_mem e.toRingHom x.property⟩ := rfl

#print axioms paired_c3_cotangent_ring_equiv_toCotangent
#print axioms pairedC3CotangentRingEquiv
end HodgeLean.Foundations.Program.G32Native
