import HodgeLean.Foundations.QuotientDuality.RetainedFieldSourceChartOpen

/-! Coverage of the actual original-field normalization chart. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

theorem fieldSourceNormalizationChartMap_range
    (B : Over (Spec ↧ℂ)) {L : Type} [Field L]
    (η : Spec (CommRingCat.of L) ⟶ B.left) [QuasiCompact η] [QuasiSeparated η]
    (U : B.left.affineOpens) (hU : η ⁻¹ᵁ U.1 = ⊤) :
    letI : Algebra Γ(B.left, U) L :=
      (η.app U.1 ≫ (s2v_fieldSourceSectionsIso η U.1 hU).hom).hom.toAlgebra
    let N := integralClosure Γ(B.left, U) L
    letI : Algebra ℂ N := ((algebraMap Γ(B.left, U) N).comp
      (complexAffineCoefficient B U)).toAlgebra
    Set.range (fieldSourceNormalizationChartMap B η U hU).left =
      (η.fromNormalization ⁻¹ᵁ U.1 : Set η.normalization) := by
  let R := Γ(B.left, U)
  let A := Γ(Spec (CommRingCat.of L), η ⁻¹ᵁ U.1)
  letI : Algebra R A := (η.app U.1).hom.toAlgebra
  letI : Algebra R L :=
    (η.app U.1 ≫ (s2v_fieldSourceSectionsIso η U.1 hU).hom).hom.toAlgebra
  let N := integralClosure R L
  letI : Algebra ℂ N := ((algebraMap R N).comp (complexAffineCoefficient B U)).toAlgebra
  let e₀ : A ≃+* L := (s2v_fieldSourceSectionsIso η U.1 hU).commRingCatIsoToRingEquiv
  let e : A ≃ₐ[R] L := { e₀ with commutes' := fun _ => rfl }
  let E := e.mapIntegralClosure
  have hsurj : Function.Surjective (Spec.map (CommRingCat.ofHom E.toRingHom)) :=
    (PrimeSpectrum.homeomorphOfRingEquiv E.toRingEquiv).symm.surjective
  change Set.range ((η.normalizationOpenCover.f U) ∘
    (Spec.map (CommRingCat.ofHom E.toRingHom))) = _
  rw [Set.range_comp, Set.range_eq_univ.mpr hsurj, Set.image_univ]
  exact (congrArg (fun O : η.normalization.Opens => (O : Set η.normalization))
    (η.fromNormalization_preimage U)).symm

#print axioms fieldSourceNormalizationChartMap_range
end HodgeLean.Foundations.QuotientDuality
