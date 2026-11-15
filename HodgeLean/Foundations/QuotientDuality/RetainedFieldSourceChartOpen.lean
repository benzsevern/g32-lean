import HodgeLean.Foundations.QuotientDuality.RetainedFieldSourceChart

/-! Open immersion of each original-field normalization chart. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

theorem fieldSourceNormalizationChartMap_isOpenImmersion
    (B : Over (Spec ↧ℂ)) {L : Type} [Field L]
    (η : Spec (CommRingCat.of L) ⟶ B.left) [QuasiCompact η] [QuasiSeparated η]
    (U : B.left.affineOpens) (hU : η ⁻¹ᵁ U.1 = ⊤) :
    letI : Algebra Γ(B.left, U) L :=
      (η.app U.1 ≫ (s2v_fieldSourceSectionsIso η U.1 hU).hom).hom.toAlgebra
    let N := integralClosure Γ(B.left, U) L
    letI : Algebra ℂ N := ((algebraMap Γ(B.left, U) N).comp
      (complexAffineCoefficient B U)).toAlgebra
    IsOpenImmersion (fieldSourceNormalizationChartMap B η U hU).left := by
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
  change IsOpenImmersion
    (Spec.map (CommRingCat.ofHom E.toRingHom) ≫ η.normalizationOpenCover.f U)
  letI : IsIso (Spec.map (CommRingCat.ofHom E.toRingHom)) :=
    inferInstanceAs (IsIso (Scheme.Spec.mapIso E.toRingEquiv.toCommRingCatIso.op).hom)
  infer_instance

#print axioms fieldSourceNormalizationChartMap_isOpenImmersion
end HodgeLean.Foundations.QuotientDuality
