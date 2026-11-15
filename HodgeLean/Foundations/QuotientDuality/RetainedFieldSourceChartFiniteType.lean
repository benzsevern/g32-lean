import HodgeLean.Foundations.QuotientDuality.RetainedFieldSourceChartOpen

/-! Finite type of the actual original-field affine normalization chart. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

theorem fieldSourceNormalizationChart_finiteType
    (B : Over (Spec ↧ℂ)) {L : Type} [Field L]
    (η : Spec (CommRingCat.of L) ⟶ B.left) [QuasiCompact η] [QuasiSeparated η]
    [LocallyOfFiniteType (η.fromNormalization ≫ B.hom)]
    (U : B.left.affineOpens) (hU : η ⁻¹ᵁ U.1 = ⊤) :
    letI : Algebra Γ(B.left, U) L :=
      (η.app U.1 ≫ (s2v_fieldSourceSectionsIso η U.1 hU).hom).hom.toAlgebra
    let N := integralClosure Γ(B.left, U) L
    letI : Algebra ℂ N := ((algebraMap Γ(B.left, U) N).comp
      (complexAffineCoefficient B U)).toAlgebra
    Algebra.FiniteType ℂ N := by
  let R := Γ(B.left, U)
  letI : Algebra R L :=
    (η.app U.1 ≫ (s2v_fieldSourceSectionsIso η U.1 hU).hom).hom.toAlgebra
  let N := integralClosure R L
  letI : Algebra ℂ N := ((algebraMap R N).comp (complexAffineCoefficient B U)).toAlgebra
  let j := fieldSourceNormalizationChartMap B η U hU
  letI : IsOpenImmersion j.left := fieldSourceNormalizationChartMap_isOpenImmersion B η U hU
  have H : LocallyOfFiniteType (j.left ≫ (η.fromNormalization ≫ B.hom)) := inferInstance
  have hj := j.w
  change j.left ≫ (η.fromNormalization ≫ B.hom) =
    Spec.map (CommRingCat.ofHom (algebraMap ℂ N)) at hj
  rw [hj] at H
  exact RingHom.finiteType_algebraMap.mp (HasRingHomProperty.Spec_iff.mp H)

#print axioms fieldSourceNormalizationChart_finiteType
end HodgeLean.Foundations.QuotientDuality
