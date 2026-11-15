import HodgeLean.Foundations.QuotientDuality.RetainedFieldSourceChartFiniteType
import HodgeLean.Foundations.QuotientDuality.RetainedFieldSourceScalars
import HodgeLean.Foundations.QuotientDuality.MonomialNormalizationOrientation
import HodgeLean.Foundations.Program.SchoenCycleC1FieldSourceGenericEmbedding

/-! Coherent orientations on actual original-field monomial normalization charts. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Foundations.Program
open scoped BigOperators
namespace HodgeLean.Foundations.QuotientDuality

theorem field_source_monomial_chart_orientation
    (B : Over (Spec ↧ℂ)) [IsIntegral B.left] {L : Type} [Field L]
    (η : Spec (CommRingCat.of L) ⟶ B.left) [IsDominant η] [QuasiCompact η] [QuasiSeparated η]
    [LocallyOfFiniteType (η.fromNormalization ≫ B.hom)]
    (U : B.left.affineOpens) [Nonempty U.1] (hU : η ⁻¹ᵁ U.1 = ⊤)
    (n m : ℕ) (hm : 0 < m) (z : Fin n → Γ(B.left, U))
    (hEt : (MvPolynomial.eval₂Hom (complexAffineCoefficient B U) z).Etale)
    (α : Fin n → ℕ) :
    letI : Algebra Γ(B.left, U) L :=
      (η.app U.1 ≫ (s2v_fieldSourceSectionsIso η U.1 hU).hom).hom.toAlgebra
    let N := integralClosure Γ(B.left, U) L
    letI : Algebra ℂ N := ((algebraMap Γ(B.left, U) N).comp
      (complexAffineCoefficient B U)).toAlgebra
    ∀ (ε : Γ(B.left, U)ˣ) (v : L),
      v ^ m = algebraMap Γ(B.left, U) L (ε : Γ(B.left, U)) *
        ∏ i, (algebraMap Γ(B.left, U) L (z i)) ^ α i →
      Subfield.closure (Set.range (algebraMap Γ(B.left, U) L) ∪ {v}) = ⊤ →
      Nonempty (LocalRationalOrientation
        (TopCat.of (ComplexPoint (Over.mk (affineSpecStructureMap N)))) (2 * n)) := by
  let R := Γ(B.left, U)
  letI : Algebra R L :=
    (η.app U.1 ≫ (s2v_fieldSourceSectionsIso η U.1 hU).hom).hom.toAlgebra
  let N := integralClosure R L
  letI : Algebra ℂ R := (complexAffineCoefficient B U).toAlgebra
  letI : Algebra ℂ L := ((algebraMap R L).comp (complexAffineCoefficient B U)).toAlgebra
  letI : IsScalarTower ℂ R L := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra ℂ N := ((algebraMap R N).comp (complexAffineCoefficient B U)).toAlgebra
  letI : Algebra.FiniteType ℂ N := fieldSourceNormalizationChart_finiteType B η U hU
  dsimp only
  intro ε v hv hgen
  obtain ⟨κ, hκinj, hκ⟩ := s2e_c1_field_source_generic_embedding L B.left η
  letI : IsFractionRing R B.left.functionField :=
    functionField_isFractionRing_of_isAffineOpen B.left U.1 U.2
  have hscalar := fieldSourceChart_scalar_eq_generic B.left η κ hκ U hU
  have hinj : Function.Injective (algebraMap R L) := by
    change Function.Injective (η.app U.1 ≫ (s2v_fieldSourceSectionsIso η U.1 hU).hom).hom
    rw [hscalar]
    exact κ.injective.comp (IsFractionRing.injective R B.left.functionField)
  let c : MvPolynomial (Fin n) ℂ →ₐ[ℂ] R := MvPolynomial.aeval z
  apply monomial_normalization_coherent_orientation R L n m hm c hEt hinj α
    (ε : R) ε.isUnit v ?_ hgen
  simpa only [c, MvPolynomial.aeval_X] using hv

#print axioms field_source_monomial_chart_orientation
end HodgeLean.Foundations.QuotientDuality
