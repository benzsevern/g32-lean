import HodgeLean.Foundations.Program.G32Native.PELReferenceLieCenter
import HodgeLean.Foundations.Program.G32Native.PELMultiplicityLieTransport
import HodgeLean.Foundations.Program.G32Native.PELMatrixTangentLie

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct Quaternion
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
namespace HodgeLean.Foundations.Program.GeneralTypeIII
open HodgeLean.Foundations.Abdulali

/-- The retained reference tangent Lie algebra has its orthogonal
multiplicity Lie equivalence, without a general-member premise.
Source: Abdulali, Annals of Mathematics 155 (2002), §§3.1–3.3;
Humphreys, Introduction to Lie Algebras and Representation Theory, §19. -/
theorem pel_reference_tangent_lie_equiv (R : PELSplitReference) :
    Nonempty (LieAlgebra.Orthogonal.so (Fin 6) ℂ ≃ₗ⁅ℂ⁆ pelMatrixTangentLie
      (pelIsometryGroup (R.form.map (algebraMap ℚ ℂ))
        (Set.range fun i : Fin 4 =>
          (R.operator (QuaternionAlgebra.basisOneIJK (-3 : ℚ) 0 R.b i)).map
            (algebraMap ℚ ℂ)))) := by
  letI := (torusCohomology_cupProductOf R.B.X).finite
  let E := polarizationForm (torusCohomology_cupProductOf R.B.X) R.polarized.nondegenerate
  let F := fun i : Fin 4 => (abelianEnd0Action R.B.X
    (R.end0 (QuaternionAlgebra.basisOneIJK (-3 : ℚ) 0 R.b i))).unop
  let c := Algebra.TensorProduct.basis ℂ R.basis
  let L := pelMatrixTangentLie
    (pelIsometryGroup (R.form.map (algebraMap ℚ ℂ))
      (Set.range fun i : Fin 4 =>
        (R.operator (QuaternionAlgebra.basisOneIJK (-3 : ℚ) 0 R.b i)).map (algebraMap ℚ ℂ)))
  have hform : LinearMap.toMatrix₂ c c (E.baseChange ℂ) =
      R.form.map (algebraMap ℚ ℂ) := by
    ext i j
    simp only [c, PELSplitReference.form, E, LinearMap.toMatrix₂_apply,
      Algebra.TensorProduct.basis_apply, LinearMap.BilinForm.baseChange_tmul,
      one_mul, Matrix.map_apply, Algebra.smul_def, mul_one]
  have ht := pelGenericGroup_tangent R.basis E F
  rw [hform] at ht
  simp only [LinearMap.toMatrix_baseChange] at ht
  rw [pelGenericGroup, g1_lie_identityComponent] at ht
  change L.toSubmodule = (complexSpan (skewCentralizerOfFamily E F)).map
    (LinearMap.toMatrix c c).toLinearMap at ht
  have hm (X : Module.End ℂ (ℂ ⊗[ℚ] HQ R.B.X 1)) :
      LinearMap.toMatrix c c X ∈ L ↔
        X ∈ complexSpan (skewCentralizerOfFamily E
          (fun i => pelReferenceQuaternionAction R
            (QuaternionAlgebra.basisOneIJK (-3 : ℚ) 0 R.b i))) := by
    change LinearMap.toMatrix c c X ∈ L.toSubmodule ↔ _
    rw [ht]
    have hi := (LinearMap.toMatrix c c).injective
    constructor
    · rintro ⟨Y, hY, hYX⟩
      have heq : Y = X := hi hYX
      subst Y
      dsimp only [E, F] at hY
      rwa [pel_reference_actual_skew_eq] at hY
    · intro hX
      refine ⟨X, ?_, rfl⟩
      dsimp only [E, F]
      rw [pel_reference_actual_skew_eq]
      exact hX
  obtain ⟨s, a, e, B, hs, ha, hI, hsym, hB, he, hformB, hn⟩ := pelReferenceMultiplicity R
  exact pel_multiplicity_lie_equiv c L e B hsym hB
    (fun X => (hm X).trans (hn X))

/-- Simplicity of the retained tangent algebra follows through the actual
multiplicity Lie equivalence. -/
theorem pel_reference_tangent_isSimple (R : PELSplitReference) :
    LieAlgebra.IsSimple ℂ (pelMatrixTangentLie
      (pelIsometryGroup (R.form.map (algebraMap ℚ ℂ))
        (Set.range fun i : Fin 4 =>
          (R.operator (QuaternionAlgebra.basisOneIJK (-3 : ℚ) 0 R.b i)).map
            (algebraMap ℚ ℂ)))) := by
  obtain ⟨e⟩ := pel_reference_tangent_lie_equiv R
  letI := pel_so6_isSimple_aux
  exact pel_simple_lieEquiv e

#print axioms pel_reference_tangent_lie_equiv
#print axioms pel_reference_tangent_isSimple
end HodgeLean.Foundations.Program.GeneralTypeIII
