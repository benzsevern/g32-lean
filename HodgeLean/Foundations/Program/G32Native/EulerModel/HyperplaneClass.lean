import HodgeLean.Foundations.Program.G32Native.EulerModel.Hyperplane
import HodgeLean.Foundations.Program.G32Native.EulerModel.ComponentClass
import HodgeLean.Adapters.IntersectionProductScaf

/-! # The normalized class of the specified coordinate hyperplane -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.Adapters HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The actual coordinate hyperplane is integral and has a normalized supported class. -/
theorem hyperplane_class (Q : Over (Spec ↧ℂ))
    [IsIntegral Q.left] [Smooth Q.hom] [IsProjective Q.hom]
    (k : ℕ) (hk : 0 < k)
    (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))) :
    let HI := (s2e_hyperplaneIdeal k).comap eQ.hom.left
    let QH := s2c_subscheme Q HI
    let jH := s2c_subschemeι Q HI
    ∃ (hH : IsIntegral QH.left),
      letI := hH
      ∃ cH : s2e_supportedClass Q (s2e_componentCycle jH ℚ) 1,
        a3b4_IsCycleClass Q.hom (s2e_componentCycle jH ℚ) 1 cH := by
  let HI := (s2e_hyperplaneIdeal k).comap eQ.hom.left
  let QH := s2c_subscheme Q HI
  let jH := s2c_subschemeι Q HI
  obtain ⟨E⟩ := coordinate_hyperplane_model eQ hk
  let PP := Over.mk (ProjectiveSpace.toBase (Fin (k - 1 + 1)) (Spec ↧ℂ))
  letI hyperplaneModelIntegral : IsIntegral PP.left :=
    IntersectionProductScaf_projective_integral (k - 1)
  letI hyperplaneIntegral : IsIntegral QH.left := IsIntegral.of_isIso E.inv.left
  letI hyperplaneModelSmooth : Smooth PP.hom :=
    IntersectionProductScaf_projective_smooth (k - 1)
  letI hyperplaneSmooth : Smooth QH.hom := by
    rw [← Over.w E.hom]
    change Smooth (E.hom.left ≫ PP.hom)
    infer_instance
  letI hyperplaneImmersion : IsClosedImmersion jH.left :=
    inferInstanceAs (IsClosedImmersion HI.subschemeι)
  have hQ := s2e_projective_model_dimension Q k eQ
  have hH := s2e_projective_model_dimension QH (k - 1) E
  have hdim : dim Q.left = (k - 1) + 1 := by rw [hQ]; omega
  refine ⟨hyperplaneIntegral, ?_⟩
  apply a3b4a_cycleClass_exists_of_codimension
  intro x hx
  rw [s2e_componentCycle_support] at hx
  obtain rfl := Set.mem_singleton_iff.mp hx
  exact (s2e_immersion_generic_coheight_of_dimensions jH (k - 1) 1 hH hdim).ge

#print axioms hyperplane_class
end HodgeLean.Foundations.Program.G32Native.EulerModel
