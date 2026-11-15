import HodgeLean.Foundations.Program.G32Native.EulerModel.CoordinateHyperplaneModels
import HodgeLean.Foundations.Program.G32Native.EulerModel.HyperplaneClass

/-! # Normalization on every literal native coordinate hyperplane -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.Foundations.Program HodgeLean.Adapters
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- Every literal native residue hyperplane is smooth, integral, has coheight one, and carries its normalized supported class. -/
theorem nativeResidueHyperplane_class (k : ℕ) (hk : 0 < k) (j : Fin (k + 1)) :
    let PP := Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))
    let I := s2e_s2b_residueIdeal k j
    let QI := s2c_subscheme PP I
    let jI := s2c_subschemeι PP I
    ∃ (hI : IsIntegral QI.left),
      letI := hI
      Smooth QI.hom ∧ Order.coheight (jI.left (genericPoint QI.left)) = 1 ∧
        ∃ c : s2e_supportedClass PP (s2e_componentCycle jI ℚ) 1,
          a3b4_IsCycleClass PP.hom (s2e_componentCycle jI ℚ) 1 c := by
  let PP := Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))
  let I := s2e_s2b_residueIdeal k j
  let QI := s2c_subscheme PP I
  let jI := s2c_subschemeι PP I
  let MP := Over.mk (ProjectiveSpace.toBase (Fin (k - 1 + 1)) (Spec ↧ℂ))
  letI : IsIntegral PP.left := IntersectionProductScaf_projective_integral k
  letI : Smooth PP.hom := IntersectionProductScaf_projective_smooth k
  letI : IsProjective PP.hom := ⟨⟨⟨k, 𝟙 _, Category.id_comp _⟩⟩⟩
  letI : IsIntegral MP.left := IntersectionProductScaf_projective_integral (k - 1)
  letI : Smooth MP.hom := IntersectionProductScaf_projective_smooth (k - 1)
  obtain ⟨E⟩ := residue_hyperplane_projective_model k hk j
  letI hI : IsIntegral QI.left := IsIntegral.of_isIso E.inv.left
  letI hsm : Smooth QI.hom := by
    rw [← Over.w E.hom]
    change Smooth (E.hom.left ≫ MP.hom)
    infer_instance
  letI : IsClosedImmersion jI.left := inferInstanceAs (IsClosedImmersion I.subschemeι)
  have hdimI := s2e_projective_model_dimension QI (k - 1) E
  have hdimP := s2e_projective_model_dimension PP k (Iso.refl PP)
  have hcod : Order.coheight (jI.left (genericPoint QI.left)) = 1 :=
    s2e_immersion_generic_coheight_of_dimensions jI (k - 1) 1 hdimI
      (by rw [hdimP]; omega)
  refine ⟨hI, hsm, hcod, ?_⟩
  apply a3b4a_cycleClass_exists_of_codimension
  intro x hx
  rw [s2e_componentCycle_support] at hx
  obtain rfl := Set.mem_singleton_iff.mp hx
  exact hcod.ge

#print axioms nativeResidueHyperplane_class
end HodgeLean.Foundations.Program.G32Native.EulerModel
