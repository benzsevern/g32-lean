import HodgeLean.Foundations.Program.G32Native.PELGenericGroupEndomorphisms

noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
namespace HodgeLean.Foundations.Program.GeneralTypeIII

variable (A B : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
  [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
  [GrpObj B] [IsCommMonObj B] [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
local instance : Module.Finite ℚ (HQ A 1) := (torusCohomology_cupProductOf A).finite
local instance : Module.Finite ℚ (HQ B 1) := (torusCohomology_cupProductOf B).finite

/-- Containment of the exact reference Hodge group in a marked fibre group
suffices for the retained action to exhaust the fibre endomorphisms. -/
theorem containing_group_action_surjective
    {D : Type*} [Ring D] [Algebra ℚ D] {n : ℕ}
    (bA : Module.Basis (Fin n) ℚ (HQ A 1)) (bB : Module.Basis (Fin n) ℚ (HQ B 1))
    (rhoD : D →ₐ[ℚ] AbelianEnd0 A) (e : D ≃ₐ[ℚ] AbelianEnd0 B)
    (hfixed : ∀ d,
      LinearMap.toMatrix bA bA (abelianEnd0Action A (rhoD d)).unop =
        LinearMap.toMatrix bB bB (abelianEnd0Action B (e d)).unop)
    (hGroup : g2_hodgeGroup (latticeHodgePieces B)
        (spec_latticeHodgePieces_isInternal B) bB ⊆
      g2_hodgeGroup (latticeHodgePieces A) (spec_latticeHodgePieces_isInternal A) bA) :
    Function.Surjective rhoD := by
  intro a
  let T := Matrix.toLin bB bB (LinearMap.toMatrix bA bA (abelianEnd0Action A a).unop)
  have hcA := (end0_range_iff_commutant A (abelianEnd0Action A a).unop).mp ⟨a, rfl⟩
  have hcM := (commutant_iff_group_tangent (latticeHodgePieces A)
    (spec_latticeHodgePieces_isInternal A) bA _).mp hcA
  have hcB := (commutant_iff_group_tangent (latticeHodgePieces B)
    (spec_latticeHodgePieces_isInternal B) bB T).mpr (by
      intro M hM
      simpa only [T, LinearMap.toMatrix_toLin] using hcM M (g1_lieOfSet_mono hGroup hM))
  obtain ⟨b, hb⟩ := (end0_range_iff_commutant B T).mpr hcB
  change (abelianEnd0Action B b).unop = T at hb
  refine ⟨e.symm b, ?_⟩
  apply spec_g4_abelianEnd0Action_injective A
  apply MulOpposite.unop_injective
  apply (LinearMap.toMatrix bA bA).injective
  rw [hfixed, e.apply_symm_apply, hb]
  exact LinearMap.toMatrix_toLin bB bB _


#print axioms containing_group_action_surjective
end HodgeLean.Foundations.Program.GeneralTypeIII
