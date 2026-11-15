import HodgeLean.Foundations.Program.UniversalFamilyB60cPullbackRiemann

noncomputable section
open scoped TensorProduct
open HodgeLean.Papers HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- An action-compatible homology marking exchanges the signs of the Weil eigenvalues. -/
theorem b60c_marking_eigenspaces (P : g32t_Sixfold)
    (g : (ℂ ⊗[ℤ] b60_Lattice) ≃ₗ[ℂ] (ℂ ⊗[ℚ] HQ P.X 1))
    (hJ : ∀ x, g (b60_omegaC x) = -(P.W.J.baseChange ℂ) (g x)) (r : ℂ) :
    (Module.End.eigenspace b60_omegaC (-r)).map g.toLinearMap =
      Module.End.eigenspace (P.W.J.baseChange ℂ) r := by
  ext y
  simp only [Submodule.mem_map, Module.End.mem_eigenspace_iff, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hi := hJ x
    rw [hx, map_smul] at hi
    apply neg_injective
    simpa only [neg_smul] using hi.symm
  · intro hy
    refine ⟨g.symm y, ?_, g.apply_symm_apply y⟩
    apply g.injective
    rw [hJ, map_smul, g.apply_symm_apply, hy]
    simp only [neg_smul]

#print axioms b60c_marking_eigenspaces

end HodgeLean.Foundations.Program
