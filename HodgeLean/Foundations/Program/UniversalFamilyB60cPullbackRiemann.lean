import HodgeLean.Foundations.Program.UniversalFamilyB60cMemberFiltration

noncomputable section
open scoped TensorProduct
open HodgeLean.Papers HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- A real form-preserving complex marking transports a member's Riemann relations
to the fixed lattice. -/
theorem b60c_member_riemann_pullback (P : g32t_Sixfold) (hP : g32t_IsMember P)
    (g : (ℂ ⊗[ℤ] b60_Lattice) ≃ₗ[ℂ] (ℂ ⊗[ℚ] HQ P.X 1))
    (hE : ∀ x y, (polarizationForm (torusCohomology_cupProductOf P.X)
      hP.nondegenerate).baseChange ℂ (g x) (g y) = b60_E.baseChange ℂ x y)
    (hsigma : ∀ x, g (b2_conj b60_Lattice x) = HodgeBlocks.sigmaQ _ (g x)) :
    b2_IsRiemannForm b60_Lattice ((b60c_F P).comap g.toLinearMap) b60_E := by
  obtain ⟨pol, hpol⟩ := hP.positive
  refine ⟨b60_E_alt, ?_, ?_⟩
  · intro x hx y hy
    rw [← hE x y, ← hpol]
    exact pol.orthogonal 1 0 1 0 (by decide) (g x) hx (g y) hy
  · intro x hx hx0
    have hne : g x ≠ 0 := by simpa only [map_zero] using g.injective.ne hx0
    have hp := pol.positive 1 0 (by norm_num) (g x) hx hne
    rw [hpol, ← hsigma x, hE x (b2_conj b60_Lattice x)] at hp
    simpa only [HodgeBlocks.Iexp, sub_zero, zpow_one] using hp

#print axioms b60c_member_riemann_pullback

end HodgeLean.Foundations.Program
