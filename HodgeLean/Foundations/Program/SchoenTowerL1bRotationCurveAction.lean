import HodgeLean.Foundations.Program.SchoenTowerL1bRotationResidueKernel
import HodgeLean.Foundations.Program.SchoenTowerL1bRotationStalkComposition

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- An actual finite curve action at a fixed point has a scalar-preserving
formal parameter expansion intertwining its stalk action with a root rescaling. -/
theorem s2v_l1b_rotation_curve_action_expansion
    {G : Type*} [Monoid G] (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (hdim : TopologicalSpace.dim X.left = 1)
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (g : G) (p : ComplexPoint X) (hp : (a g).left p.underlying = p.underlying)
    (N : ℕ) (hN : 0 < N) (hgN : g ^ N = 1) :
    ∃ ζ : ℂ, ζ ^ N = 1 ∧
      ∃ ι : X.left.presheaf.stalk p.underlying →+* PowerSeries ℂ,
        Function.Injective ι ∧ (∃ u, ι u = PowerSeries.X) ∧
        (∀ c : ℂ, ι (HodgeLean.Foundations.Curves.stalkC p.underlying c) = PowerSeries.C c) ∧
        ∀ v, ι (s2e_fixed_point_stalkPullback X.left (a g).left p.underlying hp v) =
          PowerSeries.rescale ζ (ι v) := by
  letI : SmoothOfRelativeDimension 1 X.hom := by
    simpa only [hdim] using
      (inferInstance : SmoothOfRelativeDimension (TopologicalSpace.dim X.left) X.hom)
  let R := X.left.presheaf.stalk p.underlying
  letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC p.underlying).toAlgebra
  obtain ⟨ι, u, hι, hu, hlocal, hker⟩ := s2v_l1b_rotation_curve_expansion_kernel X p
  letI := hlocal
  let β := s2e_fixed_point_stalkPullback X.left (a g).left p.underlying hp
  let τ : R →ₐ[ℂ] R :=
    { toRingHom := β
      commutes' := s2e_fixed_point_stalkPullback_scalars X (a g) p.underlying hp }
  letI : IsLocalHom (X.left.presheaf.stalkCongr (.of_eq hp)).inv.hom :=
    isLocalHom_of_iso (X.left.presheaf.stalkCongr (.of_eq hp)).symm
  letI : IsLocalHom τ.toRingHom := inferInstanceAs
    (IsLocalHom ((X.left.presheaf.stalkCongr (.of_eq hp)).inv ≫
      (a g).left.stalkMap p.underlying).hom)
  have hperiod : τ^[N] u = u :=
    s2v_l1b_rotation_action_stalk_periodic X a ha1 hamul g p.underlying hp N hgN u
  have hc (c : ℂ) : ι (algebraMap ℂ R c) = PowerSeries.C c := ι.commutes c
  have hres := s2v_l1b_rotation_residue_invariant
    (PowerSeries.constantCoeff.comp ι.toRingHom)
    (fun c => by change PowerSeries.constantCoeff (ι (algebraMap ℂ R c)) = c
                 rw [hc, PowerSeries.constantCoeff_C]) τ
  refine ⟨PowerSeries.coeff 1 (ι (τ u)),
    s2v_l1b_rotation_tangent_pow ι u hu hker τ hres N hperiod, ?_⟩
  exact s2v_l1b_rotation_local_linearization ι hι u hu hker τ N hN hperiod

end HodgeLean.Foundations.Program
