import HodgeLean.Foundations.Program.SchoenTowerL1bPrincipalChart
import HodgeLean.Foundations.Program.SchoenTowerL1aPreProofs
import HodgeLean.Foundations.Program.SchoenTowerL1bPullbackEquations
import HodgeLean.Foundations.Program.SchoenTowerL1bPrincipalNeighborhoods

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The retained symmetric quotient has a local principal branch equation at each complex point. -/
theorem s2v_l1b_original_branch_local_equation
    (Z B : Over (Spec ↧ℂ))
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (hdimZ : TopologicalSpace.dim Z.left = 1) (h : ℕ)
    (γ : g3_power Z (h + 1) ⟶ B) [IsFinite γ.left]
    (hγsurj : Function.Surjective (Point.map γ))
    (hγinv : ∀ τ, s2_permute Z (h + 1) τ ≫ γ = γ)
    (hγ : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Z (h + 1) ⟶ T),
      (∀ τ, s2_permute Z (h + 1) τ ≫ f = f) →
      ∃! u : B ⟶ T, γ ≫ u = f)
    (b : ComplexPoint Z) (x : ComplexPoint B) :
    ∃ U : B.left.affineOpens, x.underlying ∈ U.1 ∧
      ∃ g : Γ(B.left, U), (s2c_branchIdeal Z B h γ b).ideal U = Ideal.span {g} := by
  obtain ⟨z, hz⟩ := hγsurj x
  obtain ⟨A, V, hA, hV, u, v, q, hu, hv, hq, hsquare, ⟨p, hp⟩,
    ρ, zA, c, hρv, hρq, hqinj, hqimage, hEtV, hEtA, hc, hprod, hbranch, hzi⟩ :=
    s2v_l1a_pre_invariant_charts_aux Z B hdimZ h γ hγsurj hγinv hγ b z
  let : IsAffine A.left := hA
  let : IsOpenImmersion u.left := hu
  obtain ⟨U, hU, g, hg⟩ := s2v_l1b_principal_equation_on_chart_image
    u.left (s2c_branchIdeal Z B h γ b) (c (Fin.last h)) hbranch
  refine ⟨U, hU ?_, g, hg⟩
  have he : Point.map u (Point.map q p) = x := by
    rw [← Point.map_comp_apply, ← hsquare, Point.map_comp_apply, hp, hz]
  refine ⟨(Point.map q p).underlying, ?_⟩
  rw [← Point.underlying_map, he]

/-- All original branch total pullbacks have equations on one prescribed affine neighborhood. -/
theorem s2v_l1b_original_branches_simultaneous_equations
    (Z B X : Over (Spec ↧ℂ))
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (hdimZ : TopologicalSpace.dim Z.left = 1) (h : ℕ)
    (γ : g3_power Z (h + 1) ⟶ B) [IsFinite γ.left]
    (hγsurj : Function.Surjective (Point.map γ))
    (hγinv : ∀ τ, s2_permute Z (h + 1) τ ≫ γ = γ)
    (hγ : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Z (h + 1) ⟶ T),
      (∀ τ, s2_permute Z (h + 1) τ ≫ f = f) →
      ∃! u : B ⟶ T, γ ≫ u = f)
    {J : Type*} [Finite J] (b : J → ComplexPoint Z)
    (f : X ⟶ B) (x : ComplexPoint X) (V : X.left.Opens) (hxV : x.underlying ∈ V) :
    ∃ U : X.left.affineOpens, x.underlying ∈ U.1 ∧ U.1 ≤ V ∧
      ∃ g : J → Γ(X.left, U),
        ∀ j, ((s2c_branchIdeal Z B h γ (b j)).comap f.left).ideal U = Ideal.span {g j} := by
  apply s2v_l1b_simultaneous_principal_neighborhood X.left
    (fun j => (s2c_branchIdeal Z B h γ (b j)).comap f.left) x.underlying V hxV
  intro j
  apply s2v_l1b_local_principal_pullback f.left (s2c_branchIdeal Z B h γ (b j)) x.underlying
  simpa only [Point.underlying_map] using
    s2v_l1b_original_branch_local_equation Z B hdimZ h γ hγsurj hγinv hγ
      (b j) (Point.map f x)

end HodgeLean.Foundations.Program
