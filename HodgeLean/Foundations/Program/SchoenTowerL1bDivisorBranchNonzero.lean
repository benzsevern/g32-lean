import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorEtaleCoordinates
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorNonzeroChart
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorIdealNonzero

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- A retained incidence ideal has a nonzero local equation at every complex point. -/
theorem s2v_l1b_divisor_branch_nonzero_equation
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
      ∃ g : Γ(B.left, U), (s2c_branchIdeal Z B h γ b).ideal U = Ideal.span {g} ∧ g ≠ 0 := by
  obtain ⟨z, hz⟩ := hγsurj x
  obtain ⟨A, V, hA, hV, u, v, q, hu, hv, hq, hsquare, ⟨p, hp⟩,
    ρ, zA, c, hρv, hρq, hqinj, hqimage, hEtV, hEtA, hc, hprod, hbranch, hzi⟩ :=
    s2v_l1a_pre_invariant_charts_aux Z B hdimZ h γ hγsurj hγinv hγ b z
  letI : IsAffine A.left := hA
  letI : IsOpenImmersion u.left := hu
  letI : Nonempty A.left := ⟨(Point.map q p).underlying⟩
  letI : IsIntegral A.left := isIntegral_of_isOpenImmersion u.left
  letI : Nonempty (⊤ : A.left.Opens) := ⟨⟨(Point.map q p).underlying, trivial⟩⟩
  have hcn : c (Fin.last h) ≠ 0 :=
    s2v_l1b_divisor_etale_coordinate_ne_zero A.hom.appTop.hom c hEtA (Fin.last h)
  obtain ⟨U, hU, g, hg, hgn⟩ := s2v_l1b_divisor_nonzero_equation_on_chart_image
    u.left (s2c_branchIdeal Z B h γ b) (c (Fin.last h)) hcn hbranch
  refine ⟨U, hU ?_, g, hg, hgn⟩
  have he : Point.map u (Point.map q p) = x := by
    rw [← Point.map_comp_apply, ← hsquare, Point.map_comp_apply, hp, hz]
  refine ⟨(Point.map q p).underlying, ?_⟩
  rw [← Point.underlying_map, he]

/-- Any supplied affine equation of an incidence ideal has nonzero germ. -/
theorem s2v_l1b_divisor_branch_germ_ne_zero
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
    (b : ComplexPoint Z) (x : ComplexPoint B)
    (V : B.left.affineOpens) (hx : x.underlying ∈ V.1) (g : Γ(B.left, V))
    (hg : (s2c_branchIdeal Z B h γ b).ideal V = Ideal.span {g}) :
    (B.left.presheaf.germ V.1 x.underlying hx).hom g ≠ 0 := by
  obtain ⟨W, hxW, a, ha, ha0⟩ :=
    s2v_l1b_divisor_branch_nonzero_equation Z B hdimZ h γ hγsurj hγinv hγ b x
  letI : Nonempty W.1 := ⟨⟨x.underlying, hxW⟩⟩
  apply s2v_l1b_divisor_ideal_generator_germ_ne_zero B.left
    (s2c_branchIdeal Z B h γ b) W a _ ha0 x.underlying V hx g hg
  rw [ha]
  exact Ideal.subset_span (Set.mem_singleton a)

end HodgeLean.Foundations.Program
