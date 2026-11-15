import HodgeLean.Foundations.Program.SchoenTowerL1bBranchEquations
import HodgeLean.Foundations.Program.SchoenTowerL1bRegularNeighborhoods
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RingHom.Etale

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- An etale polynomial coordinate in a nontrivial ring is nonzero. -/
theorem s2v_l1b_etale_coordinate_ne_zero
    {k R J : Type*} [CommRing k] [CommRing R] [Nontrivial R]
    (f : k →+* R) (z : J → R) (het : (MvPolynomial.eval₂Hom f z).Etale)
    (j : J) : z j ≠ 0 := by
  letI : Algebra (MvPolynomial J k) R := (MvPolynomial.eval₂Hom f z).toAlgebra
  letI : Algebra.Etale (MvPolynomial J k) R := het
  have hr := Module.Flat.isSMulRegular_of_isRegular (M := R)
    (r := (MvPolynomial.X j : MvPolynomial J k)) MvPolynomial.isRegular_X
  intro hz
  have H : (MvPolynomial.X j : MvPolynomial J k) • (1 : R) =
      (MvPolynomial.X j : MvPolynomial J k) • (0 : R) := by
    simp only [Algebra.smul_def, show algebraMap (MvPolynomial J k) R
      (MvPolynomial.X j) = z j from MvPolynomial.eval₂Hom_X' f z j, hz, zero_mul]
  exact one_ne_zero (hr H)

/-- A principal equation transported from an affine chart retains nonvanishing. -/
theorem s2v_l1b_nonzero_principal_equation_on_chart_image
    {X Y : Scheme} [IsAffine X] (u : X ⟶ Y) [IsOpenImmersion u]
    (I : Y.IdealSheafData) (g : Γ(X, ⊤)) (hgn : g ≠ 0)
    (hg : (I.comap u).ideal ⟨⊤, isAffineOpen_top X⟩ = Ideal.span {g}) :
    ∃ V : Y.affineOpens, Set.range u ⊆ V.1 ∧
      ∃ a : Γ(Y, V), I.ideal V = Ideal.span {a} ∧ a ≠ 0 := by
  let V : Y.affineOpens := ⟨u ''ᵁ ⊤, (isAffineOpen_top X).image_of_isOpenImmersion u⟩
  refine ⟨V, ?_, (u.appIso ⊤).inv.hom g, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨x, trivial, rfl⟩
  · rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion] at hg
    have H := congrArg (Ideal.map (u.appIso ⊤).inv.hom) hg
    rw [Ideal.map_comap_of_surjective _
      (ConcreteCategory.bijective_of_isIso (u.appIso ⊤).inv).surjective,
      Ideal.map_span, Set.image_singleton] at H
    exact H
  · intro hz
    exact hgn ((ConcreteCategory.bijective_of_isIso (u.appIso ⊤).inv).injective
      (hz.trans (map_zero (u.appIso ⊤).inv.hom).symm))

/-- The original insertion branch has a nonzero local equation at every complex point. -/
theorem s2v_l1b_original_branch_nonzero_local_equation
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
      ∃ g : Γ(B.left, U), (s2c_branchIdeal Z B h γ b).ideal U = Ideal.span {g} ∧
        g ≠ 0 := by
  obtain ⟨z, hz⟩ := hγsurj x
  obtain ⟨A, V, hA, hV, u, v, q, hu, hv, hq, hsquare, ⟨p, hp⟩,
    ρ, zA, c, hρv, hρq, hqinj, hqimage, hEtV, hEtA, hc, hprod, hbranch, hzi⟩ :=
    s2v_l1a_pre_invariant_charts_aux Z B hdimZ h γ hγsurj hγinv hγ b z
  letI : IsAffine A.left := hA
  letI : IsOpenImmersion u.left := hu
  haveI : Nonempty (⊤ : A.left.Opens) := ⟨⟨(Point.map q p).underlying, trivial⟩⟩
  have hcn := s2v_l1b_etale_coordinate_ne_zero A.hom.appTop.hom c hEtA (Fin.last h)
  obtain ⟨U, hU, g, hg, hgn⟩ := s2v_l1b_nonzero_principal_equation_on_chart_image
    u.left (s2c_branchIdeal Z B h γ b) (c (Fin.last h)) hcn hbranch
  refine ⟨U, hU ?_, g, hg, hgn⟩
  have he : Point.map u (Point.map q p) = x := by
    rw [← Point.map_comp_apply, ← hsquare, Point.map_comp_apply, hp, hz]
  refine ⟨(Point.map q p).underlying, ?_⟩
  rw [← Point.underlying_map, he]

/-- Finitely many original total branch pullbacks have simultaneous nonzero equations. -/
theorem s2v_l1b_original_branches_nonzero_simultaneous_equations
    (Z B X : Over (Spec ↧ℂ))
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom] [IsIntegral X.left]
    (hdimZ : TopologicalSpace.dim Z.left = 1) (h : ℕ)
    (γ : g3_power Z (h + 1) ⟶ B) [IsFinite γ.left]
    (hγsurj : Function.Surjective (Point.map γ))
    (hγinv : ∀ τ, s2_permute Z (h + 1) τ ≫ γ = γ)
    (hγ : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Z (h + 1) ⟶ T),
      (∀ τ, s2_permute Z (h + 1) τ ≫ f = f) →
      ∃! u : B ⟶ T, γ ≫ u = f)
    {J : Type*} [Finite J] (b : J → ComplexPoint Z)
    (f : X ⟶ B) [IsDominant f.left] [QuasiCompact f.left]
    (x : ComplexPoint X) (V : X.left.Opens) (hxV : x.underlying ∈ V) :
    ∃ U : X.left.affineOpens, x.underlying ∈ U.1 ∧ U.1 ≤ V ∧
      ∃ g : J → Γ(X.left, U),
        ∀ j, ((s2c_branchIdeal Z B h γ (b j)).comap f.left).ideal U =
          Ideal.span {g j} ∧ g j ≠ 0 := by
  apply s2v_l1b_simultaneous_nonzero_principal_neighborhood X.left
    (fun j => (s2c_branchIdeal Z B h γ (b j)).comap f.left) x.underlying V hxV
  intro j
  apply s2v_l1b_local_nonzero_principal_pullback f.left (s2c_branchIdeal Z B h γ (b j))
    x.underlying
  simpa only [Point.underlying_map] using
    s2v_l1b_original_branch_nonzero_local_equation Z B hdimZ h γ hγsurj hγinv hγ
      (b j) (Point.map f x)

end HodgeLean.Foundations.Program
