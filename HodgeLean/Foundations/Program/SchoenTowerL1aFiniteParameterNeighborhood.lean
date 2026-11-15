import HodgeLean.Foundations.Program.SchoenTowerL1aPrescribedEtale
import HodgeLean.Foundations.Program.SchoenTowerL1aMorphismParameters

/-! # Actual finite-support etale parameter neighborhoods

Implication from the smooth affine curve to an affine etale parameter
neighborhood retaining any finite support and its prescribed values.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program
attribute [local instance] overSpecAlgebra

/-- Prescribed finite values are realized by an actual etale affine parameter neighborhood of a smooth affine curve.
Source: Stacks Project, tag 054L; Atiyah–Macdonald, Introduction to Commutative Algebra, Proposition 1.10. -/
theorem s2v_l1a_finite_parameter_neighborhood
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsAffine X.left] [Smooth X.hom]
    [SmoothOfRelativeDimension 1 X.hom]
    {ι : Type} [Finite ι] [Nonempty ι]
    (p : ι → ComplexPoint X) (hp : Function.Injective p) (c : ι → ℂ) :
    ∃ (U : Over (Spec ↧ℂ)) (hU : IsAffine U.left) (u : U ⟶ X)
      (y : ι → ComplexPoint U) (z : Γ(U.left, ⊤)),
      IsOpenImmersion u.left ∧ (∀ i, Point.map u (y i) = p i) ∧
      (MvPolynomial.eval₂Hom U.hom.appTop.hom (fun _ : Fin 1 => z)).Etale ∧
      (∀ i, Point.evaluate ⊤ z (y i) = c i) := by
  classical
  obtain ⟨g, r, hg, hr, hEt⟩ := s2v_l1a_affine_curve_prescribed_etale_section X p hp c
  let i₀ : ι := Classical.arbitrary ι
  obtain ⟨f, hf, hvalue⟩ := s2t_principal_etale_coordinate X g r (p i₀)
    (by rw [hr]; exact one_ne_zero) hEt
  let O := X.left.basicOpen r
  let U := openScheme X O
  let u : U ⟶ X := openInclusion X O
  have hmem (i : ι) : (p i).underlying ∈ O :=
    (Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero r (p i)
      (show p i ∈ Point.overOpen ⊤ from trivial)).mpr (by rw [hr]; exact one_ne_zero)
  let y (i : ι) : ComplexPoint U := asOpenPoint X O (p i) (hmem i)
  letI : IsAffine U.left := (isAffineOpen_top X.left).basicOpen r
  letI : Etale f.left := hf
  let z : Γ(U.left, ⊤) := f.left.appTop
    ((s2t_affineSpacePolynomialEquiv (Fin 1)) (MvPolynomial.X 0))
  have hcoord : (s2t_affineSpacePolynomialEquiv (Fin 1)) (MvPolynomial.X 0) =
      AffineSpace.coord (Spec ↧ℂ) (0 : Fin 1) := SpecIso_hom_appTop_X 0
  have hpoly := s2v_l1a_affineSpace_section_polynomial_etale U (Fin 1) f
  have hpoly' : (MvPolynomial.eval₂Hom (algebraMap ℂ Γ(U.left, ⊤))
      (fun _ : Fin 1 => z)).Etale := by
    have hzfun : (fun _ : Fin 1 => z) =
        (fun i => f.left.appTop ((s2t_affineSpacePolynomialEquiv (Fin 1)) (MvPolynomial.X i))) := by
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      rfl
    rw [hzfun]
    exact hpoly
  have hcoeff := s2v_l1a_etale_eval_change_coefficients
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv
    (algebraMap ℂ Γ(U.left, ⊤)) (fun _ : Fin 1 => z) hpoly'
  refine ⟨U, inferInstance, u, y, z, inferInstanceAs (IsOpenImmersion O.ι), ?_, ?_, ?_⟩
  · intro i
    apply Over.OverMorphism.ext
    exact liftToOpen_fac X O (p i) (hmem i)
  · have hcoef : U.hom.appTop.hom = (algebraMap ℂ Γ(U.left, ⊤)).comp
        (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv.toRingHom := by
      ext k
      change U.hom.appTop.hom k =
        U.hom.appLE ⊤ ⊤ (by simp) ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
          ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom k))
      rw [Iso.hom_inv_id_apply]
      simp only [Scheme.Hom.appLE, TopologicalSpace.Opens.map_top, homOfLE_refl, op_id,
        U.left.presheaf.map_id, Category.comp_id]
    rw [hcoef]
    exact hcoeff
  · intro i
    change Point.evaluate ⊤ (f.left.appTop _) (y i) = _
    rw [hcoord, evaluate_top_eq_appTop]
    change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
      ((y i).left.appTop (f.left.appTop (AffineSpace.coord (Spec ↧ℂ) (0 : Fin 1)))) = _
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop]
    change affineSpaceEquiv (Fin 1) (Point.map f (y i)) 0 = _
    rw [hvalue]
    have hy : Point.map u (y i) = p i := by
      apply Over.OverMorphism.ext
      exact liftToOpen_fac X O (p i) (hmem i)
    rw [hy, hg]

end HodgeLean.Foundations.Program
