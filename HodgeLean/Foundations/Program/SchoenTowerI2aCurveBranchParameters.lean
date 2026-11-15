import HodgeLean.Foundations.Program.SchoenTowerL1aCurveParameter
import HodgeLean.Foundations.Program.SchoenTowerI2aSimultaneousNeighborhoods
import HodgeLean.Foundations.Program.SchoenTowerOverSections

/-! # Simultaneous branch parameters on the actual curve
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program
attribute [local instance] overSpecAlgebra

/-- All specified distinct curve points have their actual shifted point equations in one separating affine etale parameter neighborhood.
Source: Schoen (1988), Lemma 2.2, printed p. 13; Mathlib, affine localization and rational point ideals. -/
theorem s2v_i2a_simultaneous_curve_branch_parameters
    (Z : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (hdimZ : TopologicalSpace.dim Z.left = 1) (n : ℕ)
    (p : Fin (n + 1) → ComplexPoint Z) (hp : Function.Injective p) :
    ∃ (V : Over (Spec ↧ℂ)) (hV : IsAffine V.left) (v : V ⟶ Z)
      (y : Fin (n + 1) → ComplexPoint V) (z : Γ(V.left, ⊤)),
      IsOpenImmersion v.left ∧ (∀ i, Point.map v (y i) = p i) ∧
      (MvPolynomial.eval₂Hom V.hom.appTop.hom (fun _ : Fin 1 => z)).Etale ∧
      Function.Injective (fun i => Point.evaluate ⊤ z (y i)) ∧
      ∀ i, (((p i).left.ker).comap v.left).ideal ⟨⊤, @isAffineOpen_top V.left hV⟩ =
        Ideal.span {z - algebraMap ℂ Γ(V.left, ⊤) (Point.evaluate ⊤ z (y i))} := by
  classical
  obtain ⟨U, hU, u, y, z, hu, hy, hEt, hz0, hzsep⟩ :=
    s2v_l1a_projective_etale_support Z hdimZ n p
  letI : IsAffine U.left := hU
  letI : IsOpenImmersion u.left := hu
  letI : Smooth U.hom := by rw [← Over.w u]; infer_instance
  let A := Γ(U.left, ⊤)
  letI : Algebra.FiniteType ℂ A := s2t_globalSections_finiteType U
  let φ (i : Fin (n + 1)) := s2t_affinePointAlgHom U (y i)
  have hyinj : Function.Injective y := by
    intro i j hij
    apply hp
    rw [← hy i, ← hy j, hij]
  have hφinj : Function.Injective φ := (s2t_affinePointAlgHom_injective U).comp hyinj
  have hsep : Function.Injective (fun i => φ i z) := by
    intro i j hij
    by_contra hne
    apply hzsep i j (fun H => hne (hp H))
    simpa only [φ, s2t_affinePointAlgHom_apply] using hij
  have hcoef : U.hom.appTop.hom = (algebraMap ℂ A).comp
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv.toRingHom := by
    ext c
    change U.hom.appTop.hom c = U.hom.appLE ⊤ ⊤ (by simp)
      ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
        ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom c))
    rw [Iso.hom_inv_id_apply]
    simp only [Scheme.Hom.appLE, TopologicalSpace.Opens.map_top, homOfLE_refl,
      op_id, U.left.presheaf.map_id, Category.comp_id]
  have hEtC : (MvPolynomial.eval₂Hom (algebraMap ℂ A) (fun _ : Fin 1 => z)).Etale := by
    rw [hcoef] at hEt
    exact (s2v_l1a_etale_eval_change_coefficients_iff _ _ _).mp hEt
  obtain ⟨D, hD, hI⟩ := s2v_i2a_simultaneous_point_parameter_equations φ hφinj z
    (s2v_l1a_univariate_eval_etale z hEtC) hsep
  let O := U.left.basicOpen D
  let V := ComplexPoint.openScheme U O
  let w : V ⟶ U := ComplexPoint.openInclusion U O
  letI : IsOpenImmersion w.left := inferInstanceAs (IsOpenImmersion O.ι)
  letI : IsAffine V.left := (isAffineOpen_top U.left).basicOpen D
  have hmem (i : Fin (n + 1)) : (y i).underlying ∈ O :=
    (Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero D (y i) (show y i ∈ Point.overOpen ⊤ from trivial)).mpr
      (by rw [← s2t_affinePointAlgHom_apply, hD]; exact one_ne_zero)
  let a (i : Fin (n + 1)) : ComplexPoint V := ComplexPoint.asOpenPoint U O (y i) (hmem i)
  have ha (i : Fin (n + 1)) : Point.map w (a i) = y i := by
    apply Over.OverMorphism.ext
    exact ComplexPoint.liftToOpen_fac U O (y i) (hmem i)
  let z' := w.left.appTop.hom z
  have heval (i : Fin (n + 1)) : Point.evaluate ⊤ z' (a i) = φ i z := by
    calc
      Point.evaluate ⊤ z' (a i) = Point.evaluate ⊤ z (y i) := by
        rw [← s2v_l1a_pointSectionEvaluation_apply, ← s2v_l1a_pointSectionEvaluation_apply,
          ← ha i, s2v_l1a_pointSectionEvaluation_map]
        rfl
      _ = φ i z := (s2t_affinePointAlgHom_apply U (y i) z).symm
  refine ⟨V, inferInstance, w ≫ u, a, z',
    inferInstanceAs (IsOpenImmersion (w.left ≫ u.left)), ?_, ?_, ?_, ?_⟩
  · intro i
    change Point.map u (Point.map w (a i)) = p i
    rw [ha, hy]
  · have hw : w.left.appTop.hom.Etale := by
      simpa only [Scheme.Hom.appLE, TopologicalSpace.Opens.map_top, homOfLE_refl,
        op_id, V.left.presheaf.map_id, Category.comp_id, Scheme.Hom.appTop] using
        (Scheme.Hom.etale_appLE w.left (isAffineOpen_top _) (isAffineOpen_top _) le_top)
    have H := s2v_l1a_etale_ringHom_comp _ _ hEt hw
    have heq : w.left.appTop.hom.comp
        (MvPolynomial.eval₂Hom U.hom.appTop.hom (fun _ : Fin 1 => z)) =
        MvPolynomial.eval₂Hom V.hom.appTop.hom (fun _ : Fin 1 => z') := by
      apply MvPolynomial.ringHom_ext
      · intro c
        simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
        exact congrArg (fun f : V.left ⟶ Spec ↧ℂ => f.appTop.hom c) (Over.w w)
      · intro i
        simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
        rfl
    rw [heq] at H
    exact H
  · intro i j hij
    apply hsep
    simpa only [heval] using hij
  · intro i
    let B := Γ(V.left, ⊤)
    letI : Algebra A B := w.left.appTop.hom.toAlgebra
    letI : IsLocalization.Away D B := s2v_l1a_openScheme_sections_localization U.left D
    let e : Localization.Away D ≃ₐ[A] B := IsLocalization.algEquiv (Submonoid.powers D) _ _
    have heq : w.left.appTop.hom = e.toRingHom.comp (algebraMap A (Localization.Away D)) := by
      ext r
      exact (e.commutes r).symm
    have hker : RingHom.ker (φ i).toRingHom =
        (y i).left.ker.ideal ⟨⊤, isAffineOpen_top _⟩ := by
      rw [← s2v_l1a_pointSectionEvaluation_kernel]
      congr 1
      ext s
      rw [s2v_l1a_pointSectionEvaluation_apply]
      exact s2t_affinePointAlgHom_apply U (y i) s
    have hpoint : (y i).left ≫ u.left = (p i).left := congrArg (fun f : ComplexPoint Z => f.left) (hy i)
    change (((p i).left.ker).comap (w.left ≫ u.left)).ideal ⟨⊤, isAffineOpen_top _⟩ = _
    rw [Scheme.IdealSheafData.comap_comp]
    have hk : ((p i).left.ker).comap u.left = (y i).left.ker := by
      rw [← hpoint]
      exact s2v_l1a_open_kernel (y i).left u.left
    rw [hk, s2v_l1a_affine_ideal_pullback, ← hker, heq, ← Ideal.map_map, hI,
      Ideal.map_span, Set.image_singleton]
    apply congrArg Ideal.span
    apply congrArg (fun r : B => ({r} : Set B))
    change (e.toRingHom.comp (algebraMap A (Localization.Away D)))
      (z - algebraMap ℂ A (φ i z)) = _
    rw [← heq, map_sub, heval]
    exact congrArg (fun t => z' - t) ((s2t_overSectionsAlgHom w).commutes (φ i z))

end HodgeLean.Foundations.Program
