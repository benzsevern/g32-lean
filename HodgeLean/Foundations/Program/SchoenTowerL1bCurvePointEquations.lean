import HodgeLean.Foundations.Program.SchoenTowerL1bAffinePointEquations
import HodgeLean.Foundations.Program.SchoenTowerL1aCurveParameter

/-! # One curve parameter for simultaneous branch point equations

Every point in the specified finite support has its actual ideal equation
on the same affine etale parameter neighborhood, including repeated points.
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

/-- A finite tuple on a smooth projective curve has one separating etale parameter
whose translated equations generate every actual point ideal on the same affine open. -/
theorem s2v_l1b_simultaneous_curve_parameter
    (Z : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (hdimZ : TopologicalSpace.dim Z.left = 1)
    (n : ℕ) (p : Fin (n + 1) → ComplexPoint Z) :
    ∃ (U : Over (Spec ↧ℂ)) (hU : IsAffine U.left)
      (u : U ⟶ Z) (y : Fin (n + 1) → ComplexPoint U) (z : Γ(U.left, ⊤)),
      IsOpenImmersion u.left ∧ (∀ j, Point.map u (y j) = p j) ∧
      (MvPolynomial.eval₂Hom U.hom.appTop.hom (fun _ : Fin 1 => z)).Etale ∧
      (∀ j, (((p j).left.ker).comap u.left).ideal ⟨⊤, @isAffineOpen_top U.left hU⟩ =
        Ideal.span {z - U.hom.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
          (Point.evaluate ⊤ z (y j)))}) ∧
      (∀ j k, p j ≠ p k → Point.evaluate ⊤ z (y j) ≠ Point.evaluate ⊤ z (y k)) := by
  classical
  obtain ⟨U, hU, u, y, z, hu, hy, hEt, hz0, hzsep⟩ :=
    s2v_l1a_projective_etale_support Z hdimZ n p
  letI : IsAffine U.left := hU
  letI : IsOpenImmersion u.left := hu
  letI : Mono u := Over.mono_of_mono_left u
  letI : Smooth U.hom := by
    rw [← Over.w u]
    infer_instance
  have hcoef : U.hom.appTop.hom = (algebraMap ℂ Γ(U.left, ⊤)).comp
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv.toRingHom := by
    ext k
    change U.hom.appTop.hom k =
      U.hom.appLE ⊤ ⊤ (by simp) ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
        ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom k))
    rw [Iso.hom_inv_id_apply]
    simp only [Scheme.Hom.appLE, TopologicalSpace.Opens.map_top, homOfLE_refl, op_id,
      U.left.presheaf.map_id, Category.comp_id]
  have hEtC : (MvPolynomial.eval₂Hom (algebraMap ℂ Γ(U.left, ⊤))
      (fun _ : Fin 1 => z)).Etale := by
    rw [hcoef] at hEt
    exact (s2v_l1a_etale_eval_change_coefficients_iff _ _ _).mp hEt
  let κ := Set.range y
  letI : Fintype κ := (Set.finite_range y).fintype
  have hsep : Function.Injective (fun k : κ => Point.evaluate ⊤ z k.1) := by
    intro k l hkl
    apply Subtype.ext
    obtain ⟨j, hj⟩ := k.2
    obtain ⟨i, hi⟩ := l.2
    have hp : p j = p i := by
      by_contra hne
      exact hzsep j i hne (by simpa only [hj, hi] using hkl)
    have hyy : y j = y i := by
      apply (cancel_mono u).mp
      exact (hy j).trans (hp.trans (hy i).symm)
    exact hj.symm.trans (hyy.trans hi)
  obtain ⟨d, hd, hIdeal⟩ := s2v_l1b_affine_point_equations U
    (fun k : κ => k.1) Subtype.val_injective z
    (s2v_l1a_univariate_eval_etale z hEtC) hsep
  let O := U.left.basicOpen d
  let V := ComplexPoint.openScheme U O
  let w : V ⟶ U := ComplexPoint.openInclusion U O
  letI : IsOpenImmersion w.left := inferInstanceAs (IsOpenImmersion O.ι)
  have hmem (j : Fin (n + 1)) : (y j).underlying ∈ O :=
    (Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero d (y j)
      (show y j ∈ Point.overOpen ⊤ from trivial)).mpr
      (by rw [hd ⟨y j, ⟨j, rfl⟩⟩]; exact one_ne_zero)
  let a (j : Fin (n + 1)) : ComplexPoint V :=
    ComplexPoint.asOpenPoint U O (y j) (hmem j)
  have ha (j : Fin (n + 1)) : Point.map w (a j) = y j := by
    apply Over.OverMorphism.ext
    exact ComplexPoint.liftToOpen_fac U O (y j) (hmem j)
  letI : IsAffine V.left := (isAffineOpen_top U.left).basicOpen d
  let z' : Γ(V.left, ⊤) := w.left.appTop.hom z
  have heval (j : Fin (n + 1)) : Point.evaluate ⊤ z' (a j) =
      Point.evaluate ⊤ z (y j) := by
    rw [← s2v_l1a_pointSectionEvaluation_apply, ← s2v_l1a_pointSectionEvaluation_apply,
      ← ha j, s2v_l1a_pointSectionEvaluation_map]
    rfl
  refine ⟨V, inferInstance, w ≫ u, a, z',
    inferInstanceAs (IsOpenImmersion (w.left ≫ u.left)), ?_, ?_, ?_, ?_⟩
  · intro j
    change Point.map u (Point.map w (a j)) = p j
    rw [ha, hy]
  · have hw : w.left.appTop.hom.Etale := by
      simpa only [Scheme.Hom.appLE, TopologicalSpace.Opens.map_top, homOfLE_refl,
        op_id, V.left.presheaf.map_id, Category.comp_id, Scheme.Hom.appTop] using
        (Scheme.Hom.etale_appLE w.left (isAffineOpen_top _) (isAffineOpen_top _) le_top)
    have H := s2v_l1a_etale_ringHom_comp _ _ hEt hw
    have heq : (w.left.appTop.hom.comp
        (MvPolynomial.eval₂Hom U.hom.appTop.hom (fun _ : Fin 1 => z))) =
        MvPolynomial.eval₂Hom V.hom.appTop.hom (fun _ : Fin 1 => z') := by
      apply MvPolynomial.ringHom_ext
      · intro c
        simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
        exact congrArg (fun f : V.left ⟶ Spec ↧ℂ => f.appTop.hom c) (Over.w w)
      · intro j
        simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
        rfl
    rw [heq] at H
    exact H
  · intro j
    have hpoint : (y j).left ≫ u.left = (p j).left :=
      congrArg (fun f : ComplexPoint Z => f.left) (hy j)
    change (((p j).left.ker).comap (w.left ≫ u.left)).ideal ⟨⊤, isAffineOpen_top _⟩ = _
    rw [Scheme.IdealSheafData.comap_comp]
    have hk : ((p j).left.ker).comap u.left = (y j).left.ker := by
      rw [← hpoint]
      exact s2v_l1a_open_kernel (y j).left u.left
    rw [hk]
    have H := hIdeal ⟨y j, ⟨j, rfl⟩⟩
    rw [map_sub] at H
    rw [heval]
    have hc : w.left.appTop.hom (algebraMap ℂ Γ(U.left, ⊤)
        (Point.evaluate ⊤ z (y j))) = V.hom.appTop.hom
          ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
            (Point.evaluate ⊤ z (y j))) := by
      have Hc := congrArg (fun f : V.left ⟶ Spec ↧ℂ =>
        f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
          (Point.evaluate ⊤ z (y j)))) (Over.w w)
      simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        algebraMap, RingHom.comp_apply, Scheme.Hom.appTop, Scheme.Hom.appLE, TopologicalSpace.Opens.map_top,
        homOfLE_refl, op_id, U.left.presheaf.map_id, Category.comp_id] using Hc
    change ((y j).left.ker.comap w.left).ideal ⟨⊤, isAffineOpen_top _⟩ =
      Ideal.span {z' - w.left.appTop.hom (algebraMap ℂ Γ(U.left, ⊤)
        (Point.evaluate ⊤ z (y j)))} at H
    rw [hc] at H
    exact H
  · intro j k hjk
    rw [heval, heval]
    exact hzsep j k hjk

end HodgeLean.Foundations.Program
