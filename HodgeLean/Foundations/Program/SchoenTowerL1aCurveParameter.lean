import HodgeLean.Foundations.Program.SchoenTowerGeometryDefs
import HodgeLean.Foundations.Program.SchoenTowerL1aProjectiveAffine
import HodgeLean.Foundations.Program.SchoenTowerL1aProjectiveCurveJets
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import HodgeLean.Foundations.Program.SchoenTowerL1aProjectiveEtaleSupport
import HodgeLean.Foundations.Program.SchoenTowerL1aAffinePointEquation
import HodgeLean.Foundations.Program.SchoenTowerL1aUnivariateEtale
import HodgeLean.Foundations.Program.SchoenTowerL1aOpenKernel
import HodgeLean.Foundations.Program.SchoenTowerL1aEtaleRestriction

/-! # Separating curve parameters for L1a

This interface isolates the curve parameter construction needed before the
ordered and symmetric chart maps. HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program
attribute [local instance] overSpecAlgebra

/-- A finite collection on the retained curve has a separating affine etale parameter
whose zero ideal is the first specified point.
Source: Schoen (1988), Lemma 2.2 and its proof, printed p. 13; Hartshorne, Algebraic Geometry, II.6, local parameters on a smooth curve. -/
theorem s2v_l1a_separating_curve_parameter_aux
    (Z : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (hdimZ : TopologicalSpace.dim Z.left = 1)
    (n : ℕ) (p : Fin (n + 1) → ComplexPoint Z) :
    ∃ (U : Over (Spec ↧ℂ)) (hU : IsAffine U.left)
      (u : U ⟶ Z) (y : Fin (n + 1) → ComplexPoint U) (z : Γ(U.left, ⊤)),
      IsOpenImmersion u.left ∧ (∀ j, Point.map u (y j) = p j) ∧
      (MvPolynomial.eval₂Hom U.hom.appTop.hom (fun _ : Fin 1 => z)).Etale ∧
      (((p 0).left.ker).comap u.left).ideal ⟨⊤, @isAffineOpen_top U.left hU⟩ =
        Ideal.span {z} ∧
      (∀ j k, p j ≠ p k →
        Point.evaluate ⊤ z (y j) ≠ Point.evaluate ⊤ z (y k)) := by
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
  let k₀ : κ := ⟨y 0, ⟨0, rfl⟩⟩
  obtain ⟨d, hd, hIdeal⟩ := s2v_l1a_affine_point_equation U
    (fun k : κ => k.1) Subtype.val_injective k₀ z
    (s2v_l1a_univariate_eval_etale z hEtC) hz0 (by
      intro k hk heq
      obtain ⟨j, hj⟩ := k.2
      have hneq : p j ≠ p 0 := by
        intro heq'
        have hyj : y j = y 0 := by
          apply (cancel_mono u).mp
          exact (hy j).trans (heq'.trans (hy 0).symm)
        apply hk
        apply Subtype.ext
        exact hj.symm.trans hyj
      exact hzsep j 0 hneq (by simpa only [hj, hz0] using heq))
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
  · have hpoint : (y 0).left ≫ u.left = (p 0).left :=
      congrArg (fun f : ComplexPoint Z => f.left) (hy 0)
    change (((p 0).left.ker).comap (w.left ≫ u.left)).ideal ⟨⊤, isAffineOpen_top _⟩ = Ideal.span {z'}
    rw [Scheme.IdealSheafData.comap_comp]
    have hk : ((p 0).left.ker).comap u.left = (y 0).left.ker := by
      rw [← hpoint]
      exact s2v_l1a_open_kernel (y 0).left u.left
    rw [hk]
    exact hIdeal
  · intro j k hjk
    rw [heval, heval]
    exact hzsep j k hjk

end HodgeLean.Foundations.Program
