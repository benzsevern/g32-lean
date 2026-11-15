import HodgeLean.Foundations.Program.SchoenTowerL1aCurveFirstJets
import HodgeLean.Foundations.Program.SchoenTowerL1aEtaleRestriction
import HodgeLean.Foundations.Program.SchoenTowerL1aPointSections
import HodgeLean.Foundations.Program.SchoenTowerL1aJetLocalization

/-! # Nonzero first-order classes in the actual affine curve ring

Etale coordinates on smaller principal opens supply numerators with nonzero
first-order class in the actual affine point ideal.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Every actual complex point of a smooth affine curve has a nonzero first-order class in its global point ideal.
Source: Hartshorne, Algebraic Geometry, II.2, II.8 and III.10, localization and etale curve coordinates. -/
theorem s2v_l1a_affine_curve_point_first_jet
    (Z : Over (Spec ↧ℂ)) [IsAffine Z.left] [SmoothOfRelativeDimension 1 Z.hom]
    (p : ComplexPoint Z) :
    ∃ r : Γ(Z.left, ⊤), r ∈ p.left.ker.ideal ⟨⊤, isAffineOpen_top _⟩ ∧
      r ∉ (p.left.ker.ideal ⟨⊤, isAffineOpen_top _⟩) ^ 2 := by
  let D := localEtaleCoordinates Z 1 p.underlying
  obtain ⟨d, hdD, hpd⟩ := (isAffineOpen_top Z.left).exists_basicOpen_le
    (V := D.neighborhood) ⟨p.underlying, D.mem⟩ trivial
  let U := Z.left.basicOpen d
  let D' := s2v_l1a_restrict_localEtaleCoordinates D
    ⟨U, (isAffineOpen_top Z.left).basicOpen d⟩ hdD hpd
  let y : ComplexPoint (ComplexPoint.openScheme Z U) :=
    ComplexPoint.asOpenPoint Z U p hpd
  letI : IsAffine (ComplexPoint.openScheme Z U).left := (isAffineOpen_top Z.left).basicOpen d
  obtain ⟨hA, u, hu, hnu⟩ := s2v_l1a_curve_chart_point_ideal_first_jet D' y
  let evB := s2v_l1a_pointSectionEvaluation (ComplexPoint.openScheme Z U) y
  have hkerB : RingHom.ker evB = y.left.ker.ideal ⟨⊤, isAffineOpen_top _⟩ :=
    s2v_l1a_pointSectionEvaluation_kernel (ComplexPoint.openScheme Z U) y
  have huB : u ∈ RingHom.ker evB := hkerB.symm ▸ hu
  have hnuB : u ∉ RingHom.ker evB ^ 2 := by simpa only [hkerB] using hnu
  let e := U.topIso.symm.commRingCatIsoToRingEquiv
  let evA := evB.comp e.toRingHom
  let uA := e.symm u
  change evB u = 0 at huB
  have huA : uA ∈ RingHom.ker evA := by
    change evB (e (e.symm u)) = 0
    simpa only [e.apply_symm_apply] using huB
  have hnuA : uA ∉ RingHom.ker evA ^ 2 := by
    intro hbad
    apply hnuB
    have H := (Ideal.le_comap_pow (K := RingHom.ker evB) e.toRingHom 2) hbad
    change e (e.symm u) ∈ RingHom.ker evB ^ 2 at H
    simpa only [e.apply_symm_apply] using H
  let res := Z.left.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
  letI : Algebra Γ(Z.left, ⊤) Γ(Z.left, U) := res.hom.toAlgebra
  have hlocal : IsLocalization.Away d Γ(Z.left, U) :=
    (isAffineOpen_top Z.left).isLocalization_basicOpen d
  have hres : res ≫ U.topIso.inv = U.ι.appTop := by
    have hr : U.ι.appTop ≫ U.topIso.hom = res :=
      Scheme.Opens.ι_appTop_topIso_hom U
    rw [← hr, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hfac : y.left ≫ U.ι = p.left := ComplexPoint.liftToOpen_fac Z U p hpd
  have heval : evA.comp (algebraMap Γ(Z.left, ⊤) Γ(Z.left, U)) =
      s2v_l1a_pointSectionEvaluation Z p := by
    apply RingHom.ext
    intro r
    change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom
      ((res ≫ U.topIso.inv ≫ y.left.appTop).hom r) =
        (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (p.left.appTop.hom r)
    rw [← Category.assoc, hres, ← Scheme.Hom.comp_appTop, hfac]
  obtain ⟨r, hr, hnr⟩ := s2v_l1a_localized_first_jet_numerator d
    (s2v_l1a_pointSectionEvaluation Z p) evA heval uA huA hnuA
  rw [s2v_l1a_pointSectionEvaluation_kernel Z p] at hr hnr
  exact ⟨r, hr, hnr⟩

end HodgeLean.Foundations.Program
