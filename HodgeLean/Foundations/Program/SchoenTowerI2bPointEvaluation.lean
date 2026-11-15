import HodgeLean.Foundations.Program.SchoenTowerI2bTransport
import HodgeLean.Foundations.Program.SchoenTowerI2bChartScalars

/-! Evaluation of a retained branch equation at the actual complex point.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A principal branch equation evaluates to zero at a complex point of its actual support.
Source: the support criterion for ideal sheaves and the local stalk evaluation. -/
theorem s2v_i2b_principal_support_evaluation
    (U : Scheme) [IsAffine U] (I : U.IdealSheafData) (z : Γ(U, ⊤))
    (hI : I.ideal ⟨⊤, isAffineOpen_top U⟩ = Ideal.span {z})
    (q : Spec ↧ℂ ⟶ U) (hq : q (IsLocalRing.closedPoint ℂ) ∈ I.support) :
    (q.appTop ≫ (Scheme.ΓSpecIso ↧ℂ).hom).hom z = 0 := by
  have hzero := (I.mem_support_iff_of_mem
    (U := ⟨⊤, isAffineOpen_top U⟩) (by trivial)).mp hq
  rw [hI] at hzero
  have hnot := (U.mem_zeroLocus_iff (Ideal.span {z} : Set Γ(U, ⊤))
    (q (IsLocalRing.closedPoint ℂ))).mp hzero z (Ideal.subset_span (Set.mem_singleton z))
  have heval : U.presheaf.germ ⊤ (q (IsLocalRing.closedPoint ℂ)) trivial ≫
      Scheme.stalkClosedPointTo q = q.appTop ≫ (Scheme.ΓSpecIso ↧ℂ).hom := by
    dsimp only [Scheme.stalkClosedPointTo]
    rw [← Category.assoc, Scheme.Hom.germ_stalkMap, Category.assoc]
    change q.appTop ≫ ((Spec ↧ℂ).presheaf.germ ⊤ (IsLocalRing.closedPoint ℂ) trivial ≫
      (stalkClosedPointIso ↧ℂ).hom) = q.appTop ≫ (Scheme.ΓSpecIso ↧ℂ).hom
    exact congrArg (fun f : Γ(Spec ↧ℂ, ⊤) ⟶ CommRingCat.of ℂ => q.appTop ≫ f)
      (germ_stalkClosedPointIso_hom (CommRingCat.of ℂ))
  by_contra hne
  have hv := congrArg (fun f : Γ(U, ⊤) ⟶ CommRingCat.of ℂ => f.hom z) heval
  have hunit : IsUnit ((Scheme.stalkClosedPointTo q).hom
      (U.presheaf.germ ⊤ (q (IsLocalRing.closedPoint ℂ)) trivial z)) := by
    change IsUnit ((U.presheaf.germ ⊤ (q (IsLocalRing.closedPoint ℂ)) trivial ≫
      Scheme.stalkClosedPointTo q).hom z)
    rw [hv]
    exact isUnit_iff_ne_zero.mpr hne
  have hgerm : IsUnit (U.presheaf.germ ⊤ (q (IsLocalRing.closedPoint ℂ)) trivial z) :=
    (isUnit_map_iff (Scheme.stalkClosedPointTo q).hom _).mp hunit
  exact hnot ((U.mem_basicOpen_top z _).mpr hgerm)

/-- The actual complex-point evaluation fixes the scalars supplied by the structure morphism.
Source: the complex-point base equation and contravariance of global sections. -/
theorem s2v_i2b_complex_point_scalar_compatible
    (U : Over (Spec ↧ℂ)) (q : ComplexPoint U) (c : ℂ) :
    (q.left.appTop ≫ (Scheme.ΓSpecIso ↧ℂ).hom).hom
      (((Scheme.ΓSpecIso ↧ℂ).inv ≫ U.hom.appTop).hom c) = c := by
  have he : ((Scheme.ΓSpecIso ↧ℂ).inv ≫ U.hom.appTop) ≫
      (q.left.appTop ≫ (Scheme.ΓSpecIso ↧ℂ).hom) = 𝟙 (CommRingCat.of ℂ) := by
    calc
      ((Scheme.ΓSpecIso ↧ℂ).inv ≫ U.hom.appTop) ≫
          (q.left.appTop ≫ (Scheme.ΓSpecIso ↧ℂ).hom) =
          (Scheme.ΓSpecIso ↧ℂ).inv ≫ (q.left ≫ U.hom).appTop ≫
            (Scheme.ΓSpecIso ↧ℂ).hom := by
        rw [Scheme.Hom.comp_appTop]
        simp only [Category.assoc]
      _ = 𝟙 (CommRingCat.of ℂ) := by
        rw [q.w]
        change (Scheme.ΓSpecIso ↧ℂ).inv ≫ Scheme.Hom.appTop (𝟙 (Spec ↧ℂ)) ≫
          (Scheme.ΓSpecIso ↧ℂ).hom = _
        rw [Scheme.Hom.id_appTop, Category.id_comp, Iso.inv_hom_id]
  exact congrArg (fun f : CommRingCat.of ℂ ⟶ CommRingCat.of ℂ => f.hom c) he

end HodgeLean.Foundations.Program
