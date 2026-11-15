import HodgeLean.Foundations.Program.G32Native.PairedC3AffineResidualRestriction

/-! # Residual quotient restrictions as actual scheme maps -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
universe u

/-- The spectra of the actual quotient restriction maps commute with the
canonical residual open immersions. Thus these ring restrictions are the
transition maps in the existing residual scheme. -/
theorem pairedC3_residual_restriction_scheme
    {X : Scheme.{u}} (I : X.IdealSheafData) (V W : X.affineOpens)
    (hWV : W.1 ≤ V.1) :
    Spec.map (CommRingCat.ofHom (pairedC3AffineResidualRestriction I V W hWV)) ≫
      I.subschemeCover.f V = I.subschemeCover.f W := by
  apply (cancel_mono I.subschemeι).mp
  rw [Category.assoc, I.subschemeCover_map_subschemeι,
    I.subschemeCover_map_subschemeι, I.glueDataObjι_ι, I.glueDataObjι_ι]
  rw [← Spec.map_comp_assoc]
  have hq : CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal V)) ≫
      CommRingCat.ofHom (pairedC3AffineResidualRestriction I V W hWV) =
      X.presheaf.map (homOfLE hWV).op ≫
        CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal W)) := by
    ext a
    rfl
  rw [hq, Spec.map_comp, Category.assoc, V.2.map_fromSpec W.2]

/-- Changing to supplied affine coordinates conjugates the actual quotient
restriction. The resulting spectrum map commutes with the original residual
open immersions, so it is their actual scheme transition. -/
theorem pairedC3_residual_coordinate_transition_scheme
    {X : Scheme.{u}} (I : X.IdealSheafData) (V W : X.affineOpens)
    (hWV : W.1 ≤ V.1) {P Q : Type u} [CommRing P] [CommRing Q]
    (eV : (Γ(X, V) ⧸ I.ideal V) ≃+* P)
    (eW : (Γ(X, W) ⧸ I.ideal W) ≃+* Q) :
    let r := pairedC3AffineResidualRestriction I V W hWV
    Spec.map (CommRingCat.ofHom
        (eW.toRingHom.comp (r.comp eV.symm.toRingHom))) ≫
      (Spec.map (CommRingCat.ofHom eV.toRingHom) ≫ I.subschemeCover.f V) =
      Spec.map (CommRingCat.ofHom eW.toRingHom) ≫ I.subschemeCover.f W := by
  dsimp only
  rw [← Spec.map_comp_assoc]
  have h : CommRingCat.ofHom eV.toRingHom ≫
      CommRingCat.ofHom (eW.toRingHom.comp
        ((pairedC3AffineResidualRestriction I V W hWV).comp eV.symm.toRingHom)) =
      CommRingCat.ofHom (pairedC3AffineResidualRestriction I V W hWV) ≫
        CommRingCat.ofHom eW.toRingHom := by
    ext a
    change eW (pairedC3AffineResidualRestriction I V W hWV (eV.symm (eV a))) =
      eW (pairedC3AffineResidualRestriction I V W hWV a)
    rw [RingEquiv.symm_apply_apply]
  rw [h, Spec.map_comp, Category.assoc, pairedC3_residual_restriction_scheme]

#print axioms pairedC3_residual_coordinate_transition_scheme
#print axioms pairedC3_residual_restriction_scheme
end HodgeLean.Foundations.Program.G32Native
