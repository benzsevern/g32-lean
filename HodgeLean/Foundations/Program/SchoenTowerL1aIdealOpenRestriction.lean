import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Actual ideal sections on restricted affine quotient charts

Implication from actual open restriction and affine ideal image to the
contracted coordinate ideal on the actual restricted quotient map.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Ideal sections on the actual open scheme are the original sections under
its actual global-section identification.
Source: Hartshorne, Algebraic Geometry, II.5, restriction of ideal sheaves. -/
theorem s2v_l1a_open_ideal_top
    {X : Scheme} (I : X.IdealSheafData) (U : X.affineOpens) :
    (I.comap U.1.ι).ideal ⟨⊤, @isAffineOpen_top _ U.2⟩ =
      (I.ideal U).comap U.1.topIso.hom.hom := by
  have hImg : IsAffineOpen (U.1.ι ''ᵁ ⊤) := by
    rw [U.1.ι_image_top]
    exact U.2
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion, U.1.ι_appIso]
  change I.ideal ⟨U.1.ι ''ᵁ ⊤, hImg⟩ = (I.ideal U).comap U.1.topIso.hom.hom
  have H : (I.ideal U).map U.1.topIso.inv.hom = I.ideal ⟨U.1.ι ''ᵁ ⊤, hImg⟩ :=
    I.map_ideal (U := ⟨U.1.ι ''ᵁ ⊤, hImg⟩) (V := U) U.1.ι_image_top.le
  exact H.symm.trans (Ideal.map_comap_of_equiv U.1.topIso.symm.commRingCatIsoToRingEquiv)

/-- On the actual restricted affine quotient, image of an ideal is contraction
along that same restricted map on global sections.
Source: Hartshorne, Algebraic Geometry, II.5, affine ideal images and open restriction. -/
theorem s2v_l1a_restricted_ideal_image
    {X Y : Scheme} (f : X ⟶ Y) [IsAffineHom f]
    (I : X.IdealSheafData) (U : Y.affineOpens) :
    let hV := U.2.preimage f
    ((I.map f).comap U.1.ι).ideal ⟨⊤, @isAffineOpen_top _ U.2⟩ =
      ((I.comap (f ⁻¹ᵁ U.1).ι).ideal ⟨⊤, @isAffineOpen_top _ hV⟩).comap
        (f ∣_ U.1).appTop.hom := by
  let V : X.affineOpens := ⟨f ⁻¹ᵁ U.1, U.2.preimage f⟩
  dsimp only
  rw [s2v_l1a_open_ideal_top (I.map f) U, Scheme.IdealSheafData.ideal_map_of_isAffineHom,
    s2v_l1a_open_ideal_top I V, Ideal.comap_comap, Ideal.comap_comap]
  have H := (arrowResLEAppIso f U.1 (f ⁻¹ᵁ U.1) le_rfl).hom.w
  change U.1.topIso.hom ≫ f.appLE U.1 (f ⁻¹ᵁ U.1) le_rfl =
    (f.resLE U.1 (f ⁻¹ᵁ U.1) le_rfl).appTop ≫ (f ⁻¹ᵁ U.1).topIso.hom at H
  rw [Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.appLE_eq_app] at H
  exact congrArg (fun φ => (I.ideal V).comap φ.hom) H

end HodgeLean.Foundations.Program
