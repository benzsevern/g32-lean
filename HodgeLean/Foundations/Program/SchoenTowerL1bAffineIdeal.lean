import HodgeLean.Foundations.Program.SchoenTowerL1aIdealPullback
import HodgeLean.Foundations.Program.SchoenTowerL1aIdealOpenRestriction

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Pulling back an ideal sheaf between affine schemes extends its ideal of global sections. -/
theorem s2v_l1b_affine_ideal_comap {X Y : Scheme} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) (I : Y.IdealSheafData) :
    (I.comap f).ideal ⟨⊤, isAffineOpen_top X⟩ =
      (I.ideal ⟨⊤, isAffineOpen_top Y⟩).map f.appTop.hom := by
  exact s2v_l1a_affine_ideal_pullback f I

/-- Pullback of a two-generated affine ideal sheaf has the two actual pulled back generators. -/
theorem s2v_l1b_affine_ideal_comap_pair {X Y : Scheme} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) (I : Y.IdealSheafData) (u v : Γ(Y, ⊤))
    (hI : I.ideal ⟨⊤, isAffineOpen_top Y⟩ = Ideal.span {u, v}) :
    (I.comap f).ideal ⟨⊤, isAffineOpen_top X⟩ =
      Ideal.span {f.appTop.hom u, f.appTop.hom v} := by
  rw [s2v_l1b_affine_ideal_comap, hI, Ideal.map_span]
  congr 1
  exact Set.image_pair _ _ _

/-- Restriction to an affine open transports its ideal through the actual top-sections isomorphism. -/
theorem s2v_l1b_restrict_ideal_top {X : Scheme} (I : X.IdealSheafData) (U : X.affineOpens) :
    ((I.comap U.1.ι).ideal ⟨⊤, @isAffineOpen_top _ U.2⟩).map U.1.topIso.hom.hom =
      I.ideal U := by
  rw [s2v_l1a_open_ideal_top]
  exact Ideal.map_comap_of_surjective _
    U.1.topIso.commRingCatIsoToRingEquiv.surjective _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- On arbitrary affine charts, ideal pullback uses the actual restricted section map. -/
theorem s2v_l1b_comap_ideal_affine_charts {X Y : Scheme} (f : X ⟶ Y)
    (I : Y.IdealSheafData) (U : Y.affineOpens) (V : X.affineOpens)
    (h : V.1 ≤ f ⁻¹ᵁ U.1) :
    (I.comap f).ideal V = (I.ideal U).map (f.appLE U.1 V.1 h).hom := by
  let : IsAffine U.1.toScheme := U.2
  let : IsAffine V.1.toScheme := V.2
  let g := f.resLE U.1 V.1 h
  have hg : g ≫ U.1.ι = V.1.ι ≫ f := by simp only [g, Scheme.Hom.resLE_comp_ι]
  have hc : (I.comap f).comap V.1.ι = (I.comap U.1.ι).comap g := by
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, hg]
  have he := s2v_l1b_affine_ideal_comap g (I.comap U.1.ι)
  change ((I.comap U.1.ι).comap g).ideal ⟨⊤, isAffineOpen_top _⟩ =
    ((I.comap U.1.ι).ideal ⟨⊤, isAffineOpen_top _⟩).map g.appTop.hom at he
  rw [← hc] at he
  have hm := congrArg (Ideal.map V.1.topIso.hom.hom) he
  rw [s2v_l1b_restrict_ideal_top, Ideal.map_map] at hm
  have ha : g.appTop ≫ V.1.topIso.hom = U.1.topIso.hom ≫ f.appLE U.1 V.1 h := by
    simp [g, Scheme.Hom.resLE_app_top]
  have ha' := congrArg CommRingCat.Hom.hom ha
  simp only [CommRingCat.hom_comp] at ha'
  rw [ha', ← Ideal.map_map, s2v_l1b_restrict_ideal_top] at hm
  exact hm

end HodgeLean.Foundations.Program
