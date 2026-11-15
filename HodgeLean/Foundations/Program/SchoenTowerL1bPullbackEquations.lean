import HodgeLean.Foundations.Program.SchoenCycleAffineIdeals
import HodgeLean.Foundations.Program.SchoenTowerL1aIdealOpenRestriction
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Properties

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Pullback on affine neighborhoods extends the actual section ideal along the retained section map. -/
theorem s2v_l1b_pullback_ideal_sections
    {X Y : Scheme} (f : X ⟶ Y) (I : Y.IdealSheafData)
    (U : X.affineOpens) (V : Y.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1) :
    (I.comap f).ideal U = Ideal.map (f.appLE V.1 U.1 hUV).hom (I.ideal V) := by
  let : IsAffine U.1 := U.2
  let : IsAffine V.1 := V.2
  have hs : (I.comap f).comap U.1.ι =
      (I.comap V.1.ι).comap (f.resLE V.1 U.1 hUV) := by
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
      Scheme.Hom.resLE_comp_ι]
  have H := congrArg (fun J : U.1.toScheme.IdealSheafData =>
    J.ideal ⟨⊤, isAffineOpen_top U.1⟩) hs
  rw [s2v_l1a_open_ideal_top, s2e_affine_comap_ideal,
    s2v_l1a_open_ideal_top] at H
  have he := (arrowResLEAppIso f V.1 U.1 hUV).hom.w
  change V.1.topIso.hom ≫ f.appLE V.1 U.1 hUV =
    (f.resLE V.1 U.1 hUV).appTop ≫ U.1.topIso.hom at he
  have hmap := congrArg (Ideal.map U.1.topIso.hom.hom) H
  rw [Ideal.map_comap_of_surjective _ (ConcreteCategory.bijective_of_isIso U.1.topIso.hom).surjective] at hmap
  rw [Ideal.map_map, ← CommRingCat.hom_comp, ← he, CommRingCat.hom_comp,
    ← Ideal.map_map, Ideal.map_comap_of_surjective _ (ConcreteCategory.bijective_of_isIso V.1.topIso.hom).surjective] at hmap
  exact hmap

/-- Local principal equations pull back near every point of the source. -/
theorem s2v_l1b_local_principal_pullback
    {X Y : Scheme} (f : X ⟶ Y) (I : Y.IdealSheafData) (x : X)
    (hI : ∃ V : Y.affineOpens, f x ∈ V.1 ∧
      ∃ g : Γ(Y, V), I.ideal V = Ideal.span {g}) :
    ∃ U : X.affineOpens, x ∈ U.1 ∧
      ∃ g : Γ(X, U), (I.comap f).ideal U = Ideal.span {g} := by
  obtain ⟨V, hxV, g, hg⟩ := hI
  obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ f ⁻¹ᵁ V.1 from hxV)
  refine ⟨⟨U, hU⟩, hxU, (f.appLE V.1 U hUV).hom g, ?_⟩
  rw [s2v_l1b_pullback_ideal_sections f I ⟨U, hU⟩ V hUV, hg,
    Ideal.map_span, Set.image_singleton]

/-- A dominant map preserves nonzero sections after restriction to a nonempty source open. -/
theorem s2v_l1b_dominant_appLE_injective
    {X Y : Scheme} [IsIntegral X] [IsReduced Y]
    (f : X ⟶ Y) [IsDominant f] [QuasiCompact f]
    (U : X.Opens) [Nonempty U] (V : Y.Opens) (hUV : U ≤ f ⁻¹ᵁ V) :
    Function.Injective (f.appLE V U hUV).hom := by
  let := IsSchemeTheoreticallyDominant.of_isDominant f
  exact (map_injective_of_isIntegral X (homOfLE hUV)).comp (f.app_injective V)

/-- Nonzero local branch equations remain nonzero under dominant pullback. -/
theorem s2v_l1b_local_nonzero_principal_pullback
    {X Y : Scheme} [IsIntegral X] [IsReduced Y]
    (f : X ⟶ Y) [IsDominant f] [QuasiCompact f]
    (I : Y.IdealSheafData) (x : X)
    (hI : ∃ V : Y.affineOpens, f x ∈ V.1 ∧
      ∃ g : Γ(Y, V), I.ideal V = Ideal.span {g} ∧ g ≠ 0) :
    ∃ U : X.affineOpens, x ∈ U.1 ∧
      ∃ g : Γ(X, U), (I.comap f).ideal U = Ideal.span {g} ∧ g ≠ 0 := by
  obtain ⟨V, hxV, g, hg, hgn⟩ := hI
  obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ f ⁻¹ᵁ V.1 from hxV)
  let : Nonempty U := ⟨⟨x, hxU⟩⟩
  refine ⟨⟨U, hU⟩, hxU, (f.appLE V.1 U hUV).hom g, ?_, ?_⟩
  · rw [s2v_l1b_pullback_ideal_sections f I ⟨U, hU⟩ V hUV, hg,
      Ideal.map_span, Set.image_singleton]
  · intro hz
    exact hgn (s2v_l1b_dominant_appLE_injective f U V.1 hUV
      (hz.trans (map_zero (f.appLE V.1 U hUV).hom).symm))

end HodgeLean.Foundations.Program
