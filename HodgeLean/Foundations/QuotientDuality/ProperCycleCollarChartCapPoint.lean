import HodgeLean.Foundations.QuotientDuality.ProperCycleCollarCapPointRestriction
import HodgeLean.Foundations.QuotientDuality.ProperCycleCollarChartLocalCap

/-! # Actual global support point values from original collar chart caps
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- When an original supported class has the given literal chart pullback, the actual collar chart cap maps to the original global support point value with the same specified ambient orientation.
Source: ProperCycleSupportCollar.cap_point_restriction; ProperCycleSupportCollar.chart_local_support_cap.
HC no distance; AV milestone no distance. -/
lemma ProperCycleSupportCollar.chart_cap_point
    {X : TopCat.{0}} [T1Space X] {S : Set X} (C : ProperCycleSupportCollar X S) (hS : IsClosed S)
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (Y : TopCat.{0})
    (e : OpenPartialHomeomorph X (E × Y)) (W : Opens X)
    (hWe : (W : Set X) ⊆ e.source) (hWN : (W : Set X) ⊆ C.neighborhood)
    (hR : ∀ (x : X) (hx : x ∈ W), (C.retraction ⟨x, hWN hx⟩).val ∈ e.source)
    (y : Y) (hflat : ∀ x ∈ e.source, x ∈ S ↔ (e x).2 = y)
    (z : S) (hzW : z.val ∈ W) (hcenter : e z.val = (0, y)) (p q : ℕ)
    (a : CohomologyWithSupport ℚ X S p)
    (b : RelativeCohomology ℚ (TopPair.ofSubset (X := TopCat.of (E × Y)) (Prod.snd ⁻¹' {y}ᶜ)) p)
    (ha : relativeCohomologyMap ℚ p (b6m_subspacePairMap X (W : Set X) Sᶜ) a =
      relativeCohomologyMap ℚ p
        (TopPair.ofSubsetHom (X := TopCat.of W) (Y := TopCat.of (E × Y))
          (TopPair.Hom.fst (C.chart_retraction_point_pair E Y e W hWe hWN hR y hflat z hzW hcenter))
          (C.chart_retraction_triad_maps E Y e W hWe hWN hR y hflat z hzW hcenter).1) b)
    (c : Homology ℚ X (p+q)) :
    let j : TopCat.of {s : S | s.val ∈ e.source} ⟶ TopCat.of S :=
      TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
    relativeHomologyMap ℚ q (imagePointPairMap j Subtype.val_injective ⟨z, hWe hzW⟩)
      (C.chart_local_support_cap hS E Y e W hWe hWN hR y hflat z hzW hcenter p q
        ((properCycle_open_local_homology_iso X W ⟨z.val, hzW⟩ (p+q)).inv.hom
          (localOrientation X (p+q) c z.val)) b) =
      localOrientation (TopCat.of S) q (C.cap hS p q c a) z := by
  dsimp only
  let j : TopCat.of {s : S | s.val ∈ e.source} ⟶ TopCat.of S :=
    TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let i : TopCat.of W ⟶ TopCat.of C.neighborhood :=
    TopCat.ofHom ⟨fun x => ⟨x.val, hWN x.property⟩, continuous_subtype_val.subtype_mk _⟩
  let r := TopPair.ofSubsetHom (i ≫ C.retraction)
    (show Set.MapsTo (i ≫ C.retraction)
      ((fun x : W => C.retraction ⟨x.val, hWN x.property⟩) ⁻¹' {z}ᶜ) {z}ᶜ from fun _ h => h)
  have hp : C.chart_support_point_pair e W hWe hWN hR z hzW ≫
      imagePointPairMap j Subtype.val_injective ⟨z, hWe hzW⟩ = r := by ext x : 2 <;> rfl
  have hm := congrArg (relativeHomologyMap ℚ q) hp
  rw [relativeHomologyMap_comp] at hm
  have h := C.cap_point_restriction hS W hWN z hzW p q a c
  dsimp only at h
  rw [ha] at h
  unfold ProperCycleSupportCollar.chart_local_support_cap
  change relativeHomologyMap ℚ q (imagePointPairMap j Subtype.val_injective ⟨z, hWe hzW⟩)
    (relativeHomologyMap ℚ q (C.chart_support_point_pair e W hWe hWN hR z hzW) _) = _
  change ((relativeHomologyMap ℚ q (imagePointPairMap j Subtype.val_injective ⟨z, hWe hzW⟩)).comp
    (relativeHomologyMap ℚ q (C.chart_support_point_pair e W hWe hWN hR z hzW))) _ = _
  rw [hm]
  exact h.symm

end HodgeLean.Foundations.QuotientDuality
