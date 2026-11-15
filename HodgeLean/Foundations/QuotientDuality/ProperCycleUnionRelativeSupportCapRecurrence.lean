import HodgeLean.Foundations.QuotientDuality.ProperCycleUnionRelativeSupportCap

/-! # Actual signed suspension recurrence in ordinary support-relative coordinates
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The original normal cap on ordinary support-relative homology commutes with the specified signed support suspensions through literal intersection coordinates.
Source: properCycle_cohomology_triad_support_cap_recurrence; properCycle_real_support_cap_source_comparison.
HC no distance; AV milestone no distance. -/
theorem properCycle_union_relative_support_cap_recurrence
    (Y : TopCat.{0}) (S T : Set Y) (hS : IsClosed S) (hT : IsClosed T)
    (p q : ℕ) (hp : Even p)
    (a : RelativeCohomology ℚ (TopPair.ofSubset (X := Y) Sᶜ) p) :
    properCycle_union_relative_support_cap (TopCat.of (ℝ × Y))
      (Prod.snd ⁻¹' S) {z | z.1 = 0 ∧ z.2 ∈ T}
      (hS.preimage continuous_snd)
      ((isClosed_eq continuous_fst continuous_const).inter (hT.preimage continuous_snd)) p (q+1)
      (relativeCohomologyMap ℚ p (properCycle_product_support_projection ℝ Y S) a) ≫
      (properCycle_real_support_suspension_iso Y T hT q).hom =
      HomologicalComplex.homologyMap ((relativeChainFunctor ℚ).map
        (properCycle_real_support_intersection_pair_iso Y S T).hom) (p+q+1) ≫
      (properCycle_real_support_suspension_iso Y (S ∩ T) (hS.inter hT) (p+q)).hom ≫
      properCycle_union_relative_support_cap Y S T hS hT p q a := by
  let X := TopCat.of (ℝ × Y)
  let S' : Set X := Prod.snd ⁻¹' S
  let T' : Set X := {z | z.1 = 0 ∧ z.2 ∈ T}
  let hS' := hS.preimage (continuous_snd : Continuous (Prod.snd : ℝ × Y → Y))
  let hT' : IsClosed T' := (isClosed_eq (continuous_fst : Continuous (Prod.fst : ℝ × Y → ℝ))
    continuous_const).inter (hT.preimage continuous_snd)
  let E := properCycle_support_cap_source_iso X S' T' hS' hT' (p+q+1)
  let U := properCycle_union_relative_support_cap X S' T' hS' hT' p (q+1)
    (relativeCohomologyMap ℚ p (properCycle_product_support_projection ℝ Y S) a)
  let B := properCycle_union_relative_support_cap Y S T hS hT p q a
  let C := ModuleCat.ofHom (triadCapCohomologyLinear ℚ X (Prod.snd ⁻¹' Sᶜ)
    T'ᶜ p (q+1) (relativeCohomologyMap ℚ p (properCycle_product_support_projection ℝ Y S) a))
  let J := HomologicalComplex.homologyMap ((relativeChainFunctor ℚ).map
    (properCycle_real_support_intersection_pair_iso Y S T).hom) (p+q+1)
  let EU := HomologicalComplex.homologyMap (triadToUnionRelativeChainMap ℚ X (Prod.snd ⁻¹' Sᶜ)
    T'ᶜ) (p+q+1) ≫ HomologicalComplex.homologyMap ((relativeChainFunctor ℚ).map
      (properCycle_real_cap_upper_union_iso Y S T).hom) (p+q+1)
  let sT := properCycle_real_support_suspension_iso Y T hT q
  let sS := properCycle_real_support_suspension_iso Y (S ∩ T) (hS.inter hT) (p+q)
  have he := properCycle_real_support_cap_source_comparison Y S T hS hT (p+q+1)
  change E.hom ≫ J = EU at he
  have h := properCycle_cohomology_triad_support_cap_recurrence Y S T hS hT p q hp a
  change C ≫ sT.hom = EU ≫ sS.hom ≫ B at h
  change U ≫ sT.hom = J ≫ sS.hom ≫ B
  apply (cancel_epi E.hom).mp
  calc
    E.hom ≫ (U ≫ sT.hom) = C ≫ sT.hom := by
      change E.hom ≫ ((E.inv ≫ C) ≫ sT.hom) = _
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = EU ≫ sS.hom ≫ B := h
    _ = E.hom ≫ (J ≫ sS.hom ≫ B) := by
      rw [← he]
      simp only [Category.assoc]

end HodgeLean.Foundations.QuotientDuality
