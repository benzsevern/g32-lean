import HodgeLean.Foundations.QuotientDuality.ProperCycleRealCapRefinedSquare
import HodgeLean.Foundations.QuotientDuality.ProperCycleRealSupportSuspension

/-! # Original normal caps in actual support-relative coordinates
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual upper normal cap in the zero-slice support-relative groups, using the specified source refinement and original right excision maps.
Source: Hatcher, Algebraic Topology, section 3.3; properCycle_real_cap_refined_inverse_square; properCycle_real_support_right_iso.
HC no distance; AV milestone no distance. -/
def properCycle_real_upper_support_cap
    (Y : TopCat.{0}) (S T : Set Y) (hS : IsClosed S) (hT : IsClosed T)
    (p q : ℕ) (hp : Even p)
    (φ : AlgebraicTopology.Simplicial.Cochain ℚ (TopCat.toSSet.obj (TopCat.of (ℝ × Y))) p)
    (hA : AlgebraicTopology.Simplicial.cochainMap ℚ
      (subsetSingularSubcomplex (TopCat.of (ℝ × Y)) (Prod.snd ⁻¹' Sᶜ)).ι p φ = 0)
    (hφ : AlgebraicTopology.Simplicial.coboundary ℚ p φ = 0) :
    RelativeHomology ℚ (TopPair.ofSubset (X := TopCat.of (ℝ × Y))
      {z | z.1 = 0 ∧ z.2 ∈ S ∩ T}ᶜ) (p+q+1) ⟶
    RelativeHomology ℚ (TopPair.ofSubset (X := TopCat.of (ℝ × Y))
      {z | z.1 = 0 ∧ z.2 ∈ T}ᶜ) (q+1) := by
  let X := TopCat.of (ℝ × Y)
  let A := subsetSingularSubcomplex X (Prod.snd ⁻¹' Sᶜ)
  let P := subsetSingularSubcomplex X {z | 0 ≤ z.1 ∧ z.2 ∈ T}ᶜ
  let Q := subsetSingularSubcomplex X {z | z.1 ≤ 0 ∧ z.2 ∈ T}ᶜ
  letI := properCycle_real_cap_refinement_right_isIso Y S T hS hT (p+q)
  exact (properCycle_real_support_right_iso Y (S ∩ T) (hS.inter hT) (p+q+1)).inv ≫
    inv (HomologicalComplex.homologyMap
      (properCycle_real_cap_source_refinement Y S T).τ₃ (p+q+1)) ≫
    properCycle_subcomplex_cap_homology_map A (P ⊔ Q) p (q+1) hp φ hA hφ ≫
    (properCycle_real_support_right_iso Y T hT (q+1)).hom

/-- The actual lower normal cap in base support-relative groups, using literal base projection, the specified left comparisons and the original source refinement.
Source: Hatcher, Algebraic Topology, section 3.3; properCycle_real_cap_refined_inverse_square; properCycle_product_support_homology_iso.
HC no distance; AV milestone no distance. -/
def properCycle_real_lower_support_cap
    (Y : TopCat.{0}) (S T : Set Y) (hS : IsClosed S) (hT : IsClosed T)
    (p q : ℕ) (hp : Even p)
    (φ : AlgebraicTopology.Simplicial.Cochain ℚ (TopCat.toSSet.obj (TopCat.of (ℝ × Y))) p)
    (hA : AlgebraicTopology.Simplicial.cochainMap ℚ
      (subsetSingularSubcomplex (TopCat.of (ℝ × Y)) (Prod.snd ⁻¹' Sᶜ)).ι p φ = 0)
    (hφ : AlgebraicTopology.Simplicial.coboundary ℚ p φ = 0) :
    RelativeHomology ℚ (TopPair.ofSubset (X := Y) (S ∩ T)ᶜ) (p+q) ⟶
      RelativeHomology ℚ (TopPair.ofSubset (X := Y) Tᶜ) q := by
  let X := TopCat.of (ℝ × Y)
  let A := subsetSingularSubcomplex X (Prod.snd ⁻¹' Sᶜ)
  let P := subsetSingularSubcomplex X {z | 0 ≤ z.1 ∧ z.2 ∈ T}ᶜ
  let Q := subsetSingularSubcomplex X {z | z.1 ≤ 0 ∧ z.2 ∈ T}ᶜ
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.down ℕ)
  letI := properCycle_real_cap_refinement_left_isIso Y S T hS hT (p+q)
  exact (properCycle_product_support_homology_iso ℝ Y (S ∩ T) (p+q)).inv ≫
    ((H (p+q)).mapIso (properCycle_real_support_left_iso Y (S ∩ T))).inv ≫
    inv (HomologicalComplex.homologyMap
      (properCycle_real_cap_source_refinement Y S T).τ₁ (p+q)) ≫
    properCycle_subcomplex_cap_homology_map A (P ⊓ Q) p q hp φ hA hφ ≫
    ((H q).mapIso (properCycle_real_support_left_iso Y T)).hom ≫
    (properCycle_product_support_homology_iso ℝ Y T q).hom

/-- The original normal cap commutes with the actual signed support suspension after its specified source refinement, in the actual support-relative groups.
Source: Hatcher, Algebraic Topology, sections 2.2 and 3.3; properCycle_real_cap_refined_inverse_square; properCycle_real_support_suspension_iso.
HC no distance; AV milestone no distance. -/
theorem properCycle_real_support_cap_suspension
    (Y : TopCat.{0}) (S T : Set Y) (hS : IsClosed S) (hT : IsClosed T)
    (p q : ℕ) (hp : Even p)
    (φ : AlgebraicTopology.Simplicial.Cochain ℚ (TopCat.toSSet.obj (TopCat.of (ℝ × Y))) p)
    (hA : AlgebraicTopology.Simplicial.cochainMap ℚ
      (subsetSingularSubcomplex (TopCat.of (ℝ × Y)) (Prod.snd ⁻¹' Sᶜ)).ι p φ = 0)
    (hφ : AlgebraicTopology.Simplicial.coboundary ℚ p φ = 0) :
    properCycle_real_upper_support_cap Y S T hS hT p q hp φ hA hφ ≫
        (properCycle_real_support_suspension_iso Y T hT q).hom =
      (properCycle_real_support_suspension_iso Y (S ∩ T) (hS.inter hT) (p+q)).hom ≫
        properCycle_real_lower_support_cap Y S T hS hT p q hp φ hA hφ := by
  letI := properCycle_real_cap_refinement_left_isIso Y S T hS hT (p+q)
  letI := properCycle_real_cap_refinement_right_isIso Y S T hS hT (p+q)
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.down ℕ)
  let Rs := properCycle_real_support_right_iso Y (S ∩ T) (hS.inter hT) (p+q+1)
  let Rt := properCycle_real_support_right_iso Y T hT (q+1)
  let Ls := (H (p+q)).mapIso (properCycle_real_support_left_iso Y (S ∩ T))
  let Lt := (H q).mapIso (properCycle_real_support_left_iso Y T)
  let Ps := properCycle_product_support_homology_iso ℝ Y (S ∩ T) (p+q)
  let Pt := properCycle_product_support_homology_iso ℝ Y T q
  let Ds := properCycle_real_cap_target_connecting_iso Y (S ∩ T) (hS.inter hT) (p+q)
  let Dt := properCycle_real_cap_target_connecting_iso Y T hT q
  let l := HomologicalComplex.homologyMap (properCycle_real_cap_source_refinement Y S T).τ₁ (p+q)
  let r := HomologicalComplex.homologyMap (properCycle_real_cap_source_refinement Y S T).τ₃ (p+q+1)
  let X := TopCat.of (ℝ × Y)
  let A := subsetSingularSubcomplex X (Prod.snd ⁻¹' Sᶜ)
  let P := subsetSingularSubcomplex X {z | 0 ≤ z.1 ∧ z.2 ∈ T}ᶜ
  let Q := subsetSingularSubcomplex X {z | z.1 ≤ 0 ∧ z.2 ∈ T}ᶜ
  let Klo := properCycle_subcomplex_cap_homology_map A (P ⊓ Q) p q hp φ hA hφ
  let Khi := properCycle_subcomplex_cap_homology_map A (P ⊔ Q) p (q+1) hp φ hA hφ
  have hc := congrArg (fun m => m ≫ Dt.hom)
    (properCycle_real_cap_refined_inverse_square Y S T hS hT p q hp φ hA hφ)
  change (inv r ≫ Khi) ≫ Dt.hom = (Ds.hom ≫ inv l ≫ Klo ≫ Dt.inv) ≫ Dt.hom at hc
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at hc
  change (Rs.inv ≫ inv r ≫ Khi ≫ Rt.hom) ≫
      (Rt.inv ≫ Dt.hom ≫ Lt.hom ≫ Pt.hom) =
    (Rs.inv ≫ Ds.hom ≫ Ls.hom ≫ Ps.hom) ≫
      (Ps.inv ≫ Ls.inv ≫ inv l ≫ Klo ≫ Lt.hom ≫ Pt.hom)
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  simpa only [Category.assoc] using congrArg (fun m => Rs.inv ≫ m ≫ Lt.hom ≫ Pt.hom) hc

end HodgeLean.Foundations.QuotientDuality
