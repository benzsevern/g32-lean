import HodgeLean.Foundations.QuotientDuality.ProperCycleIteratedIntersectionSuspension

/-! # Exact recurrence for the original iterated normal caps
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The original iterated normal caps commute with the actual signed support suspensions on the recursive point-support pairs.
Source: properCycle_union_relative_support_cap_recurrence; properCycle_iterated_intersection_suspension.
HC no distance; AV milestone no distance. -/
theorem properCycle_iterated_union_cap_recurrence
    (Y : TopCat.{0}) (S T : Set Y) (hS : IsClosed S) (hT : IsClosed T)
    (p : ℕ) (hp : Even p)
    (a : RelativeCohomology ℚ (TopPair.ofSubset (X := Y) Sᶜ) p) (n : ℕ) :
    properCycle_iterated_union_relative_cap Y S T hS hT p a (n+1) ≫
      (properCycle_real_support_suspension_iso (properCycle_real_support_space Y n)
        (properCycle_real_point_support Y T n)
        (properCycle_real_point_support_isClosed Y T hT n) n).hom =
      (properCycle_real_support_suspension_iso (properCycle_real_support_space Y n)
        (properCycle_real_point_support Y (S ∩ T) n)
        (properCycle_real_point_support_isClosed Y (S ∩ T) (hS.inter hT) n) (p+n)).hom ≫
      properCycle_iterated_union_relative_cap Y S T hS hT p a n := by
  let X := properCycle_real_support_space Y n
  let A := properCycle_real_normal_support Y S n
  let B := properCycle_real_point_support Y T n
  let hA := properCycle_real_normal_support_isClosed Y S hS n
  let hB := properCycle_real_point_support_isClosed Y T hT n
  let an := properCycle_real_support_coclass Y S p a n
  let U := properCycle_union_relative_support_cap (TopCat.of (ℝ × X))
    (Prod.snd ⁻¹' A) {z | z.1 = 0 ∧ z.2 ∈ B} (hA.preimage continuous_snd)
    ((isClosed_eq continuous_fst continuous_const).inter (hB.preimage continuous_snd)) p (n+1)
    (relativeCohomologyMap ℚ p (properCycle_product_support_projection ℝ X A) an)
  let C := properCycle_union_relative_support_cap X A B hA hB p n an
  let JU := HomologicalComplex.homologyMap ((relativeChainFunctor ℚ).map
    (properCycle_iterated_support_intersection_pair_iso Y S T (n+1)).inv) (p+n+1)
  let J := HomologicalComplex.homologyMap ((relativeChainFunctor ℚ).map
    (properCycle_iterated_support_intersection_pair_iso Y S T n).inv) (p+n)
  let R := HomologicalComplex.homologyMap ((relativeChainFunctor ℚ).map
    (properCycle_real_support_intersection_pair_iso X A B).hom) (p+n+1)
  let sT := properCycle_real_support_suspension_iso X B hB n
  let sI := properCycle_real_support_suspension_iso X (A ∩ B) (hA.inter hB) (p+n)
  let sP := properCycle_real_support_suspension_iso X
    (properCycle_real_point_support Y (S ∩ T) n)
    (properCycle_real_point_support_isClosed Y (S ∩ T) (hS.inter hT) n) (p+n)
  have h := properCycle_union_relative_support_cap_recurrence X A B hA hB p n hp an
  change U ≫ sT.hom = R ≫ sI.hom ≫ C at h
  have hi := properCycle_iterated_intersection_suspension Y S T hS hT n (p+n)
  change JU ≫ R ≫ sI.hom = sP.hom ≫ J at hi
  change (JU ≫ U) ≫ sT.hom = sP.hom ≫ (J ≫ C)
  calc
    _ = JU ≫ (U ≫ sT.hom) := Category.assoc _ _ _
    _ = JU ≫ (R ≫ sI.hom ≫ C) := by rw [h]
    _ = (JU ≫ R ≫ sI.hom) ≫ C := by simp only [Category.assoc]
    _ = (sP.hom ≫ J) ≫ C := by rw [hi]
    _ = _ := Category.assoc _ _ _

/-- The original normal cap after any number of actual real support suspensions retains the original base cap through the specified composed suspension isomorphisms.
Source: properCycle_iterated_union_cap_recurrence; properCycle_iterated_support_suspension_iso.
HC no distance; AV milestone no distance. -/
theorem properCycle_iterated_union_cap_suspension
    (Y : TopCat.{0}) (S T : Set Y) (hS : IsClosed S) (hT : IsClosed T)
    (p : ℕ) (hp : Even p)
    (a : RelativeCohomology ℚ (TopPair.ofSubset (X := Y) Sᶜ) p) (n : ℕ) :
    properCycle_iterated_union_relative_cap Y S T hS hT p a n ≫
      (properCycle_iterated_zero_support_suspension_iso Y T hT n).hom =
      (properCycle_iterated_support_suspension_iso Y (S ∩ T) (hS.inter hT) p n).hom ≫
      properCycle_iterated_union_relative_cap Y S T hS hT p a 0 := by
  induction n with
  | zero =>
    change properCycle_iterated_union_relative_cap Y S T hS hT p a 0 ≫ 𝟙 _ =
      𝟙 _ ≫ properCycle_iterated_union_relative_cap Y S T hS hT p a 0
    simp only [Category.comp_id, Category.id_comp]
  | succ n ih =>
    let sT := properCycle_real_support_suspension_iso (properCycle_real_support_space Y n)
      (properCycle_real_point_support Y T n) (properCycle_real_point_support_isClosed Y T hT n) n
    let sP := properCycle_real_support_suspension_iso (properCycle_real_support_space Y n)
      (properCycle_real_point_support Y (S ∩ T) n)
      (properCycle_real_point_support_isClosed Y (S ∩ T) (hS.inter hT) n) (p+n)
    let tT := properCycle_iterated_zero_support_suspension_iso Y T hT n
    let tP := properCycle_iterated_support_suspension_iso Y (S ∩ T) (hS.inter hT) p n
    let Kn := properCycle_iterated_union_relative_cap Y S T hS hT p a n
    let Ku := properCycle_iterated_union_relative_cap Y S T hS hT p a (n+1)
    let K₀ := properCycle_iterated_union_relative_cap Y S T hS hT p a 0
    have hs := properCycle_iterated_union_cap_recurrence Y S T hS hT p hp a n
    change Ku ≫ sT.hom = sP.hom ≫ Kn at hs
    change Kn ≫ tT.hom = tP.hom ≫ K₀ at ih
    change Ku ≫ (sT.hom ≫ tT.hom) = (sP.hom ≫ tP.hom) ≫ K₀
    calc
      _ = (Ku ≫ sT.hom) ≫ tT.hom := (Category.assoc _ _ _).symm
      _ = (sP.hom ≫ Kn) ≫ tT.hom := by rw [hs]
      _ = sP.hom ≫ (Kn ≫ tT.hom) := Category.assoc _ _ _
      _ = sP.hom ≫ (tP.hom ≫ K₀) := by rw [ih]
      _ = _ := (Category.assoc _ _ _).symm

end HodgeLean.Foundations.QuotientDuality
