import HodgeLean.Foundations.QuotientDuality.ProperCycleIntrinsicSupportSum
import HodgeLean.Foundations.QuotientDuality.ProperCycleIntrinsicSupportPointValues
import HodgeLean.Foundations.QuotientDuality.ProperCycleIsolatedComponentChart

/-! # Independence of intrinsic classes on actual pure cycle supports
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Adapters
namespace HodgeLean.Foundations.QuotientDuality

/-- At an actual point on just one original component, the original point value of the intrinsic sum is exactly that component's coefficient times its specified intrinsic point value.
Source: properCycle_intrinsic_support_component_point_zero; functoriality of relative singular homology.
HC no distance; AV milestone no distance. -/
lemma properCycle_intrinsic_support_sum_point_value
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (k : ℕ) (hdim : TopologicalSpace.dim X.left = 2*k)
    (γ : AlgebraicCycle X.left ℚ) (hc : ∀ ξ ∈ γ.support, Order.coheight ξ = k)
    (v : γ.support → ℚ) (ξ : γ.support) (z : a3b4_cycleSupport X.hom γ)
    (hother : ∀ η ∈ γ.support, η ≠ ξ.val →
      z.val.underlying ∉ closure ({η} : Set X.left)) :
    localOrientation (TopCat.of (a3b4_cycleSupport X.hom γ)) (2*k)
      (properCycle_intrinsic_support_sum X k hdim γ hc v) z =
      v ξ • localOrientation (TopCat.of (a3b4_cycleSupport X.hom γ)) (2*k)
        (properCycle_intrinsic_component_on_support X γ ξ.val ξ.property k
          (properCycle_middle_component_dimension X k hdim ξ.val (hc ξ.val ξ.property))) z := by
  classical
  letI : CompactSpace X.left := a3b4_compactSpace X.hom
  letI : Fintype γ.support := (a3b2_support_finite γ).fintype
  let L := (relativeHomologyProjection ℚ (pointComplementPair (M := a3b4_cycleSupport X.hom γ) z) (2*k)).hom
  change L (∑ η : γ.support, v η •
    properCycle_intrinsic_component_on_support X γ η.val η.property k
      (properCycle_middle_component_dimension X k hdim η.val (hc η.val η.property))) = _
  rw [map_sum]
  simp only [map_smul]
  apply Finset.sum_eq_single ξ
  · intro η _ hη
    exact (congrArg (fun t => v η • t)
      (properCycle_intrinsic_support_component_point_zero X γ η.val η.property k
        (properCycle_middle_component_dimension X k hdim η.val (hc η.val η.property)) z
        (hother η.val η.property (fun h => hη (Subtype.ext h))))).trans (smul_zero _)
  · intro h
    exact (h (Finset.mem_univ ξ)).elim

/-- Original point values at isolated intrinsic holomorphic points detect every coefficient of the actual intrinsic support sum.
Source: properCycle_isolated_component_holomorphic_point; properCycle_intrinsic_support_component_point_ne_zero.
HC no distance; AV milestone no distance. -/
lemma properCycle_intrinsic_support_sum_injective
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (k : ℕ) (hdim : TopologicalSpace.dim X.left = 2*k)
    (γ : AlgebraicCycle X.left ℚ) (hc : ∀ ξ ∈ γ.support, Order.coheight ξ = k) :
    Function.Injective (properCycle_intrinsic_support_sum X k hdim γ hc) := by
  classical
  letI : CompactSpace X.left := a3b4_compactSpace X.hom
  letI : Fintype γ.support := (a3b2_support_finite γ).fintype
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro v hv
  funext ξ
  obtain ⟨e, he, y, hy, hother⟩ :=
    properCycle_isolated_component_holomorphic_point X k hdim γ hc ξ.val ξ.property
  let z := properCycle_component_support_map X γ ξ.val ξ.property y
  let L := (relativeHomologyProjection ℚ (pointComplementPair (M := a3b4_cycleSupport X.hom γ) z) (2*k)).hom
  have hzero : L (properCycle_intrinsic_support_sum X k hdim γ hc v) = 0 := by
    rw [hv, map_zero]
  have hsum := properCycle_intrinsic_support_sum_point_value X k hdim γ hc v ξ z hother
  have hn := properCycle_intrinsic_support_component_point_ne_zero X γ ξ.val ξ.property k
    (properCycle_middle_component_dimension X k hdim ξ.val (hc ξ.val ξ.property)) e he y hy hother
  exact (smul_eq_zero.mp (hsum.symm.trans hzero)).resolve_right hn

end HodgeLean.Foundations.QuotientDuality
