import HodgeLean.Foundations.Program.SchoenTransferQ3RetainedComponentCalculation
import HodgeLean.Foundations.Program.SchoenTransferQ3ComponentOpenNormalization
import HodgeLean.Foundations.Program.SchoenTransferQ3CycleCodimension

/-! Normalization of the original supported pullback on the actual weighted inverse cycle. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The actual finite open pullback of a generically smooth supported cycle
class is normalized on the original unreduced weighted inverse cycle. -/
theorem s4_q3_finite_open_pullback_isCycleClass
    {X W : Over (Spec ↧ℂ)} [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral W.left] [IsProjective W.hom]
    (q : X ⟶ W) [IsFinite q.left] [Surjective q.left] (hq : IsOpenMap q.left)
    (z : AlgebraicCycle W.left ℚ) (k : ℕ)
    (hz : ∀ x ∈ z.support, Order.coheight x = k ∧
      ∃ A : W.left.Opens, x ∈ A ∧ Smooth (A.ι ≫ W.hom))
    (hS : ∀ a, Point.map q a ∈ a3b4_cycleSupport W.hom z →
      a ∈ a3b4_cycleSupport X.hom (ccm3_flatPullback q.left z))
    (α : RelativeCohomology ℚ (TopPair.ofSubset (X := TopCat.of (ComplexPoint W))
      (a3b4_cycleSupport W.hom z)ᶜ) (2 * k))
    (hα : a3b4_IsCycleClass W.hom z k α) :
    a3b4_IsCycleClass X.hom (ccm3_flatPullback q.left z) k
      (relativeCohomologyMap ℚ (2 * k)
        (a3b4_supportPairMap (TopCat.ofHom (Point.continuousMap q))
          (a3b4_cycleSupport X.hom (ccm3_flatPullback q.left z)) (a3b4_cycleSupport W.hom z) hS) α) := by
  letI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  letI : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  letI : IsNoetherian X.left := {}
  let γ := ccm3_flatPullback q.left z
  have hγ : ∀ p ∈ γ.support, Order.coheight p = k :=
    s4_q3_flatPullback_pure_coheight q hq z k (fun p hp => (hz p hp).1)
  apply s4_q3_normalized_of_component_open_calculations X γ k hγ
  intro p hp
  have hn : ccm3_flatPullback q.left z p ≠ 0 := hp
  rw [s4_q3_flatPullback_coefficient_at_image q hq z p] at hn
  have hx : q.left p ∈ z.support := (mul_ne_zero_iff.mp hn).1
  have hprime : ccm3_flatPullbackPrime q.left (q.left p) p ≠ 0 := (mul_ne_zero_iff.mp hn).2
  obtain ⟨η, hηp, hη⟩ := (ccm3_flatPullbackPrime_support q (q.left p) p).mp hprime
  have hcalc := s4_q3_retained_component_open_normal_calculation q hq z k hz hS α hα
    (q.left p) hx η hη
  dsimp only at hcalc
  rw [hηp] at hcalc
  obtain ⟨U, hpU, hU⟩ := hcalc
  refine ⟨U, hpU, ?_⟩
  intro a haU haC hother
  change a.underlying ∈ closure ({p} : Set X.left) at haC
  exact hU a haU haC hother

end HodgeLean.Foundations.Program
