import HodgeLean.Foundations.Program.SchoenTransferQ3RetainedCoefficients
import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.Support

/-! The entire weighted support under the retained open map. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.Adapters AlgebraicGeometry.SingularCycles
open scoped Classical
namespace HodgeLean.Foundations.Program

/-- Prime separation prevents cancellation from removing an inverse component,
so the weighted analytic support is the full inverse image. -/
theorem s4_q3_flatPullback_support_preimage
    {X W : Over (Spec ↧ℂ)} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsNoetherian X.left]
    (q : X ⟶ W) (hq : IsOpenMap q.left) (z : AlgebraicCycle W.left ℚ) :
    a3b4_cycleSupport X.hom (ccm3_flatPullback q.left z) =
      Point.map q ⁻¹' a3b4_cycleSupport W.hom z := by
  ext t
  simp only [a3b4_cycleSupport, Set.mem_preimage, Set.mem_iUnion]
  constructor
  · rintro ⟨p, hp, htp⟩
    change ccm3_flatPullback q.left z p ≠ 0 at hp
    rw [s4_q3_flatPullback_coefficient_at_image q hq z p] at hp
    refine ⟨q.left p, (mul_ne_zero_iff.mp hp).1, ?_⟩
    change q.left t.underlying ∈ closure ({q.left p} : Set W.left)
    exact specializes_iff_mem_closure.mp
      ((specializes_iff_mem_closure.mpr htp).map q.left.continuous)
  · rintro ⟨x, hzx, htx⟩
    have htJ : t.underlying ∈ (ccm3_inverseIdeal q.left x).support := by
      rw [ccm3_inverseIdeal, Scheme.IdealSheafData.support_comap]
      change q.left t.underlying ∈ ((ccm3_primeIdeal W.left x).support : Set W.left)
      rw [ccm3_primeIdeal, Scheme.IdealSheafData.coe_support_vanishingIdeal]
      exact htx
    have htunion : t.underlying ∈
        ⋃ p ∈ (ccm3_flatPullbackPrime q.left x).support, closure ({p} : Set X.left) := by
      rw [prime_cycle_algebraic_support q x]
      exact htJ
    obtain ⟨p, hp, htp⟩ := Set.mem_iUnion₂.mp htunion
    have himage : q.left p = x := by
      obtain ⟨y, hy, hyc⟩ := (ccm3_flatPullbackPrime_support q x p).mp hp
      simpa only [hy] using s4_q3_inverse_component_dominates q.left hq x y hyc
    refine ⟨p, ?_, htp⟩
    change ccm3_flatPullback q.left z p ≠ 0
    rw [s4_q3_flatPullback_coefficient_at_image q hq z p, himage]
    exact mul_ne_zero hzx hp

end HodgeLean.Foundations.Program
