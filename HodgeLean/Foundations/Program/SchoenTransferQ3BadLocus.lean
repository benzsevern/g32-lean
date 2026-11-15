import HodgeLean.Foundations.Program.SchoenTransferQ3FlatOpen
import HodgeLean.Foundations.Program.SchoenTransferQ3RetainedCoefficients
import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.Boundary

/-! All inverse components over smooth target primes avoid the intrinsic bad set. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.Adapters AlgebraicGeometry.SingularCycles
namespace HodgeLean.Foundations.Program

/-- Every source stalk above a smooth target point is flat, so the intrinsic
bad target set contains no such point. -/
theorem s4_q3_smooth_point_not_bad
    {X W : Over (Spec ↧ℂ)} [IsIntegral X.left] [Smooth X.hom] [IsIntegral W.left]
    [LocallyOfFinitePresentation W.hom]
    (q : X ⟶ W) [IsFinite q.left]
    (hqsurj : Function.Surjective (Point.map q))
    (x : W.left) (hx : x ∈ W.hom.smoothLocus) :
    x ∉ actualBadLocus W.hom q.left := by
  let U := W.hom.smoothLocus
  have hsmooth : Smooth (U.ι ≫ W.hom) :=
    boundary_smooth_restrict W.hom U le_rfl
  letI : Surjective q.left := ⟨s2_surjective_of_point_surjective q hqsurj⟩
  letI : Flat (q.left ∣_ U) := s4_q3_finite_flat_over_smooth_open q U hsmooth
  rintro (hxs | ⟨y, hy, hyx⟩)
  · exact hxs hx
  · have hyU : q.left y ∈ U := hyx.symm ▸ hx
    have hf := Flat.stalkMap (q.left ∣_ U) ⟨y, hyU⟩
    exact hy ((RingHom.Flat.respectsIso.arrow_mk_iso_iff
      (morphismRestrictStalkMap q.left U ⟨y, hyU⟩)).mp hf)

/-- Every surviving inverse component lies above a retained smooth ambient
prime and therefore avoids the intrinsic bad target set. -/
theorem s4_q3_surviving_components_avoid_bad
    {X W : Over (Spec ↧ℂ)} [IsIntegral X.left] [Smooth X.hom]
    [QuasiCompact X.hom] [IsNoetherian X.left] [IsIntegral W.left]
    [LocallyOfFinitePresentation W.hom] [QuasiCompact W.hom]
    (q : X ⟶ W) [IsFinite q.left]
    (hqsurj : Function.Surjective (Point.map q)) (hq : IsOpenMap q.left)
    (z : AlgebraicCycle W.left ℚ)
    (hz : ∀ x ∈ z.support, ∃ V : W.left.Opens, x ∈ V ∧ Smooth (V.ι ≫ W.hom)) :
    ∀ p ∈ (ccm3_flatPullback q.left z).support,
      q.left p ∉ actualBadLocus W.hom q.left := by
  have hmem := (s4_q3_retained_smooth_open W z hz).2.2
  intro p hp
  change ccm3_flatPullback q.left z p ≠ 0 at hp
  rw [s4_q3_flatPullback_coefficient_at_image q hq z p] at hp
  exact s4_q3_smooth_point_not_bad q hqsurj (q.left p)
    (hmem _ (mul_ne_zero_iff.mp hp).1)

end HodgeLean.Foundations.Program
