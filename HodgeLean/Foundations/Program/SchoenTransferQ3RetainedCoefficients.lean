import HodgeLean.Foundations.Program.SchoenTransferQ3ComponentDomination
import HodgeLean.Foundations.Program.SchoenTransferQ3Coefficients
import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.Basic

/-! Separate the target-prime contributions before collecting coefficients. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.Adapters
open scoped BigOperators Classical
namespace HodgeLean.Foundations.Program

/-- For an open map, only the prime which is the image of the source point
can contribute to its inverse-image coefficient. -/
theorem s4_q3_flatPullback_coefficient_at_image
    {X W : Over (Spec ↧ℂ)} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsNoetherian X.left]
    (q : X ⟶ W) (hq : IsOpenMap q.left)
    (z : AlgebraicCycle W.left ℚ) (p : X.left) :
    ccm3_flatPullback q.left z p = z (q.left p) *
      ccm3_flatPullbackPrime q.left (q.left p) p := by
  letI : CompactSpace W.left := QuasiCompact.compactSpace_of_compactSpace W.hom
  rw [s4_q3_flatPullback_coefficient]
  apply Finset.sum_eq_single (q.left p)
  · intro x hx hxp
    suffices h : ccm3_flatPullbackPrime q.left x p = 0 by rw [h, mul_zero]
    by_contra hn
    obtain ⟨y, hy, hyc⟩ := (ccm3_flatPullbackPrime_support q x p).mp hn
    have himage := s4_q3_inverse_component_dominates q.left hq x y hyc
    rw [hy] at himage
    exact hxp himage.symm
  · intro hn
    have hz : z (q.left p) = 0 := by
      by_contra hz
      exact hn (z.finite_support.mem_toFinset.mpr hz)
    rw [hz, zero_mul]

/-- Each unreduced inverse component has its original rational weight times
its positive generic stalk multiplicity, with no cross-prime contribution. -/
theorem s4_q3_inverse_component_coefficient
    {X W : Over (Spec ↧ℂ)} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsNoetherian X.left]
    (q : X ⟶ W) (hq : IsOpenMap q.left) (z : AlgebraicCycle W.left ℚ)
    (x : W.left) (y : (ccm3_inverseIdeal q.left x).subscheme)
    (hy : closure ({y} : Set (ccm3_inverseIdeal q.left x).subscheme) ∈
      irreducibleComponents (ccm3_inverseIdeal q.left x).subscheme) :
    ccm3_flatPullback q.left z ((ccm3_inverseIdeal q.left x).subschemeι y) =
      z x * (AlgebraicGeometry.SingularCycles.genericMultiplicity q.left x y
        (ccm3_genericLength_finite_pos q x y hy).2 : ℚ) := by
  rw [s4_q3_flatPullback_coefficient_at_image q hq,
    s4_q3_inverse_component_dominates q.left hq x y hy,
    AlgebraicGeometry.SingularCycles.prime_coefficient q x y hy]

end HodgeLean.Foundations.Program
