import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNConormalQuotient
import Mathlib.Tactic.Ring

/-! # Orientation under inversion of a normalized paired ratio -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program.G32Native
variable {B : Type*} [CommRing B]

/-- On opposite ratio charts the normalized conormal generator acquires
exactly a minus sign. The assertion retains the original conormal map
and allows the reciprocal identity to hold modulo the old slice ideal.
This rejects an unchanged-sign transition across the two charts.
Source: Hartshorne, Algebraic Geometry, II.7.13, the two blowup charts. -/
theorem paired_c3_inverse_ratio_conormal_class
    (I J : Ideal B) (h : I ≤ J) (z z' : J)
    (hinv : (1 + z.1) * (1 + z'.1) - 1 ∈ I) :
    (Submodule.Quotient.mk (J.toCotangent z) :
      J.Cotangent ⧸ LinearMap.range (Ideal.mapCotangent I J (AlgHom.id B B) h)) =
        Submodule.Quotient.mk (J.toCotangent (-z')) := by
  apply (pairedConormalCokernelIdealEquiv I J h).injective
  rw [paired_conormal_cokernel_ideal_mk, paired_conormal_cokernel_ideal_mk]
  apply (Submodule.Quotient.eq _).mpr
  change z.1 - (-z'.1) ∈ I ⊔ J ^ 2
  have he : z.1 - (-z'.1) =
      ((1 + z.1) * (1 + z'.1) - 1) - z.1 * z'.1 := by ring
  rw [he]
  apply (I ⊔ J ^ 2).sub_mem (Submodule.mem_sup_left hinv)
  apply Submodule.mem_sup_right
  rw [pow_two]
  exact Ideal.mul_mem_mul z.property z'.property

#print axioms paired_c3_inverse_ratio_conormal_class
end HodgeLean.Foundations.Program.G32Native
