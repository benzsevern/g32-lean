import HodgeLean.Foundations.Program.SchoenTowerI2bChartDensity
import HodgeLean.Foundations.Program.SchoenTowerI2bCoordinateRegular
import HodgeLean.Foundations.Program.SchoenTowerI2bChartAlgebra

/-! Density of the unpaired branch on the two algebraic blowup charts.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
open Polynomial
namespace HodgeLean.Foundations.Program

/-- A weakly regular branch triple gives denominator saturation after imposing the unpaired branch.
Source: prefix saturation of a regular sequence and reduction by the unpaired branch equation. -/
theorem s2v_i2b_regular_triple_chart_saturated
    {R : Type*} [CommRing R] (u v z : R)
    (hreg : RingTheory.Sequence.IsWeaklyRegular R [z, v, u])
    (p : R[X])
    (hp : C v * p ∈ Ideal.span {C u - X * C v} ⊔ Ideal.span {C z}) :
    p ∈ Ideal.span {C u - X * C v} ⊔ Ideal.span {C z} := by
  have hv : ∀ a : R, v * a ∈ Ideal.span {z} → a ∈ Ideal.span {z} := by
    simpa [Ideal.ofList_cons, Ideal.ofList_nil] using
      s2v_i2b_weakly_regular_prefix_saturated [z, v, u] hreg 1 (by simp)
  have hu : ∀ a : R, u * a ∈ Ideal.span {z} ⊔ Ideal.span {v} →
      a ∈ Ideal.span {z} ⊔ Ideal.span {v} := by
    simpa [Ideal.ofList_cons, Ideal.ofList_nil] using
      s2v_i2b_weakly_regular_prefix_saturated [z, v, u] hreg 2 (by simp)
  let q := Ideal.Quotient.mk (Ideal.span {z})
  have hqI : Ideal.map q (Ideal.span {z} ⊔ Ideal.span {v}) = Ideal.span {q v} := by
    rw [Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq,
      Ideal.map_span, Set.image_singleton]
  have hu' := s2v_i2b_saturation_of_surjective q Ideal.Quotient.mk_surjective
    (Ideal.span {z} ⊔ Ideal.span {v}) (by rw [Ideal.mk_ker]; exact le_sup_left) u hu
  rw [hqI] at hu'
  exact s2v_i2b_chart_relation_saturated_mod_branch u v z
    (s2v_i2b_quotient_regular_of_saturated _ v hv)
    (s2v_i2b_quotient_regular_of_saturated _ (q u) hu') p hp

/-- On the algebraic chart the unpaired divisor is the closure of its nonexceptional part.
Source: denominator saturation of the branch triple and quotient spectrum density. -/
theorem s2v_i2b_unpaired_algebraic_chart_density
    {R : Type*} [CommRing R] (u v z : R)
    (hreg : RingTheory.Sequence.IsWeaklyRegular R [z, v, u]) :
    let q := Ideal.Quotient.mk (Ideal.span {C u - X * C v})
    closure (PrimeSpectrum.zeroLocus ({q (C z)} : Set (s2v_L1bChart u v)) ∩
      (PrimeSpectrum.basicOpen (q (C v)) : Set (PrimeSpectrum (s2v_L1bChart u v)))) =
      PrimeSpectrum.zeroLocus ({q (C z)} : Set (s2v_L1bChart u v)) := by
  dsimp only
  let F : Ideal R[X] := Ideal.span {C u - X * C v}
  let q := Ideal.Quotient.mk F
  have hmap : Ideal.map q (F ⊔ Ideal.span {C z}) = Ideal.span {q (C z)} := by
    rw [Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq,
      Ideal.map_span, Set.image_singleton]
  have hs := s2v_i2b_saturation_of_surjective q Ideal.Quotient.mk_surjective
    (F ⊔ Ideal.span {C z}) (by rw [Ideal.mk_ker]; exact le_sup_left) (C v)
    (s2v_i2b_regular_triple_chart_saturated u v z hreg)
  rw [hmap] at hs
  simpa only [PrimeSpectrum.zeroLocus_span] using
    s2v_i2b_saturated_divisor_density (Ideal.span {q (C z)}) (q (C v)) hs

end HodgeLean.Foundations.Program
