import HodgeLean.Foundations.Program.SchoenTowerI2bCoordinateRegular
import HodgeLean.Foundations.Program.SchoenTowerI2bChartAlgebra
import HodgeLean.Foundations.Program.SchoenCycleCartierLocalization

/-! Rank-one centre ideals on the algebraic blowup charts.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Polynomial
namespace HodgeLean.Foundations.Program

/-- A weakly regular selected pair gives a free rank-one centre ideal on its chart.
Source: regularity of the chart denominator and the principal-ideal module equivalence. -/
theorem s2v_i2b_regular_pair_chart_centre_free
    {R : Type*} [CommRing R] (u v : R)
    (hreg : RingTheory.Sequence.IsWeaklyRegular R [v, u]) :
    let q := Ideal.Quotient.mk (Ideal.span {C u - X * C v})
    Nonempty ((Ideal.span {q (C u), q (C v)}) ≃ₗ[s2v_L1bChart u v]
      s2v_L1bChart u v) := by
  dsimp only
  rw [s2v_l1b_chart_centre_principal]
  have hv := ((RingTheory.Sequence.isWeaklyRegular_cons_iff R v [u]).mp hreg).1
  have hu : ∀ a : R, u * a ∈ Ideal.span {v} → a ∈ Ideal.span {v} := by
    simpa [Ideal.ofList_cons, Ideal.ofList_nil] using
      s2v_i2b_weakly_regular_prefix_saturated [v, u] hreg 1 (by simp)
  have hden := s2v_i2b_chart_denominator_regular u v hv
    (s2v_i2b_quotient_regular_of_saturated _ u hu)
  apply s2e_regular_principal_ideal_free
  simpa only [mul_comm] using hden

/-- A ring isomorphism transports a free rank-one ideal to its image ideal.
Source: a regular principal generator for a free ideal and cancellation through the isomorphism. -/
theorem s2v_i2b_free_ideal_map_equiv
    {R A : Type*} [CommRing R] [CommRing A] (f : R ≃+* A) (I : Ideal R)
    (hI : Nonempty (I ≃ₗ[R] R)) :
    Nonempty ((Ideal.map (f : R →+* A) I) ≃ₗ[A] A) := by
  obtain ⟨e⟩ := hI
  obtain ⟨z, hz, hregular⟩ := s2e_free_ideal_regular_generator I e
  rw [hz, Ideal.map_span, Set.image_singleton]
  apply s2e_regular_principal_ideal_free
  intro a b hab
  obtain ⟨a, rfl⟩ := f.surjective a
  obtain ⟨b, rfl⟩ := f.surjective b
  apply congrArg f
  apply hregular
  apply f.injective
  simpa only [map_mul, RingEquiv.coe_toRingHom] using hab

end HodgeLean.Foundations.Program
