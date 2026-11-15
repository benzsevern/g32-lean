import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Ideal.Maps

/-! # Noetherian descent through ideal contraction -/
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Ideal extension with a contraction inverse descends the ascending chain condition.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 6,
Proposition 6.1, the ascending chain criterion. -/
theorem s2e_isNoetherianRing_of_ideal_contraction
    {R A : Type*} [CommRing R] [CommRing A] [hA : IsNoetherianRing A]
    (f : R →+* A) (hc : ∀ J : Ideal R, (J.map f).comap f = J) :
    IsNoetherianRing R := by
  let e : Ideal R ↪o Ideal A := OrderEmbedding.ofMapLEIff (fun J => J.map f) (by
    intro I J
    constructor
    · intro h
      have h' := Ideal.comap_mono (f := f) h
      simpa only [hc] using h'
    · exact Ideal.map_mono)
  exact isNoetherian_mk (OrderEmbedding.wellFounded e.dual hA.wf)

#print axioms s2e_isNoetherianRing_of_ideal_contraction
end HodgeLean.Foundations.Program
