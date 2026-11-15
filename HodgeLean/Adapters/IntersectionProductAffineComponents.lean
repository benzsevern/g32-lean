import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization

noncomputable section

open CategoryTheory AlgebraicGeometry Order

namespace HodgeLean.Adapters

/-- The carrier of the affine scheme spectrum is the prime spectrum. -/
def a3_specPrimeHomeo (R : Type*) [CommRing R] :
    (Spec (.of R)) ≃ₜ PrimeSpectrum R :=
  Homeomorph.refl _

/-- A component point of an affine spectrum defines a minimal prime. -/
theorem a3_spec_component_minimal {R : Type*} [CommRing R] (p : Spec (.of R))
    (hp : closure ({p} : Set (Spec (.of R))) ∈ irreducibleComponents (Spec (.of R))) :
    p.asIdeal ∈ minimalPrimes R := by
  let e := a3_specPrimeHomeo R
  change (e p).asIdeal ∈ minimalPrimes R
  rw [← PrimeSpectrum.vanishingIdeal_singleton]
  apply (PrimeSpectrum.vanishingIdeal_mem_minimalPrimes).mpr
  have hi : e '' closure ({p} : Set (Spec (.of R))) ∈
      irreducibleComponents (PrimeSpectrum R) :=
    image_mem_irreducibleComponents_of_isPreirreducible_fiber e e.continuous e.isOpenMap
      (fun _ => (Set.subsingleton_singleton.preimage e.injective).isPreirreducible)
      e.surjective hp
  rw [e.image_closure, Set.image_singleton] at hi
  simpa [e, a3_specPrimeHomeo] using hi

/-- A minimal prime of a quotient contracts to a minimal prime over the quotient ideal. -/
theorem a3_quotient_minimal_comap {R : Type*} [CommRing R] (I : Ideal R)
    (q : Ideal (R ⧸ I)) (hq : q ∈ minimalPrimes (R ⧸ I)) :
    q.comap (Ideal.Quotient.mk I) ∈ I.minimalPrimes := by
  rw [Ideal.minimalPrimes_eq_comap]
  exact ⟨q, hq, rfl⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- The coordinate prime of an affine-scheme component point is a minimal prime. -/
theorem a3_affine_component_minimal {Y : Scheme} [IsAffine Y] (y : Y)
    (hy : closure ({y} : Set Y) ∈ irreducibleComponents Y) :
    (Y.isoSpec.hom y).asIdeal ∈ minimalPrimes Γ(Y, ⊤) := by
  let e := Y.isoSpec.hom.homeomorph
  have hi : e '' closure ({y} : Set Y) ∈
      irreducibleComponents (Spec Γ(Y, ⊤)) :=
    image_mem_irreducibleComponents_of_isPreirreducible_fiber
      e e.continuous e.isOpenMap
      (fun _ => (Set.subsingleton_singleton.preimage e.injective).isPreirreducible)
      e.surjective hy
  rw [e.image_closure, Set.image_singleton] at hi
  exact a3_spec_component_minimal (Y.isoSpec.hom y) hi

/-- A component point of an affine-open scheme gives a minimal prime in the ambient section ring. -/
theorem a3_affineOpenScheme_component_minimal {X : Scheme} (U : X.affineOpens)
    (x : U.1.toScheme)
    (hx : closure ({x} : Set U.1.toScheme) ∈ irreducibleComponents U.1.toScheme) :
    (U.2.isoSpec.hom x).asIdeal ∈ minimalPrimes Γ(X, U.1) := by
  let e := U.2.isoSpec.hom.homeomorph
  have hi : e '' closure ({x} : Set U.1.toScheme) ∈
      irreducibleComponents (Spec Γ(X, U.1)) :=
    image_mem_irreducibleComponents_of_isPreirreducible_fiber e e.continuous e.isOpenMap
      (fun _ => (Set.subsingleton_singleton.preimage e.injective).isPreirreducible)
      e.surjective hx
  rw [e.image_closure, Set.image_singleton] at hi
  exact a3_spec_component_minimal (U.2.isoSpec.hom x) hi

#print axioms a3_spec_component_minimal
#print axioms a3_quotient_minimal_comap
#print axioms a3_affine_component_minimal
#print axioms a3_affineOpenScheme_component_minimal

end HodgeLean.Adapters
