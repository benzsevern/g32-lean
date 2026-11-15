import HodgeLean.Foundations.Program.SchoenTowerL1bPrimeChartTransform

/-! Componentwise calculations for reduced transforms.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A centre containing no irreducible component can be removed without changing the divisor's
closure, with no irreducibility assumption on the divisor. -/
theorem s2v_l1b_divisor_dense_of_minimalPrimes {R : Type*} [CommRing R]
    (P K : Ideal R) (hK : ∀ q ∈ P.minimalPrimes, ¬ K ≤ q) :
    closure (PrimeSpectrum.zeroLocus (P : Set R) \
      PrimeSpectrum.zeroLocus (K : Set R)) = PrimeSpectrum.zeroLocus (P : Set R) := by
  apply Set.Subset.antisymm
  · exact closure_minimal Set.sdiff_subset (PrimeSpectrum.isClosed_zeroLocus _)
  · intro p hp
    change P ≤ p.asIdeal at hp
    obtain ⟨q, hq, hqp⟩ := Ideal.exists_minimalPrimes_le hp
    let z : PrimeSpectrum R := ⟨q, hq.isPrime⟩
    have hs : ({z} : Set (PrimeSpectrum R)) ⊆
        PrimeSpectrum.zeroLocus (P : Set R) \
          PrimeSpectrum.zeroLocus (K : Set R) := by
      intro t ht
      have ht' : t = z := Set.mem_singleton_iff.mp ht
      subst t
      change (P : Set R) ⊆ q ∧ ¬ (K : Set R) ⊆ q
      exact ⟨hq.le, hK q hq⟩
    apply closure_mono hs
    rw [PrimeSpectrum.closure_singleton]
    exact hqp

end HodgeLean.Foundations.Program
