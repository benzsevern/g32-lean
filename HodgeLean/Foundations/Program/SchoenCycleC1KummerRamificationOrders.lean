import HodgeLean.Foundations.Program.SchoenCycleC1SignedDvrOrderUniqueness
import HodgeLean.Foundations.Program.SchoenCycleC1RamificationOrderTransport

/-! # Exact signed-order relation for a local Kummer coefficient -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Comparing both actual local decompositions in a Kummer power equation
gives degree times upstairs order equal to ramification times downstairs order. -/
theorem s2e_c1_kummer_ramification_order_relation
    {R S K L : Type*} [CommRing R] [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Field L] [Algebra R K] [Algebra S L] [IsFractionRing S L]
    (φ : R →+* S) (σ : K →+* L)
    (hσ : ∀ r, σ (algebraMap R K r) = algebraMap S L (φ r))
    (t : R) (s : S) (hs : Irreducible s) (e : ℕ) (w : Sˣ)
    (hram : φ t = (w : S) * s ^ e)
    (f : K) (z : L) (m : ℕ) (u : Rˣ) (v : Sˣ) (a r : ℤ)
    (hf : f = algebraMap R K (u : R) * algebraMap R K t ^ a)
    (hz : z = algebraMap S L (v : S) * algebraMap S L s ^ r)
    (hpower : z ^ m = σ f) : (m : ℤ) * r = (e : ℤ) * a := by
  obtain ⟨v', hv'⟩ := s2e_c1_signed_order_ramification_transport φ σ hσ t s e w hram f u a hf
  have hpow : z ^ m = algebraMap S L ((v ^ m : Sˣ) : S) *
      algebraMap S L s ^ ((m : ℤ) * r) := by
    rw [hz, mul_pow, Units.val_pow_eq_pow_val, map_pow]
    congr 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm r (m : ℤ)]
  exact s2e_c1_signed_dvr_order_unique s hs (v ^ m) v' ((m : ℤ) * r) ((e : ℤ) * a)
    (hpow.symm.trans (hpower.trans hv'))

end HodgeLean.Foundations.Program
