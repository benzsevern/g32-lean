import HodgeLean.Foundations.Program.SchoenTowerN2bDenominators
import Mathlib.Algebra.Field.Basic

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Localized lifts of a finite family of rational elements have one common denominator power. -/
theorem n2b_common_rational_representatives
    {ι κ : Type} [Fintype ι] [Fintype κ]
    {K : Type} [CommRing K]
    (R : ι → Type) [∀ i, CommRing (R i)] [∀ i, Algebra (R i) K]
    (L : κ → ι → Type) [∀ k i, CommRing (L k i)]
    [∀ k i, Algebra (R i) (L k i)]
    (s : ∀ k i, R i) [∀ k i, IsLocalization.Away (s k i) (L k i)]
    (φ : ∀ k i, L k i →+* K)
    (hφ : ∀ k i a, φ k i (algebraMap (R i) (L k i) a) = algebraMap (R i) K a)
    (z : κ → K) (v : ∀ k i, L k i) (hv : ∀ k i, φ k i (v k i) = z k) :
    ∃ N : ℕ, ∀ k i, ∃ a : R i,
      z k * algebraMap (R i) K (s k i) ^ N = algebraMap (R i) K a := by
  obtain ⟨N, hN⟩ := n2b_common_localization_exponent
    (fun p : κ × ι => R p.2) (fun p : κ × ι => L p.1 p.2)
    (fun p => s p.1 p.2) (fun p => v p.1 p.2)
  refine ⟨N, fun k i => ?_⟩
  obtain ⟨a, ha⟩ := hN (k, i)
  refine ⟨a, ?_⟩
  have h := congrArg (φ k i) ha
  simpa only [map_mul, map_pow, hφ, hv] using h

end HodgeLean.Foundations.Program
