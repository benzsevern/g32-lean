import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Tactic.Ring

/-! # Signed orders under a specified local ramification equation -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A local ramification equation transports a downstairs unit and signed
parameter power to an upstairs unit and the ramification-scaled signed power. -/
theorem s2e_c1_signed_order_ramification_transport
    {R S K L : Type*} [CommRing R] [CommRing S] [Field K] [Field L]
    [Algebra R K] [Algebra S L]
    (φ : R →+* S) (σ : K →+* L)
    (hσ : ∀ r, σ (algebraMap R K r) = algebraMap S L (φ r))
    (t : R) (s : S) (e : ℕ) (w : Sˣ)
    (hram : φ t = (w : S) * s ^ e)
    (f : K) (u : Rˣ) (a : ℤ)
    (hf : f = algebraMap R K (u : R) * algebraMap R K t ^ a) :
    ∃ v : Sˣ, σ f = algebraMap S L (v : S) * algebraMap S L s ^ ((e : ℤ) * a) := by
  let v : Sˣ := Units.map φ.toMonoidHom u * w ^ a
  have hwa : algebraMap S L ((w ^ a : Sˣ) : S) = algebraMap S L (w : S) ^ a := by
    change ((Units.map (algebraMap S L).toMonoidHom (w ^ a) : Lˣ) : L) = _
    rw [map_zpow, Units.val_zpow_eq_zpow_val]
    rfl
  have hv : algebraMap S L (v : S) =
      algebraMap S L (φ (u : R)) * algebraMap S L (w : S) ^ a := by
    change algebraMap S L (φ (u : R) * ((w ^ a : Sˣ) : S)) = _
    rw [map_mul, hwa]
  refine ⟨v, ?_⟩
  calc
    σ f = algebraMap S L (φ (u : R)) *
        (algebraMap S L (w : S) * algebraMap S L s ^ e) ^ a := by
      rw [hf, map_mul, map_zpow₀, hσ, hσ, hram, map_mul, map_pow]
    _ = (algebraMap S L (φ (u : R)) * algebraMap S L (w : S) ^ a) *
        algebraMap S L s ^ ((e : ℤ) * a) := by
      rw [mul_zpow, ← zpow_natCast, ← zpow_mul, mul_assoc]
    _ = algebraMap S L (v : S) * algebraMap S L s ^ ((e : ℤ) * a) := by rw [hv]

end HodgeLean.Foundations.Program
