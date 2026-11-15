import HodgeLean.Foundations.Program.SchoenCycleC1MeasuredFixedField
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-! # Descent of regular invariants to the normal base ring -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.Program

/-- Regular invariants descend to the normal base ring when the compatible
faithful generic action has cardinality equal to the measured field degree. -/
theorem s2e_c1_normal_regular_invariant_descent
    {R S K L G : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing S] [IsDomain S] [Algebra R S] [Algebra.IsIntegral R S]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra S L] [IsFractionRing S L]
    [Algebra R L] [IsScalarTower R S L] [Algebra K L] [IsScalarTower R K L]
    [Module.Finite K L] [Group G] [Finite G]
    (τ : G → S ≃ₐ[R] S) (ρ : G →* (L ≃ₐ[K] L)) (hρ : Function.Injective ρ)
    (hdeg : Module.finrank K L = Nat.card G)
    (hcompat : ∀ g b, ρ g (algebraMap S L b) = algebraMap S L (τ g b)) (b : S) :
    (∀ g, τ g b = b) ↔ ∃ r : R, algebraMap R S r = b := by
  constructor
  · intro hb
    have hfixed (g : G) : ρ g (algebraMap S L b) = algebraMap S L b := by
      rw [hcompat, hb]
    obtain ⟨a, ha⟩ := (s2e_c1_measured_deck_fixed_field ρ hρ hdeg _).mp hfixed
    have hi : IsIntegral R (algebraMap S L b) :=
      (Algebra.IsIntegral.isIntegral b).map (IsScalarTower.toAlgHom R S L)
    have hai : IsIntegral R a := by
      apply (isIntegral_algHom_iff (IsScalarTower.toAlgHom R K L)
        (RingHom.injective (algebraMap K L))).mp
      change IsIntegral R (algebraMap K L a)
      rw [ha]
      exact hi
    obtain ⟨r, hr⟩ := (isIntegrallyClosed_iff K).mp inferInstance hai
    refine ⟨r, ?_⟩
    apply IsFractionRing.injective S L
    calc
      algebraMap S L (algebraMap R S r) = algebraMap R L r :=
        (IsScalarTower.algebraMap_apply R S L r).symm
      _ = algebraMap K L (algebraMap R K r) := IsScalarTower.algebraMap_apply R K L r
      _ = algebraMap S L b := by rw [hr, ha]
  · rintro ⟨r, rfl⟩ g
    exact (τ g).commutes r

end HodgeLean.Foundations.Program
