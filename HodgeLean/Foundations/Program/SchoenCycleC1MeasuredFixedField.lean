import Mathlib.FieldTheory.Galois.Basic

/-! # Fixed elements of a faithful deck group of measured degree -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A faithful finite group with cardinality equal to the field degree
identifies exactly the base field as its fixed elements. -/
theorem s2e_c1_measured_deck_fixed_field
    {K L G : Type*} [Field K] [Field L] [Algebra K L] [Module.Finite K L]
    [Group G] [Finite G] (ρ : G →* (L ≃ₐ[K] L)) (hρ : Function.Injective ρ)
    (hdeg : Module.finrank K L = Nat.card G) (z : L) :
    (∀ g, ρ g z = z) ↔ ∃ a : K, algebraMap K L a = z := by
  have hle : Nat.card (L ≃ₐ[K] L) ≤ Module.finrank K L := by
    simpa only [Nat.card_eq_fintype_card] using (AlgEquiv.card_le (F := K) (K := L))
  have hb : Function.Bijective ρ := hρ.bijective_of_nat_card_le (hdeg ▸ hle)
  have hc : Nat.card (L ≃ₐ[K] L) = Module.finrank K L :=
    (Nat.card_eq_of_bijective ρ hb).symm.trans hdeg.symm
  letI : IsGalois K L := IsGalois.of_card_aut_eq_finrank K L hc
  change (∀ g, ρ g z = z) ↔ z ∈ Set.range (algebraMap K L)
  rw [IsGalois.mem_range_algebraMap_iff_fixed]
  constructor
  · intro h σ
    obtain ⟨g, rfl⟩ := hb.surjective σ
    exact h g
  · intro h g
    exact h (ρ g)

end HodgeLean.Foundations.Program
