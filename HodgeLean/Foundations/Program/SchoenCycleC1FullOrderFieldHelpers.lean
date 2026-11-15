import HodgeLean.Foundations.Program.SchoenCycleC1CyclicPresentationHelpers

/-! # Full-order deck generators and cyclic Galois field presentations -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A field automorphism whose order equals the extension degree generates
the entire automorphism group and makes the extension cyclic Galois. -/
theorem s2e_c1_galois_cyclic_of_full_order
    {K L : Type*} [Field K] [Field L] [Algebra K L] [Module.Finite K L]
    (σ : L ≃ₐ[K] L) (horder : orderOf σ = Module.finrank K L) :
    IsGalois K L ∧ IsCyclic (L ≃ₐ[K] L) := by
  have hle : Nat.card (L ≃ₐ[K] L) ≤ Module.finrank K L := by
    simpa only [Nat.card_eq_fintype_card] using (AlgEquiv.card_le (F := K) (K := L))
  have hge : Module.finrank K L ≤ Nat.card (L ≃ₐ[K] L) := by
    rw [← horder, ← Nat.card_zpowers σ]
    exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  have hcard := Nat.le_antisymm hle hge
  have htop : Subgroup.zpowers σ = ⊤ := Subgroup.eq_top_of_card_eq _ (by
    rw [Nat.card_zpowers, horder, hcard])
  exact ⟨IsGalois.of_card_aut_eq_finrank K L hcard,
    isCyclic_iff_exists_zpowers_eq_top.mpr ⟨σ, htop⟩⟩

end HodgeLean.Foundations.Program
