import HodgeLean.Adapters.NormalConeB4aGysinSourceConservation

noncomputable section
namespace HodgeLean.Adapters
open Topology

/-- A local exact fibre sum transports along an open embedding with
compatible parameters and termwise quotient lengths. -/
theorem a3b4a_gysin_openEmbedding_length_conservation
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {n : ℕ} (π : X → Y) (hπ : IsOpenEmbedding π)
    (gX : X → (Fin n → ℂ)) (gY : Y → (Fin n → ℂ))
    (hparam : ∀ x, gY (π x) = gX x)
    (ℓX : (Fin n → ℂ) → X → ℕ∞) (ℓY : (Fin n → ℂ) → Y → ℕ∞)
    (hweight : ∀ a x, gX x = a → ℓY a (π x) = ℓX a x)
    (x₀ : X) (m : ℕ∞)
    (hcons : ∃ N₀ : Set X, IsOpen N₀ ∧ x₀ ∈ N₀ ∧
      ∀ N : Set X, IsOpen N → x₀ ∈ N → N ⊆ N₀ →
        ∃ δ : ℝ, 0 < δ ∧ ∀ a : Fin n → ℂ, ‖a‖ < δ →
          ∃ T : Finset X, (∀ x, x ∈ T ↔ x ∈ N ∧ gX x = a) ∧
            ∑ x ∈ T, ℓX a x = m) :
    ∃ N₀ : Set Y, IsOpen N₀ ∧ π x₀ ∈ N₀ ∧
      ∀ N : Set Y, IsOpen N → π x₀ ∈ N → N ⊆ N₀ →
        ∃ δ : ℝ, 0 < δ ∧ ∀ a : Fin n → ℂ, ‖a‖ < δ →
          ∃ T : Finset Y, (∀ y, y ∈ T ↔ y ∈ N ∧ gY y = a) ∧
            ∑ y ∈ T, ℓY a y = m := by
  classical
  obtain ⟨N₀, hN₀, hxN₀, hc⟩ := hcons
  refine ⟨π '' N₀, hπ.isOpenMap _ hN₀, ⟨x₀, hxN₀, rfl⟩, ?_⟩
  intro N hN hxN hNN₀
  let M := π ⁻¹' N
  have hM : IsOpen M := hN.preimage hπ.continuous
  have hMM₀ : M ⊆ N₀ := by
    intro x hx
    obtain ⟨z, hz, hzx⟩ := hNN₀ hx
    have hzx' : z = x := hπ.injective hzx
    exact hzx' ▸ hz
  obtain ⟨δ, hδ, hδc⟩ := hc M hM hxN hMM₀
  refine ⟨δ, hδ, ?_⟩
  intro a ha
  obtain ⟨T, hT, hsum⟩ := hδc a ha
  refine ⟨T.image π, ?_, ?_⟩
  · intro y
    constructor
    · intro hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      have hxt := (hT x).mp hx
      exact ⟨hxt.1, (hparam x).trans hxt.2⟩
    · rintro ⟨hyN, hgy⟩
      obtain ⟨x, _, hxy⟩ := hNN₀ hyN
      have hxN : x ∈ M := by
        change π x ∈ N
        rw [hxy]
        exact hyN
      have hg : gX x = a := (hparam x).symm.trans ((congrArg gY hxy).trans hgy)
      exact Finset.mem_image.mpr ⟨x, (hT x).mpr ⟨hxN, hg⟩, hxy⟩
  · calc
      ∑ y ∈ T.image π, ℓY a y = ∑ x ∈ T, ℓY a (π x) :=
        Finset.sum_image (fun _ _ _ _ h => hπ.injective h)
      _ = ∑ x ∈ T, ℓX a x := by
        apply Finset.sum_congr rfl
        intro x hx
        exact hweight a x ((hT x).mp hx).2
      _ = m := hsum

end HodgeLean.Adapters
