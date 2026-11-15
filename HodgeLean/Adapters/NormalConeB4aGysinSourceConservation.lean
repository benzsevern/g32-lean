import HodgeLean.Adapters.NormalConeB4aGysinParameterTrappedLength

noncomputable section
namespace HodgeLean.Adapters
open Topology

/-- Exact fibre sums transfer through a source chart that is an open
embedding, using an injective comparison-base chart over the parameters. -/
theorem a3b4a_gysin_source_chart_length_conservation
    {X Y B : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace B]
    {n : ℕ} (π : X → Y) (hπ : Continuous π) (β : X → B)
    (b : B → (Fin n → ℂ)) (g : Y → (Fin n → ℂ))
    (V : Set X) (hV : IsOpen V)
    (hπV : IsOpenEmbedding (fun x : V => π x.val))
    (D : Set B) (hb : Set.InjOn b D) (hβV : ∀ x ∈ V, β x ∈ D)
    (hcomm : ∀ x, b (β x) = g (π x))
    (x₀ : X) (hx₀ : x₀ ∈ V)
    (U : Set (Fin n → ℂ)) (F : (Fin n → ℂ) → B)
    (hFD : ∀ a ∈ U, F a ∈ D) (hbF : ∀ a ∈ U, b (F a) = a)
    (ℓX : B → X → ℕ∞) (ℓY : (Fin n → ℂ) → Y → ℕ∞) (m : ℕ∞)
    (hweight : ∀ a ∈ U, ∀ x ∈ V, β x = F a → ℓY a (π x) = ℓX (F a) x)
    (hcons : ∀ M : Set X, IsOpen M → x₀ ∈ M →
      ∃ δ : ℝ, 0 < δ ∧ ∀ a : Fin n → ℂ, ‖a‖ < δ → a ∈ U ∧
        ∃ T : Finset X, (∀ x, x ∈ T ↔ x ∈ M ∧ β x = F a) ∧
          ∑ x ∈ T, ℓX (F a) x = m) :
    ∃ N₀ : Set Y, IsOpen N₀ ∧ π x₀ ∈ N₀ ∧
      ∀ N : Set Y, IsOpen N → π x₀ ∈ N → N ⊆ N₀ →
        ∃ δ : ℝ, 0 < δ ∧ ∀ a : Fin n → ℂ, ‖a‖ < δ →
          ∃ T : Finset Y, (∀ y, y ∈ T ↔ y ∈ N ∧ g y = a) ∧
            ∑ y ∈ T, ℓY a y = m := by
  classical
  let N₀ := Set.range (fun x : V => π x.val)
  have hN₀ : IsOpen N₀ := hπV.isOpen_range
  refine ⟨N₀, hN₀, ⟨⟨x₀, hx₀⟩, rfl⟩, ?_⟩
  intro N hN hxN hNN₀
  let M := V ∩ π ⁻¹' N
  have hM : IsOpen M := hV.inter (hN.preimage hπ)
  have hxM : x₀ ∈ M := ⟨hx₀, hxN⟩
  obtain ⟨δ, hδ, hδcons⟩ := hcons M hM hxM
  refine ⟨δ, hδ, ?_⟩
  intro a ha
  obtain ⟨haU, T, hT, hsum⟩ := hδcons a ha
  have hTV (x : X) (hx : x ∈ T) : x ∈ V := ((hT x).mp hx).1.1
  have hinj (x : X) (hx : x ∈ T) (x' : X) (hx' : x' ∈ T)
      (heq : π x = π x') : x = x' := by
    have hs : (⟨x, hTV x hx⟩ : V) = ⟨x', hTV x' hx'⟩ := hπV.injective heq
    exact congrArg Subtype.val hs
  refine ⟨T.image π, ?_, ?_⟩
  · intro y
    constructor
    · intro hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      have hxt := (hT x).mp hx
      refine ⟨hxt.1.2, ?_⟩
      exact (hcomm x).symm.trans ((congrArg b hxt.2).trans (hbF a haU))
    · rintro ⟨hyN, hgy⟩
      obtain ⟨x, hx⟩ := hNN₀ hyN
      change π x.val = y at hx
      have hβ : β x.val = F a := by
        apply hb (hβV x.val x.property) (hFD a haU)
        rw [hcomm, hx, hgy, hbF a haU]
      apply Finset.mem_image.mpr
      refine ⟨x.val, (hT x.val).mpr ⟨⟨x.property, ?_⟩, hβ⟩, hx⟩
      change π x.val ∈ N
      rw [hx]
      exact hyN
  · calc
      ∑ y ∈ T.image π, ℓY a y = ∑ x ∈ T, ℓY a (π x) := Finset.sum_image hinj
      _ = ∑ x ∈ T, ℓX (F a) x := by
        apply Finset.sum_congr rfl
        intro x hx
        exact hweight a haU x (hTV x hx) ((hT x).mp hx).2
      _ = m := hsum

end HodgeLean.Adapters
