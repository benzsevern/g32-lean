import HodgeLean.Adapters.NormalConeB4aGysinChartIsolation

noncomputable section
namespace HodgeLean.Adapters
open Topology

/-- Compactness traps every nearby chart intersection in a prescribed
source neighborhood and identifies it with its normal coordinate. -/
theorem a3b4a_gysin_chart_trapped_intersection_equiv
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {n c : ℕ} (f : X → Y) (hf : IsClosedEmbedding f)
    (g : X → (Fin n → ℂ))
    (Φ : OpenPartialHomeomorph Y ((Fin n → ℂ) × (Fin c → ℂ)))
    (hcoord : ∀ w, f w ∈ Φ.source → (Φ (f w)).1 = g w)
    (w₀ : X) (hw₀ : f w₀ ∈ Φ.source) (hΦ₀ : Φ (f w₀) = 0)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hball : ∀ v ∈ Metric.closedBall (0 : Fin c → ℂ) ρ,
      ((0 : Fin n → ℂ), v) ∈ Φ.target)
    (hisolate : ∀ v ∈ Metric.closedBall (0 : Fin c → ℂ) ρ,
      Φ.symm (0, v) ∈ Set.range f → v = 0) :
    ∃ N₁ : Set X, IsOpen N₁ ∧ w₀ ∈ N₁ ∧
      ∀ N : Set X, IsOpen N → w₀ ∈ N → N ⊆ N₁ →
        ∃ δ : ℝ, 0 < δ ∧ ∀ a : Fin n → ℂ, ‖a‖ < δ →
          ∃ E : {w : X // w ∈ N ∧ g w = a} ≃
            {v : Fin c → ℂ // v ∈ Metric.ball 0 ρ ∧ (a, v) ∈ Φ.target ∧
              Φ.symm (a, v) ∈ Set.range f},
            ∀ w, Φ.symm (a, (E w).val) = f w.val := by
  classical
  let D := {z : (Fin n → ℂ) × (Fin c → ℂ) | ‖z.2‖ < ρ}
  have hD : IsOpen D := isOpen_lt (continuous_norm.comp continuous_snd) continuous_const
  let N₁ := f ⁻¹' (Φ.source ∩ Φ ⁻¹' D)
  have hN₁ : IsOpen N₁ :=
    (Φ.continuousOn.isOpen_inter_preimage Φ.open_source hD).preimage hf.continuous
  have hw₁ : w₀ ∈ N₁ := by
    refine ⟨hw₀, ?_⟩
    change ‖(Φ (f w₀)).2‖ < ρ
    rw [hΦ₀]
    change ‖(0 : Fin c → ℂ)‖ < ρ
    rwa [norm_zero]
  refine ⟨N₁, hN₁, hw₁, ?_⟩
  intro N hN hwN hNN₁
  let C := f '' Nᶜ
  have hC : IsClosed C := hf.isClosedMap _ hN.isClosed_compl
  let O := Φ.target ∩ Φ.symm ⁻¹' Cᶜ
  have hO : IsOpen O :=
    Φ.continuousOn_symm.isOpen_inter_preimage Φ.open_target hC.isOpen_compl
  have hsymm0 : Φ.symm (0 : (Fin n → ℂ) × (Fin c → ℂ)) = f w₀ := by
    rw [← hΦ₀]
    exact Φ.left_inv hw₀
  have hzero : ({(0 : Fin n → ℂ)} ×ˢ Metric.closedBall (0 : Fin c → ℂ) ρ) ⊆ O := by
    rintro ⟨a, v⟩ ⟨ha, hv⟩
    have ha' : a = 0 := ha
    subst a
    refine ⟨hball v hv, ?_⟩
    rintro ⟨w, hn, hw⟩
    have hv0 := hisolate v hv ⟨w, hw⟩
    rw [hv0] at hw
    have hww := hf.injective (hw.trans hsymm0)
    exact hn (hww.symm ▸ hwN)
  obtain ⟨V, B, hV, _, h0V, hKB, hVB⟩ := generalized_tube_lemma
    (isCompact_singleton (x := (0 : Fin n → ℂ)))
    (isCompact_closedBall (0 : Fin c → ℂ) ρ) hO hzero
  obtain ⟨δ, hδ, hδV⟩ := Metric.isOpen_iff.mp hV 0 (h0V (Set.mem_singleton 0))
  refine ⟨δ, hδ, ?_⟩
  intro a ha
  have hsmall (v : Fin c → ℂ) (hv : v ∈ Metric.closedBall 0 ρ) :
      (a, v) ∈ O := by
    apply hVB
    refine ⟨hδV ?_, hKB hv⟩
    simpa only [Metric.mem_ball, dist_zero_right] using ha
  let W := {w : X // w ∈ N ∧ g w = a}
  let Z := {v : Fin c → ℂ // v ∈ Metric.ball 0 ρ ∧ (a, v) ∈ Φ.target ∧
    Φ.symm (a, v) ∈ Set.range f}
  have hsource (w : W) : f w.val ∈ Φ.source := (hNN₁ w.property.1).1
  have hpair (w : W) : Φ (f w.val) = (a, (Φ (f w.val)).2) :=
    Prod.ext ((hcoord w.val (hsource w)).trans w.property.2) rfl
  have htarget (w : W) : (a, (Φ (f w.val)).2) ∈ Φ.target := by
    rw [← hpair w]
    exact Φ.map_source (hsource w)
  have hinverse (w : W) : Φ.symm (a, (Φ (f w.val)).2) = f w.val := by
    rw [← hpair w]
    exact Φ.left_inv (hsource w)
  let e : W → Z := fun w => ⟨(Φ (f w.val)).2, by
    refine ⟨?_, htarget w, ⟨w.val, (hinverse w).symm⟩⟩
    rw [Metric.mem_ball, dist_zero_right]
    exact (hNN₁ w.property.1).2⟩
  have he (w : W) : Φ.symm (a, (e w).val) = f w.val := hinverse w
  have hinj : Function.Injective e := by
    intro w w' h
    apply Subtype.ext
    apply hf.injective
    exact (he w).symm.trans ((congrArg (fun v => Φ.symm (a, v))
      (congrArg Subtype.val h)).trans (he w'))
  have hsurj : Function.Surjective e := by
    intro v
    obtain ⟨w, hw⟩ := v.property.2.2
    have hwN' : w ∈ N := by
      by_contra hn
      exact (hsmall v.val (Metric.ball_subset_closedBall v.property.1)).2 ⟨w, hn, hw⟩
    have hs : f w ∈ Φ.source := by
      rw [hw]
      exact Φ.map_target v.property.2.1
    have hp : Φ (f w) = (a, v.val) := by
      rw [hw]
      exact Φ.right_inv v.property.2.1
    have hg : g w = a := (hcoord w hs).symm.trans (congrArg Prod.fst hp)
    refine ⟨⟨w, hwN', hg⟩, ?_⟩
    apply Subtype.ext
    exact congrArg Prod.snd hp
  exact ⟨Equiv.ofBijective e ⟨hinj, hsurj⟩, he⟩

end HodgeLean.Adapters
