import HodgeLean.Adapters.NormalConeB4aGysinLocalTrapping

/-! # Uniform trapping for deformations against a fixed support -/

noncomputable section
namespace HodgeLean.Adapters

/-- A continuous family avoiding a fixed support outside an open subset of a
compact set continues to avoid it there for all nearby parameters. -/
theorem a3b4a_gysin_support_uniform_trapping
    {P X Y : Type*} [TopologicalSpace P] [TopologicalSpace X] [TopologicalSpace Y]
    (F : C(P × X, Y)) (p : P) (S : Set Y) (hS : IsClosed S)
    (K W : Set X) (hK : IsCompact K) (hW : IsOpen W)
    (hF : ∀ x ∈ K, F (p, x) ∈ S → x ∈ W) :
    ∃ V : Set P, IsOpen V ∧ p ∈ V ∧
      ∀ t ∈ V, ∀ x ∈ K, F (t, x) ∈ S → x ∈ W := by
  obtain ⟨V, B, hV, _, hpV, hKB, hVB⟩ := generalized_tube_lemma
    (isCompact_singleton (x := p)) (hK.diff hW)
    (hS.isOpen_compl.preimage F.continuous) (by
      rintro ⟨t, x⟩ ⟨ht, hx⟩
      have ht' : t = p := ht
      subst t
      exact fun hs => hx.2 (hF x hx.1 hs))
  refine ⟨V, hV, hpV (Set.mem_singleton p), ?_⟩
  intro t ht x hx hs
  by_contra hxW
  exact hVB ⟨ht, hKB ⟨hx, hxW⟩⟩ hs

/-- Straight parameter segments sufficiently near zero preserve the uniform
trapping region of a continuous family. -/
theorem a3b4a_gysin_support_segment_trapping
    {P X Y : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [TopologicalSpace X] [TopologicalSpace Y]
    (F : C(P × X, Y)) (S : Set Y) (hS : IsClosed S)
    (K W : Set X) (hK : IsCompact K) (hW : IsOpen W)
    (hF : ∀ x ∈ K, F (0, x) ∈ S → x ∈ W) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ a : P, ‖a‖ < ε →
      ∀ (t : unitInterval) (x : X), x ∈ K →
        F ((t : ℝ) • a, x) ∈ S → x ∈ W := by
  obtain ⟨V, hV, h0V, htrap⟩ :=
    a3b4a_gysin_support_uniform_trapping F 0 S hS K W hK hW hF
  obtain ⟨ε, hε, hεV⟩ := Metric.isOpen_iff.mp hV 0 h0V
  refine ⟨ε, hε, ?_⟩
  intro a ha t x hx hs
  apply htrap ((t : ℝ) • a) (hεV ?_) x hx hs
  rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg t.2.1]
  exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg a) t.2.2) ha

end HodgeLean.Adapters
