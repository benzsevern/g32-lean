import HodgeLean.Foundations.Program.G32Native.PairedResidualPoleNormalization

/-! # The paired family inside the full simple-pole differential space -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open HodgeLean.Adapters
open scoped Manifold ContDiff Topology
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

/-- The full finite simple-pole space contains the supplied paired family by a germ-preserving injection. -/
theorem paired_residual_pole_envelope [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) {r : ℕ}
    (w : Fin r → b4c_MeroForm E C hE) (x : Fin r → C)
    (hres : ∀ i j, b4c_res (hE := hE) (w i) (x j) = if i = j then 1 else 0)
    (S : Finset C)
    (horder : ∀ i p, (-1 : WithTop ℤ) ≤
      meromorphicOrderAt (HurwitzPrymRR_loc hE (w i) p) 0)
    (hout : ∀ i p, p ∉ S → AnalyticAt ℂ (HurwitzPrymRR_loc hE (w i) p) 0) :
    ∃ W : Submodule ℂ (TangentBundle 𝓘(ℂ, E) C → ℂ), Module.Finite ℂ W ∧
      (∀ q, q ∈ W ↔ b4c_IsMeroForm hE q ∧
        (∀ p, ((-(1 : ℤ)) : WithTop ℤ) ≤ meromorphicOrderAt (HurwitzPrymRR_loc hE q p) 0) ∧
        (∀ p, p ∉ S → AnalyticAt ℂ (HurwitzPrymRR_loc hE q p) 0) ∧
        ∀ p ∈ S, ∀ u, q ⟨p, u⟩ = 0) ∧
      ∃ F : (b3_HolForm E C × (Fin r → ℂ)) →ₗ[ℂ] W, Function.Injective F ∧
        ∀ v p, HurwitzPrymRR_loc hE (F v).1 p =ᶠ[𝓝[≠] 0]
          HurwitzPrymRR_loc hE (s2e_pairedDifferentialLinear hE w v) p := by
  classical
  obtain ⟨W, hfin, hW⟩ := RiemannRochEichler_exists_bounded_pole_space hE S 1
  refine ⟨W, hfin, ?_, ?_⟩
  · intro q
    simpa only [Nat.cast_one] using hW q
  let A := (residual_normalize_poles (E := E) S).comp (s2e_pairedDifferentialLinear hE w)
  have hg (v : b3_HolForm E C × (Fin r → ℂ)) (p : C) :
      HurwitzPrymRR_loc hE (A v) p =ᶠ[𝓝[≠] 0]
        HurwitzPrymRR_loc hE (s2e_pairedDifferentialLinear hE w v) p :=
    residual_normalize_poles_loc hE S _ p
  have hA (v : b3_HolForm E C × (Fin r → ℂ)) : A v ∈ W := by
    have hm := s2e_pairedDifferentialLinear_isMeroForm hE w v.1 v.2
    apply (hW (A v)).mpr
    refine ⟨⟨?_, fun p => (hm.2 p).congr (hg v p).symm⟩, ?_, ?_, ?_⟩
    · intro p a u t
      change (if p ∈ S then 0 else _) =
        a * (if p ∈ S then 0 else _) + (if p ∈ S then 0 else _)
      by_cases hp : p ∈ S
      · simp only [if_pos hp, mul_zero, add_zero]
      · simp only [if_neg hp]
        exact hm.1 p a u t
    · intro p
      rw [meromorphicOrderAt_congr (hg v p)]
      have hc : ((-1 : ℤ) : WithTop ℤ) = (-1 : WithTop ℤ) := by norm_cast
      simpa only [Nat.cast_one, hc, WithTop.coe_one] using
        (s2e_pairedDifferentialLinear_simple_poles hE w horder v.1 v.2 p).2
    · intro p hp
      have hz : HurwitzPrymRR_loc hE (A v) p 0 =
          HurwitzPrymRR_loc hE (s2e_pairedDifferentialLinear hE w v) p 0 := by
        rw [RiemannRochEichler_loc_zero, RiemannRochEichler_loc_zero]
        change (if p ∈ S then 0 else _) = _
        exact if_neg hp
      exact (s2e_pairedDifferentialLinear_analyticAt hE w v.1 v.2 p
        (fun i => hout i p hp)).congr
          (eventuallyEq_nhds_of_eventuallyEq_nhdsNE (hg v p) hz).symm
    · intro p hp u
      change (if p ∈ S then 0 else _) = 0
      exact if_pos hp
  let F := A.codRestrict W hA
  refine ⟨F, ?_, fun v p => hg v p⟩
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  have hv0 : A v = 0 := congrArg Subtype.val hv
  apply s2e_pairedDifferential_germ_zero hE w x hres v.1 v.2
  intro p
  have h := (hg v p).symm
  rw [hv0] at h
  exact h

#print axioms paired_residual_pole_envelope

end HodgeLean.Foundations.Program.G32Native
