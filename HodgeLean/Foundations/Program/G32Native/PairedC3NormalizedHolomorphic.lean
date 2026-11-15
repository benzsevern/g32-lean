import HodgeLean.Foundations.Program.G32Native.PairedResidualPoleNormalization

/-! # Holomorphic directions in the full normalized pole space -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open HodgeLean.Adapters HodgeLean.Foundations.Program Filter
open scoped Manifold ContDiff Topology BigOperators
namespace HodgeLean.Foundations.Program.G32Native
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
  [T2Space C] [CompactSpace C] [ConnectedSpace C]

/-- Normalizing a holomorphic form gives a member of the full allowed
simple-pole space, preserving every punctured germ.
Source: Forster, Lectures on Riemann Surfaces, §18. -/
def pairedC3NormalizedHolomorphicMap (h : Module.finrank ℂ E = 1)
    (n : ℕ) (y : Fin n → C)
    (W : Submodule ℂ (TangentBundle 𝓘(ℂ, E) C → ℂ))
    (hW : ∀ q, q ∈ W ↔ b4c_IsMeroForm h q ∧
      (∀ p, (-1 : WithTop ℤ) ≤ meromorphicOrderAt (HurwitzPrymRR_loc h q p) 0) ∧
      (∀ p ∉ Set.range y, AnalyticAt ℂ (HurwitzPrymRR_loc h q p) 0) ∧
      ∀ p ∈ Set.range y, ∀ u, q ⟨p, u⟩ = 0) :
    b3_HolForm E C →ₗ[ℂ] W := by
  classical
  let S := Finset.univ.image y
  have hS (p : C) : p ∈ S ↔ p ∈ Set.range y := by simp [S]
  let A := (residual_normalize_poles (E := E) S).comp (b3_HolForm E C).subtype
  refine A.codRestrict W (fun v => ?_)
  have hg (p : C) : HurwitzPrymRR_loc h (A v) p =ᶠ[𝓝[≠] 0]
      HurwitzPrymRR_loc h v.val p := residual_normalize_poles_loc h S v.val p
  apply (hW (A v)).mpr
  refine ⟨⟨?_, fun p => (RiemannRochAna_hol_isMeroForm h v).2 p |>.congr (hg p).symm⟩,
    ?_, ?_, ?_⟩
  · intro p a u t
    change (if p ∈ S then 0 else _) =
      a * (if p ∈ S then 0 else _) + (if p ∈ S then 0 else _)
    by_cases hp : p ∈ S
    · simp only [if_pos hp, mul_zero, add_zero]
    · simp only [if_neg hp]
      exact (RiemannRochAna_hol_isMeroForm h v).1 p a u t
  · intro p
    rw [meromorphicOrderAt_congr (hg p)]
    have hn : (-1 : WithTop ℤ) ≤ 0 := by
      change ((-1 : ℤ) : WithTop ℤ) ≤ ((0 : ℤ) : WithTop ℤ)
      exact_mod_cast (show (-1 : ℤ) ≤ 0 by omega)
    exact hn.trans (RiemannRochEichler_loc_analytic h v p).meromorphicOrderAt_nonneg
  · intro p hp
    have hz : HurwitzPrymRR_loc h (A v) p 0 = HurwitzPrymRR_loc h v.val p 0 := by
      rw [RiemannRochEichler_loc_zero, RiemannRochEichler_loc_zero]
      change (if p ∈ S then 0 else _) = _
      exact if_neg (fun hpS => hp ((hS p).mp hpS))
    exact (RiemannRochEichler_loc_analytic h v p).congr
      (eventuallyEq_nhds_of_eventuallyEq_nhdsNE (hg p) hz).symm
  · intro p hp u
    change (if p ∈ S then 0 else _) = 0
    exact if_pos ((hS p).mpr hp)

/-- Normalization does not identify distinct holomorphic directions.
Source: Forster, Lectures on Riemann Surfaces, §18, identity theorem. -/
theorem paired_c3_normalized_holomorphic_injective (h : Module.finrank ℂ E = 1)
    (n : ℕ) (y : Fin n → C)
    (W : Submodule ℂ (TangentBundle 𝓘(ℂ, E) C → ℂ))
    (hW : ∀ q, q ∈ W ↔ b4c_IsMeroForm h q ∧
      (∀ p, (-1 : WithTop ℤ) ≤ meromorphicOrderAt (HurwitzPrymRR_loc h q p) 0) ∧
      (∀ p ∉ Set.range y, AnalyticAt ℂ (HurwitzPrymRR_loc h q p) 0) ∧
      ∀ p ∈ Set.range y, ∀ u, q ⟨p, u⟩ = 0) :
    Function.Injective (pairedC3NormalizedHolomorphicMap h n y W hW) := by
  classical
  intro u v huv
  have he : residual_normalize_poles (Finset.univ.image y) u.val =
      residual_normalize_poles (Finset.univ.image y) v.val := congrArg Subtype.val huv
  apply RiemannRochEichler_holForm_germ_ext h u v
  intro p
  exact (residual_normalize_poles_loc h (Finset.univ.image y) u.val p).symm.trans
    ((Filter.EventuallyEq.of_eq (congrArg (fun q => HurwitzPrymRR_loc h q p) he)).trans
      (residual_normalize_poles_loc h (Finset.univ.image y) v.val p))

#print axioms paired_c3_normalized_holomorphic_injective
#print axioms pairedC3NormalizedHolomorphicMap
end HodgeLean.Foundations.Program.G32Native
