import HodgeLean.Foundations.Program.G32Native.PairedC3FullResidueEvaluation
import HodgeLean.Foundations.Program.G32Native.PairedResidualPoleNormalization
import HodgeLean.Foundations.Program.G32Native.PairedC3FullResidueKernel
import HodgeLean.Foundations.Program.G32Native.PairedC3NormalizedHolomorphic

/-! # Dimension of the full normalized simple-pole space -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open HodgeLean.Adapters HodgeLean.Foundations.Program Filter
open TauCeti.Contour
open scoped Manifold ContDiff Topology BigOperators
namespace HodgeLean.Foundations.Program.G32Native
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
  [T2Space C] [CompactSpace C] [ConnectedSpace C]

/-- The full normalized space with n+1 allowed simple poles has n
residue directions in addition to its holomorphic directions.
Source: Forster, Lectures on Riemann Surfaces, §§18–19;
Schoen, Compositio Mathematica 65 (1988), Lemma 2.3(i). -/
theorem paired_c3_full_pole_space_finrank_aux (h : Module.finrank ℂ E = 1)
    (n : ℕ) (y : Fin (n + 1) → C) (hy : Function.Injective y)
    (W : Submodule ℂ (TangentBundle 𝓘(ℂ, E) C → ℂ)) [Module.Finite ℂ W]
    (hW : ∀ q, q ∈ W ↔ b4c_IsMeroForm h q ∧
      (∀ p, (-1 : WithTop ℤ) ≤ meromorphicOrderAt (HurwitzPrymRR_loc h q p) 0) ∧
      (∀ p ∉ Set.range y, AnalyticAt ℂ (HurwitzPrymRR_loc h q p) 0) ∧
      ∀ p ∈ Set.range y, ∀ u, q ⟨p, u⟩ = 0) :
    Module.finrank ℂ W = Module.finrank ℂ (b3_HolForm E C) + n := by
  classical
  let hm := fun q : W => ((hW q.val).mp q.property).1
  let ev := pairedC3FullResidueEvaluation h n y W hm
  let A := pairedC3NormalizedHolomorphicMap h (n + 1) y W hW
  have hk (v : b3_HolForm E C) : ev (A v) = 0 := by
    funext i
    change residue (HurwitzPrymRR_loc h (A v).val (y i.castSucc)) 0 = 0
    have he : HurwitzPrymRR_loc h (A v).val (y i.castSucc) =ᶠ[𝓝[≠] 0]
        HurwitzPrymRR_loc h v.val (y i.castSucc) :=
      residual_normalize_poles_loc h (Finset.univ.image y) v.val (y i.castSucc)
    exact (residue_congr_nhdsNE he).trans
      (residue_eq_zero_of_analyticAt (RiemannRochEichler_loc_analytic h v _))
  let F := A.codRestrict (LinearMap.ker ev) hk
  have hF : Function.Injective F := by
    intro u v huv
    exact paired_c3_normalized_holomorphic_injective h (n + 1) y W hW
      (congrArg Subtype.val huv)
  have hlo : Module.finrank ℂ (b3_HolForm E C) ≤ Module.finrank ℂ (LinearMap.ker ev) :=
    LinearMap.finrank_le_finrank_of_injective hF
  have hhi : Module.finrank ℂ (LinearMap.ker ev) ≤ Module.finrank ℂ (b3_HolForm E C) :=
    paired_c3_full_residue_kernel_finrank_le h n y W
      (fun q => (hW q.val).mp q.property)
  have hs : Function.Surjective ev := paired_c3_full_residue_evaluation_surjective h n y hy W hW
  have hd := ev.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hs, finrank_top, Module.finrank_fin_fun] at hd
  omega

/-- The dimension formula indexed by a positive number of marked points.
Source: Forster, Lectures on Riemann Surfaces, §§18–19. -/
theorem paired_c3_full_pole_space_finrank (h : Module.finrank ℂ E = 1)
    (m : ℕ) (hm : 0 < m) (y : Fin m → C) (hy : Function.Injective y)
    (W : Submodule ℂ (TangentBundle 𝓘(ℂ, E) C → ℂ)) [Module.Finite ℂ W]
    (hW : ∀ q, q ∈ W ↔ b4c_IsMeroForm h q ∧
      (∀ p, (-1 : WithTop ℤ) ≤ meromorphicOrderAt (HurwitzPrymRR_loc h q p) 0) ∧
      (∀ p ∉ Set.range y, AnalyticAt ℂ (HurwitzPrymRR_loc h q p) 0) ∧
      ∀ p ∈ Set.range y, ∀ u, q ⟨p, u⟩ = 0) :
    Module.finrank ℂ W = Module.finrank ℂ (b3_HolForm E C) + (m - 1) := by
  cases m with
  | zero => omega
  | succ n => exact paired_c3_full_pole_space_finrank_aux h n y hy W hW

#print axioms paired_c3_full_pole_space_finrank
#print axioms paired_c3_full_pole_space_finrank_aux

end HodgeLean.Foundations.Program.G32Native
