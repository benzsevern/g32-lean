import HodgeLean.Foundations.Curves.AbelTheorem.Defs

noncomputable section
open HodgeLean.Foundations.Program
open Set Filter Manifold MeasureTheory
open scoped Topology ContDiff
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C] [T2Space C]
attribute [local instance] b3Forms_isManifold_real

theorem radial_cutoffs_in_neighborhoods (h : Module.finrank ℂ E = 1)
    (s : Set C) (hs : s.Finite) (U : C → Set C) (hU : ∀ x, U x ∈ 𝓝 x)
    (R : C → ℝ) (hR : ∀ x, 0 < R x) :
    ∃ a b : C → ℝ, (∀ x, 0 < a x ∧ a x < b x ∧ b x < R x) ∧
      let χ := fun x => b4c_residue_chartFunction h x
        (fun z => b4c_residue_profile (a x) (b x) ‖z‖)
      (∀ x, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (χ x)) ∧
      (∀ x, HasCompactSupport (χ x)) ∧
      (∀ x, tsupport (χ x) ⊆ U x) ∧
      (∀ x, tsupport (χ x) ⊆ (chartAt E x).source) ∧
      (∀ x, χ x =ᶠ[𝓝 x] fun _ => (1 : ℝ)) ∧
      s.PairwiseDisjoint (fun x => tsupport (χ x)) ∧
      ∀ x z, ‖z‖ ≤ b x → chartAt E x x + b4cov_lineEquiv h z ∈ (chartAt E x).target := by
  classical
  obtain ⟨V, hV, hd⟩ := hs.t2_separation
  have hcut := fun x => b4c_residue_radial_cutoff_at h x
    (inter_mem ((hV x).2.mem_nhds (hV x).1) (hU x)) (hR x)
  choose a b ha hab hbR hsm hc hsub hone hball using hcut
  refine ⟨a, b, fun x => ⟨ha x, hab x, hbR x⟩, hsm, hc,
    fun x => (hsub x).trans (fun _ hx => hx.1.2),
    fun x => (hsub x).trans inter_subset_right, hone, ?_, fun x z hz => (hball x z hz).1⟩
  intro x hx y hy hxy
  exact (hd hx hy hxy).mono ((hsub x).trans (fun _ hz => hz.1.1))
    ((hsub y).trans (fun _ hz => hz.1.1))

end HodgeLean.Foundations.Curves.AbelTheorem
