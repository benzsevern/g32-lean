import HodgeLean.Foundations.Program.SchoenCycleCanonicalDivisors
import Mathlib.Algebra.DualNumber

/-! # Local first-order variations of a canonical divisor -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Manifold Filter Topology
open scoped ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

/-- Local analytic divisibility makes a differential variation scalar, so its
class modulo the original differential vanishes. Multiplicities are retained.
Source: ACGH, Geometry of Algebraic Curves I, Chapter IV, Abel-map fibres;
Forster, Lectures on Riemann Surfaces, §13, holomorphic functions on compact surfaces. -/
theorem s2e_u1_locally_divisible_variation
    {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) (θ δ : b3_HolForm E C) (hθ : θ ≠ 0)
    (hlocal : ∀ p : C, ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧
      HurwitzPrymRR_loc hE δ p =ᶠ[𝓝[≠] 0]
        (fun z => g z * HurwitzPrymRR_loc hE θ p z)) :
    (∃ c : ℂ, δ = c • θ) ∧
      Submodule.Quotient.mk (p := Submodule.span ℂ {θ}) δ = 0 := by
  suffices hs : ∃ c : ℂ, δ = c • θ by
    refine ⟨hs, (Submodule.Quotient.mk_eq_zero _).mpr ?_⟩
    obtain ⟨c, rfl⟩ := hs
    exact Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_singleton θ))
  by_cases hδ : δ = 0
  · exact ⟨0, by rw [hδ, zero_smul]⟩
  let v : b4c_MeroForm E C hE := ⟨δ, RiemannRochAna_hol_isMeroForm hE δ⟩
  let w : b4c_MeroForm E C hE := ⟨θ, RiemannRochAna_hol_isMeroForm hE θ⟩
  have hv : (v : TangentBundle 𝓘(ℂ, E) C → ℂ) ≠ 0 := fun hz => hδ (Subtype.ext hz)
  have hw : (w : TangentBundle 𝓘(ℂ, E) C → ℂ) ≠ 0 := fun hz => hθ (Subtype.ext hz)
  let p : C := Classical.choice inferInstance
  have hgv : ∃ p, meromorphicOrderAt (HurwitzPrymRR_loc hE v p) 0 ≠ ⊤ :=
    ⟨p, RiemannRochAna_hol_order_ne_top hE δ hδ p⟩
  have hgw : ∃ p, meromorphicOrderAt (HurwitzPrymRR_loc hE w p) 0 ≠ ⊤ :=
    ⟨p, RiemannRochAna_hol_order_ne_top hE θ hθ p⟩
  have hnonneg (x : C) : 0 ≤ meromorphicOrderAt
      (fun z => HurwitzPrymRR_loc hE v x z / HurwitzPrymRR_loc hE w x z) 0 := by
    obtain ⟨g, hg, he⟩ := hlocal x
    have hn := (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (w.property.2 x)).mp
      (b4c_meroForm_order_ne_top hE w hgw x)
    have hquot : (fun z => HurwitzPrymRR_loc hE v x z /
        HurwitzPrymRR_loc hE w x z) =ᶠ[𝓝[≠] 0] g := by
      filter_upwards [he, hn] with z hz hnz
      exact (div_eq_iff hnz).mpr hz
    rw [meromorphicOrderAt_congr hquot]
    exact hg.meromorphicOrderAt_nonneg
  let F : b4c_MeroFun E C := ⟨b4c_formRatio (hE := hE) v w,
    b4c_formRatio_isMeroFun_aux hE v w hv hw hgv hgw⟩
  have hfinite (x : C) : F x ≠ OnePoint.infty := by
    change b4c_formRatio (hE := hE) v w x ≠ OnePoint.infty
    have hn := not_lt_of_ge (hnonneg x)
    simp only [b4c_formRatio, hn, ite_false]
    split_ifs <;> exact OnePoint.coe_ne_infty _
  have hconstant (x y : C) : F x = F y := by
    by_contra hxy
    obtain ⟨z, hz⟩ := b4cov_surjective (by simp : Module.finrank ℂ ℂ = 1)
      F F.property.1 ⟨x, y, hxy⟩ OnePoint.infty
    exact hfinite z hz
  obtain ⟨c, hc⟩ := OnePoint.ne_infty_iff_exists.mp (hfinite p)
  have hratio (x : C) : b4c_formRatio (hE := hE) v w x = (c : OnePoint ℂ) :=
    (hconstant x p).trans hc.symm
  refine ⟨c, ?_⟩
  apply RiemannRochEichler_holForm_germ_ext hE
  intro x
  exact s2e_constant_formRatio_germ hE v w hgv hgw c hratio x

/-- Equality with a local dual-number multiple forces the projective variation
class to vanish, including at multiple zeros.
Source: ACGH, Geometry of Algebraic Curves I, Chapter IV, differential of the Abel map. -/
theorem s2e_u1_infinitesimal_zero_divisor
    {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) (θ δ : b3_HolForm E C) (hθ : θ ≠ 0)
    (hlocal : ∀ p : C, ∃ u : ℂ → DualNumber ℂ,
      AnalyticAt ℂ (fun z => (u z).snd) 0 ∧
      ∀ᶠ z in 𝓝[≠] 0,
        (⟨HurwitzPrymRR_loc hE θ p z, HurwitzPrymRR_loc hE δ p z⟩ : DualNumber ℂ) =
          u z * TrivSqZeroExt.inl (M := ℂ) (HurwitzPrymRR_loc hE θ p z)) :
    (∀ p : C, ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧
      (fun z => HurwitzPrymRR_loc hE δ p z / HurwitzPrymRR_loc hE θ p z)
        =ᶠ[𝓝[≠] 0] g) ∧
    (∃ c : ℂ, δ = c • θ) ∧
      Submodule.Quotient.mk (p := Submodule.span ℂ {θ}) δ = 0 := by
  have hdiv (p : C) : ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧
      HurwitzPrymRR_loc hE δ p =ᶠ[𝓝[≠] 0]
        (fun z => g z * HurwitzPrymRR_loc hE θ p z) := by
    obtain ⟨u, hu, he⟩ := hlocal p
    refine ⟨fun z => (u z).snd, hu, ?_⟩
    filter_upwards [he] with z hz
    simpa only [DualNumber.snd_mul, TrivSqZeroExt.snd_mk, TrivSqZeroExt.fst_mk,
      TrivSqZeroExt.snd_inl, TrivSqZeroExt.fst_inl, mul_zero, zero_add] using congrArg TrivSqZeroExt.snd hz
  refine ⟨?_, s2e_u1_locally_divisible_variation hE θ δ hθ hdiv⟩
  intro p
  obtain ⟨g, hg, he⟩ := hdiv p
  refine ⟨g, hg, ?_⟩
  have hn := (meromorphicOrderAt_ne_top_iff_eventually_ne_zero
    (RiemannRochEichler_loc_analytic hE θ p).meromorphicAt).mp
    (RiemannRochAna_hol_order_ne_top hE θ hθ p)
  filter_upwards [he, hn] with z hz hnz
  exact (div_eq_iff hnz).mpr hz

end HodgeLean.Foundations.Program
