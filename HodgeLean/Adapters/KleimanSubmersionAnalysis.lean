import HodgeLean.Adapters.KleimanProductChartClass
import Mathlib.Analysis.Calculus.Implicit

/-! # Analytic tools for the transverse-submersion lemma

A function vanishing on the level set of a submersion has derivative vanishing on the kernel of
the submersion's derivative. A linear map whose kernel is small enough is surjective. Holomorphic
maps on an open of a complex manifold are strictly differentiable in charts, and surjectivity of
the chart derivative gives surjectivity of the manifold derivative.
-/

noncomputable section
set_option maxHeartbeats 400000
open Filter Topology
open scoped ContDiff Manifold

namespace HodgeLean.Adapters

/-- A function vanishing on the level set through `w₀` of a strictly differentiable map with
surjective derivative has derivative at `w₀` vanishing on the kernel of that derivative.
Source: Mathlib `HasStrictFDerivAt.to_implicitFunction`, the implicit function theorem. -/
theorem hc9k_fderiv_eq_zero_of_mem_ker {E F G : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [FiniteDimensional ℂ F] [NormedAddCommGroup G] [NormedSpace ℂ G]
    (P : E → F) (P' : E →L[ℂ] F) (w₀ : E) (hP : HasStrictFDerivAt P P' w₀)
    (hP' : P'.range = ⊤) (A : E → G) (hA : DifferentiableAt ℂ A w₀)
    (hvan : ∀ᶠ w in 𝓝 w₀, P w = P w₀ → A w = 0) (ξ : E) (hξ : P' ξ = 0) :
    fderiv ℂ A w₀ ξ = 0 := by
  let γ := hP.implicitFunction P P' hP' (P w₀)
  have hγ : HasStrictFDerivAt γ P'.ker.subtypeL 0 := hP.to_implicitFunction hP'
  have hγ0 : γ 0 = w₀ := hP.implicitFunction_apply_image hP'
  have hmap : ∀ᶠ k in 𝓝 (0 : P'.ker), P (γ k) = P w₀ := by
    have hT : Tendsto (fun k : P'.ker => (P w₀, k)) (𝓝 0) (𝓝 (P w₀, 0)) :=
      tendsto_const_nhds.prodMk_nhds tendsto_id
    exact hT.eventually (hP.map_implicitFunction_eq hP')
  have htend : Tendsto γ (𝓝 0) (𝓝 w₀) := by
    have := hγ.hasFDerivAt.continuousAt.tendsto
    rwa [hγ0] at this
  have hzero : (fun k => A (γ k)) =ᶠ[𝓝 0] fun _ => 0 := by
    filter_upwards [htend.eventually hvan, hmap] with k h1 h2
    exact h1 h2
  have hA' : HasFDerivAt A (fderiv ℂ A w₀) (γ 0) := by
    rw [hγ0]
    exact hA.hasFDerivAt
  have hcomp := hA'.comp (0 : P'.ker) hγ.hasFDerivAt
  have h0 := (hasFDerivAt_const (𝕜 := ℂ) (0 : G) (0 : P'.ker)).congr_of_eventuallyEq
    hzero
  have := congrArg (fun L => L ⟨ξ, hξ⟩) (hcomp.unique h0)
  simpa using this

/-- A linear map between finite-dimensional spaces whose kernel has dimension at most the
source dimension minus the target dimension is surjective.
Source: rank--nullity, Mathlib `LinearMap.finrank_range_add_finrank_ker`. -/
theorem hc9k_surjective_of_finrank_ker {E F : Type*} [AddCommGroup E] [Module ℂ E]
    [FiniteDimensional ℂ E] [AddCommGroup F] [Module ℂ F] [FiniteDimensional ℂ F]
    (L : E →ₗ[ℂ] F)
    (h : Module.finrank ℂ (LinearMap.ker L) + Module.finrank ℂ F ≤ Module.finrank ℂ E) :
    Function.Surjective L := by
  rw [← LinearMap.range_eq_top]
  apply Submodule.eq_top_of_finrank_eq
  have h1 := LinearMap.finrank_range_add_finrank_ker L
  have h2 := Submodule.finrank_le (LinearMap.range L)
  omega

/-- A subspace meeting the kernel of a linear map to `ℂ^n` only in zero has dimension at most
`n`. -/
theorem hc9k_finrank_le_of_inf_ker {E : Type*} [AddCommGroup E] [Module ℂ E]
    [FiniteDimensional ℂ E] {n : ℕ} (K : Submodule ℂ E) (u : E →ₗ[ℂ] (Fin n → ℂ))
    (h : ∀ ξ ∈ K, u ξ = 0 → ξ = 0) : Module.finrank ℂ K ≤ n := by
  have hinj : Function.Injective (u.comp K.subtype) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro ξ hξ
    exact Subtype.ext (h ξ.1 ξ.2 hξ)
  simpa using LinearMap.finrank_le_finrank_of_injective hinj

/-- An injective linear map from `ℂ^n` into the kernel of a surjective linear map to `ℂ^c` gives
`n + c ≤ d`. -/
theorem hc9k_add_le_of_injective_into_ker {n c d : ℕ}
    (ψ : (Fin n → ℂ) →ₗ[ℂ] (Fin d → ℂ))
    (G : (Fin d → ℂ) →ₗ[ℂ] (Fin c → ℂ)) (hψ : Function.Injective ψ)
    (hG : Function.Surjective G) (hGψ : G.comp ψ = 0) : n + c ≤ d := by
  have h1 := LinearMap.finrank_range_add_finrank_ker G
  rw [LinearMap.range_eq_top.mpr hG, finrank_top] at h1
  simp only [Module.finrank_fin_fun] at h1
  have hle : LinearMap.range ψ ≤ LinearMap.ker G := by
    rintro _ ⟨v, rfl⟩
    exact congrArg (fun L => L v) hGψ
  have h2 := Submodule.finrank_mono hle
  rw [LinearMap.finrank_range_of_inj hψ] at h2
  simp only [Module.finrank_fin_fun] at h2
  omega

/-- A holomorphic map on an open of a complex manifold, read in the chart at a point, is
strictly differentiable there with the chart derivative. -/
theorem hc9k_chart_rep_hasStrictFDerivAt {d c : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (Fin d → ℂ) M] [IsManifold 𝓘(ℂ, Fin d → ℂ) ω M]
    (U : TopologicalSpace.Opens M) (f : C(U, Fin c → ℂ))
    (hhol : ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin c → ℂ) ω f) (u : U) :
    HasStrictFDerivAt (fun w => f ((chartAt (Fin d → ℂ) u).symm w))
      (fderiv ℂ (fun w => f ((chartAt (Fin d → ℂ) u).symm w)) (chartAt (Fin d → ℂ) u u))
      (chartAt (Fin d → ℂ) u u) := by
  have h := (contMDiffAt_iff.mp (hhol u)).2
  simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
    Function.id_comp, modelWithCornersSelf_coe, Set.range_id, contDiffWithinAt_univ,
    extChartAt_coe_symm, extChartAt_coe, modelWithCornersSelf_coe_symm, Function.comp_id] at h
  exact h.hasStrictFDerivAt (by simp)

/-- A map on an open of a complex manifold whose chart representative at a point has surjective
derivative has surjective manifold derivative there. -/
theorem hc9k_mfderiv_surjective_of_chart_rep {d c : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (Fin d → ℂ) M] [IsManifold 𝓘(ℂ, Fin d → ℂ) ω M]
    (U : TopologicalSpace.Opens M) (f : C(U, Fin c → ℂ))
    (hhol : ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin c → ℂ) ω f) (u : U)
    (hs : Function.Surjective (fderiv ℂ (fun w => f ((chartAt (Fin d → ℂ) u).symm w))
      (chartAt (Fin d → ℂ) u u))) :
    Function.Surjective (mfderiv 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin c → ℂ) f u) := by
  have hm : MDifferentiableAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin c → ℂ) f u :=
    (hhol u).mdifferentiableAt (by simp)
  rw [hm.mfderiv]
  simp only [writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
    Function.id_comp, modelWithCornersSelf_coe, Set.range_id, fderivWithin_univ,
    extChartAt_coe_symm, extChartAt_coe, modelWithCornersSelf_coe_symm, Function.comp_id]
  exact hs

end HodgeLean.Adapters
