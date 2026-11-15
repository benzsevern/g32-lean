import HodgeLean.Foundations.Program.CoverDictionaryDescend
import HodgeLean.Foundations.Program.CoverDictionaryUnique

/-! Reconstruction of forms from descended coefficient vectors. -/

noncomputable section
open Set Metric Filter Matrix Manifold
open scoped Topology ContDiff
open HodgeLean.Papers
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.totalChart
  b65z_SharedFamily.totalMan b65z_SharedFamily.fibreChart b65z_SharedFamily.fibreMan
  b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact b65z_SharedFamily.fibreConnected
  b65z_SharedFamily.fibreFaithful

/-- Evaluation of a linear map in the coordinate basis. -/
theorem caf_linearMap_coordinates {U : Type*}
    (φ : (Fin 4 → ℂ) →ₗ[ℂ] (U → ℂ)) (v : Fin 4 → ℂ) (u : U) :
    φ v u = ∑ i, v i * φ (Pi.single i 1) u := by
  have hv : v = ∑ i : Fin 4, v i • Pi.single i (1 : ℂ) := by
    ext j
    simp [Pi.single_apply, Finset.sum_apply]
  conv_lhs => rw [hv]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- Matrix cancellation recovers the vector of form coefficients. -/
theorem caf_reconstruct_coefficients (N : Matrix (Fin 4) (Fin 4) ℂ)
    (hN : IsUnit N.det) (w r : Fin 4 → ℂ) (ds : ℂ) (hds : ds ≠ 0)
    (hr : N *ᵥ (fun i ↦ w i / ds) = r) :
    ∀ i, w i = (N⁻¹ *ᵥ r) i * ds := by
  rw [← hr, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hN, Matrix.one_mulVec]
  intro i
  exact (div_mul_cancel₀ (w i) hds).symm

/-- Coefficients at the unit tangent vector determine a linear family of holomorphic forms. -/
theorem caf_reconstruct_forms {M : Type} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ, ℂ) ω M]
    (φ : (Fin 4 → ℂ) →ₗ[ℂ] (TangentBundle 𝓘(ℂ, ℂ) M → ℂ))
    (hφ : ∀ v, φ v ∈ b3_HolForm ℂ M)
    (N : Matrix (Fin 4) (Fin 4) ℂ) (hN : IsUnit N.det)
    (x : M) (r : Fin 4 → ℂ) (ds : ℂ) (hds : ds ≠ 0)
    (hr : N *ᵥ (fun i ↦ φ (Pi.single i 1) ⟨x, (1 : ℂ)⟩ / ds) = r)
    (v : Fin 4 → ℂ) (ξ : ℂ) :
    φ v ⟨x, ξ⟩ = (v ⬝ᵥ (N⁻¹ *ᵥ r)) * (ξ * ds) := by
  rw [caf_linearMap_coordinates]
  simp_rw [caf_holForm_apply_smul _ (hφ _) x ξ,
    caf_reconstruct_coefficients N hN _ r ds hds hr]
  simp only [dotProduct, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

section Uniqueness
variable {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group} (D : b65z_SharedFamily c g)
  (t : b6t_polydisc c) {a b : ℂ} (hab : a * b ≠ 0) (hba : b - a ≠ 0)
  (poles : Fin 4 ⊕ Fin 12 → ℂ)

include hab hba

/-- Holomorphic forms agreeing on the regular locus agree everywhere. -/
theorem b65g_holForm_eq_of_good
    (ω₁ ω₂ : TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre c D.C t) → ℂ)
    (h₁ : ω₁ ∈ b3_HolForm ℂ (b65z_fibre c D.C t))
    (h₂ : ω₂ ∈ b3_HolForm ℂ (b65z_fibre c D.C t))
    (he : ∀ u, u.1 ∈ b65g_good D t a b poles → ω₁ u = ω₂ u) : ω₁ = ω₂ := by
  funext u
  obtain ⟨x, ξ⟩ := u
  change ℂ at ξ
  have hcoeff : ω₁ ⟨x, (1 : ℂ)⟩ = ω₂ ⟨x, (1 : ℂ)⟩ := by
    set z₀ := extChartAt 𝓘(ℂ, ℂ) x x
    set v : ℂ := mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x).symm z₀ (1 : ℂ)
    have hlim₁ := (caf_holForm_chart_analytic ω₁ h₁ x z₀
      (mem_extChartAt_target x)).continuousAt.tendsto.mono_left (show 𝓝[≠] z₀ ≤ 𝓝 z₀ from nhdsWithin_le_nhds)
    have hlim₂ := (caf_holForm_chart_analytic ω₂ h₂ x z₀
      (mem_extChartAt_target x)).continuousAt.tendsto.mono_left (show 𝓝[≠] z₀ ≤ 𝓝 z₀ from nhdsWithin_le_nhds)
    have he' : (fun z ↦ ω₁ ⟨(extChartAt 𝓘(ℂ, ℂ) x).symm z,
        mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x).symm z (1 : ℂ)⟩) =ᶠ[𝓝[≠] z₀]
        (fun z ↦ ω₂ ⟨(extChartAt 𝓘(ℂ, ℂ) x).symm z,
        mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x).symm z (1 : ℂ)⟩) := by
      filter_upwards [b65g_chart_punctured_good D t hab hba poles x] with z hz
      exact he _ hz.2
    have he₀ := tendsto_nhds_unique hlim₁ (hlim₂.congr' he'.symm)
    change ω₁ ⟨_, v⟩ = ω₂ ⟨_, v⟩ at he₀
    rw [extChartAt_to_inv] at he₀
    have hlin₁ := caf_holForm_apply_smul ω₁ h₁ x (v : ℂ)
    have hlin₂ := caf_holForm_apply_smul ω₂ h₂ x (v : ℂ)
    have he₀ := hlin₁.symm.trans (he₀.trans hlin₂)
    exact mul_left_cancel₀ (M₀ := ℂ) (a := v) (caf_chart_vector_ne x z₀ (mem_extChartAt_target x)) he₀
  exact (caf_holForm_apply_smul ω₁ h₁ x (ξ : ℂ)).trans
    ((congrArg (fun z : ℂ ↦ (ξ : ℂ) * z) hcoeff).trans
      (caf_holForm_apply_smul ω₂ h₂ x (ξ : ℂ)).symm)

/-- A holomorphic linear family representing a fixed r-vector is unique. -/
theorem b65g_rRepresents_unique (Y : b65z_fibre c D.C t → Matrix (Fin 4) (Fin 4) ℂ)
    (r : Fin 4 → RatFunc ℂ)
    (φ ψ : (Fin 4 → ℂ) →ₗ[ℂ] (TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre c D.C t) → ℂ))
    (hφ : ∀ v, φ v ∈ b3_HolForm ℂ (b65z_fibre c D.C t))
    (hψ : ∀ v, ψ v ∈ b3_HolForm ℂ (b65z_fibre c D.C t))
    (hrφ : b65g_rRepresents D t a b poles Y r φ)
    (hrψ : b65g_rRepresents D t a b poles Y r ψ) : φ = ψ := by
  apply LinearMap.ext
  intro v
  exact b65g_holForm_eq_of_good D t hab hba poles _ _ (hφ v) (hψ v)
    (fun u hu ↦ (hrφ v u hu).trans (hrψ v u hu).symm)

/-- A holomorphic linear family representing a fixed q-vector is unique. -/
theorem b65g_qRepresents_unique (Y : b65z_fibre c D.C t → Matrix (Fin 4) (Fin 4) ℂ)
    (q : Fin 4 → RatFunc ℂ)
    (φ ψ : (Fin 4 → ℂ) →ₗ[ℂ] (TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre c D.C t) → ℂ))
    (hφ : ∀ v, φ v ∈ b3_HolForm ℂ (b65z_fibre c D.C t))
    (hψ : ∀ v, ψ v ∈ b3_HolForm ℂ (b65z_fibre c D.C t))
    (hqφ : b65g_qRepresents D t a b poles Y q φ)
    (hqψ : b65g_qRepresents D t a b poles Y q ψ) : φ = ψ := by
  apply LinearMap.ext
  intro v
  exact b65g_holForm_eq_of_good D t hab hba poles _ _ (hφ v) (hψ v)
    (fun u hu ↦ (hqφ v u hu).trans (hqψ v u hu).symm)

end Uniqueness

section Fibre
variable {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group} (D : b65z_SharedFamily c g)
  (t : b6t_polydisc c) (a b : ℂ) (poles : Fin 4 ⊕ Fin 12 → ℂ)
  (Y : b65z_fibre c D.C t → Matrix (Fin 4) (Fin 4) ℂ)
  (φ : (Fin 4 → ℂ) →ₗ[ℂ] (TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre c D.C t) → ℂ))
  (hφ : ∀ v, φ v ∈ b3_HolForm ℂ (b65z_fibre c D.C t))
  (hY : ∀ x ∈ b65g_good D t a b poles, IsUnit (Y x).det)
  (hds : ∀ x ∈ b65g_good D t a b poles, b65g_ds D t a b ⟨x, (1 : ℂ)⟩ ≠ 0)

include hφ hY hds

/-- Descent with matrix `Y` reconstructs the r-representation. -/
theorem b65g_rRepresents_of_descended (r : Fin 4 → RatFunc ℂ)
    (hr : ∀ x ∈ b65g_good D t a b poles,
      Y x *ᵥ (fun i ↦ φ (Pi.single i 1) ⟨x, (1 : ℂ)⟩ /
        b65g_ds D t a b ⟨x, (1 : ℂ)⟩) =
        fun j ↦ b65q_eval (r j) (b65g_sFun D t a b x)) :
    b65g_rRepresents D t a b poles Y r φ := by
  intro v u hu
  obtain ⟨x, ξ⟩ := u
  have hf := caf_reconstruct_forms φ hφ (Y x) (hY x hu) x _ _ (hds x hu) (hr x hu) v ξ
  change φ v ⟨x, ξ⟩ = _
  change φ v ⟨x, ξ⟩ = _ * b65g_ds D t a b ⟨x, ξ⟩
  rw [b65g_ds_smul D t (a := a) (b := b) x ξ]
  exact hf

/-- Descent with matrix `Y⁻ᵀ` reconstructs the q-representation. -/
theorem b65g_qRepresents_of_descended (q : Fin 4 → RatFunc ℂ)
    (hq : ∀ x ∈ b65g_good D t a b poles,
      (Y x)⁻¹ᵀ *ᵥ (fun i ↦ φ (Pi.single i 1) ⟨x, (1 : ℂ)⟩ /
        b65g_ds D t a b ⟨x, (1 : ℂ)⟩) =
        fun j ↦ b65q_eval (q j) (b65g_sFun D t a b x)) :
    b65g_qRepresents D t a b poles Y q φ := by
  intro v u hu
  obtain ⟨x, ξ⟩ := u
  have hN : IsUnit ((Y x)⁻¹ᵀ).det := by
    rw [Matrix.det_transpose, Matrix.det_nonsing_inv]
    exact (hY x hu).ringInverse
  have hf := caf_reconstruct_forms φ hφ ((Y x)⁻¹ᵀ) hN x _ _ (hds x hu) (hq x hu) v ξ
  rw [← Matrix.transpose_nonsing_inv, Matrix.nonsing_inv_nonsing_inv _ (hY x hu)] at hf
  change φ v ⟨x, ξ⟩ = _
  change φ v ⟨x, ξ⟩ = _ * b65g_ds D t a b ⟨x, ξ⟩
  rw [b65g_ds_smul D t (a := a) (b := b) x ξ]
  exact hf

end Fibre
end HodgeLean.Foundations.Program
