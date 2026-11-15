import HodgeLean.Foundations.Program.CodifferentialDictionaryProjectionProofs

noncomputable section
open Set Filter Topology Manifold HodgeLean.Papers
open scoped TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local instance] Classical.propDecidable
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.totalChart
  b65z_SharedFamily.totalMan b65z_SharedFamily.fibreChart b65z_SharedFamily.fibreMan
  b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact b65z_SharedFamily.fibreConnected
  b65z_SharedFamily.fibreFaithful

open Metric Matrix

def b66d_shiftD (j : Fin 13) : ((Fin 10 → ℂ) × ℂ) →L[ℂ] ℂ :=
  if h : j.val < 10 then
    (ContinuousLinearMap.proj ⟨j.val, h⟩).comp
      (ContinuousLinearMap.fst ℂ (Fin 10 → ℂ) ℂ) else 0

theorem b66d_shift_hasFDerivAt (j : Fin 13) (u : (Fin 10 → ℂ) × ℂ) :
    HasFDerivAt (fun v : (Fin 10 → ℂ) × ℂ => b6a_valueShift v.1 j)
      (b66d_shiftD j) u := by
  unfold b6a_valueShift b66d_shiftD
  split_ifs
  · exact ((ContinuousLinearMap.proj _).comp
      (ContinuousLinearMap.fst ℂ (Fin 10 → ℂ) ℂ)).hasFDerivAt
  · exact hasFDerivAt_const 1 u
  · exact hasFDerivAt_const 0 u

theorem b66d_projectionCoeff_free_hasFDerivAt
    {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (a : b66f_Index D)
    (hfree : D.atlas.f a.2 ∉ Set.range (b6_branch c))
    (u : (Fin 10 → ℂ) × ℂ) (hu : u ∈ (D.atlas.A a).target) :
    HasFDerivAt (b66d_projectionCoeff D a)
      (ContinuousLinearMap.snd ℂ (Fin 10 → ℂ) ℂ) u := by
  apply hasFDerivAt_snd.congr_of_eventuallyEq
  filter_upwards [(D.atlas.A a).open_target.mem_nhds hu] with v hv
  exact b66d_projectionCoeff_free D a hfree v hv

set_option backward.isDefEq.respectTransparency false in
theorem b66d_projectionCoeff_finite_hasFDerivAt
    {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (a : b66f_Index D) (j : Fin 13)
    (heq : D.atlas.f a.2 = b6_branch c j) (hj : j.val ≠ 12)
    (u : (Fin 10 → ℂ) × ℂ) (hu : u ∈ (D.atlas.A a).target) :
    HasFDerivAt (b66d_projectionCoeff D a)
      (b66d_shiftD j + ((D.atlas.n a.2 : ℂ) * u.2 ^ (D.atlas.n a.2 - 1)) •
        ContinuousLinearMap.snd ℂ (Fin 10 → ℂ) ℂ) u := by
  have h := (b66d_shift_hasFDerivAt j u).add
    ((hasFDerivAt_snd (p := u) (𝕜 := ℂ)).pow (D.atlas.n a.2))
  have he : b66d_projectionCoeff D a =ᶠ[𝓝 u]
      (fun v : (Fin 10 → ℂ) × ℂ => b6a_valueShift v.1 j + v.2 ^ D.atlas.n a.2) := by
    filter_upwards [(D.atlas.A a).open_target.mem_nhds hu] with v hv
    exact b66d_projectionCoeff_finite D a j heq hj v hv
  simpa only [nsmul_eq_mul] using h.congr_of_eventuallyEq he

set_option backward.isDefEq.respectTransparency false in
theorem b66d_projectionCoeff_infinite_hasFDerivAt
    {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (a : b66f_Index D) (j : Fin 13)
    (heq : D.atlas.f a.2 = b6_branch c j) (hj : j.val = 12)
    (u : (Fin 10 → ℂ) × ℂ) (hu : u ∈ (D.atlas.A a).target) (hz : u.2 ≠ 0) :
    HasFDerivAt (b66d_projectionCoeff D a)
      ((-((u.2 ^ D.atlas.n a.2) ^ 2)⁻¹ *
        ((D.atlas.n a.2 : ℂ) * u.2 ^ (D.atlas.n a.2 - 1))) •
          ContinuousLinearMap.snd ℂ (Fin 10 → ℂ) ℂ) u := by
  have h := (hasFDerivAt_inv (pow_ne_zero (D.atlas.n a.2) hz)).comp u
    ((hasFDerivAt_snd (p := u) (𝕜 := ℂ)).pow (D.atlas.n a.2))
  have he : b66d_projectionCoeff D a =ᶠ[𝓝 u]
      (fun v : (Fin 10 → ℂ) × ℂ => (v.2 ^ D.atlas.n a.2)⁻¹) := by
    have hnz : ∀ᶠ v : (Fin 10 → ℂ) × ℂ in 𝓝 u, v.2 ≠ 0 :=
      (isOpen_ne_fun continuous_snd continuous_const).mem_nhds hz
    filter_upwards [(D.atlas.A a).open_target.mem_nhds hu, hnz] with v hv hvz
    exact b66d_projectionCoeff_infinite D a j heq hj v hv hvz
  apply (h.congr_of_eventuallyEq he).congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.toSpanSingleton_apply,
    nsmul_eq_mul, smul_eq_mul]
  ring

end HodgeLean.Foundations.Program
