import HodgeLean.Foundations.Program.CodifferentialDictionaryContractionProofs

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

theorem b66d_averaged_product_evaluation {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c) (cj : Bool)
    (φ : b65g_homG D t cj) (ψ : b65g_homG D t (!cj))
    (q r : b66f_primitiveForms D t)
    (hq : b66f_chartForm D t q.val = φ.val (Pi.single 0 1))
    (hr : b66f_chartForm D t r.val = ψ.val (Pi.single 0 1))
    (a : b66f_Index D) (p : b65z_fibre c D.C t)
    (ha : p.val ∈ (D.atlas.A a).source) (v : ℂ) :
    b66f_multiply D t q r a p.val.2 * (b66f_gen_b66g_sliceD D t a p v) ^ 2 =
      (1 / 4 : ℂ) * b65g_contract φ.val ψ.val ⟨p, v⟩ := by
  let u : TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre c D.C t) := ⟨p, v⟩
  let d := b66f_gen_b66g_sliceD D t a p v
  let A : (Fin 4 → ℂ) →ₗ[ℂ] ℂ := (LinearMap.proj u).comp φ.val
  let B : (Fin 4 → ℂ) →ₗ[ℂ] ℂ := (LinearMap.proj u).comp ψ.val
  have hformq : b66f_gen_b66g_toForm D t q.val = φ.val (Pi.single 0 1) :=
    (b66d_chartForm_toForm D t q.val).trans hq
  have hformr : b66f_gen_b66g_toForm D t r.val = ψ.val (Pi.single 0 1) :=
    (b66d_chartForm_toForm D t r.val).trans hr
  have hqpull (h : b4b_Group) : b66f_pull D t 1 h q.val a p.val.2 * d =
      A (b65g_rep cj h⁻¹ (Pi.single 0 1)) := by
    change b66f_pull D t 1 h q.val a p.val.2 * b66f_gen_b66g_sliceD D t a p v = _
    rw [← b66f_gen_b66g_pullback_apply D t q.val h a p ha v, hformq]
    simpa only [A, B, u, LinearMap.comp_apply, LinearMap.proj_apply, b4_formAct, inv_inv] using
      (congrFun (φ.property.2 h⁻¹ (Pi.single 0 1)) u).symm
  have hrpull (h : b4b_Group) : b66f_pull D t 1 h r.val a p.val.2 * d =
      B (b65g_rep (!cj) h⁻¹ (Pi.single 0 1)) := by
    change b66f_pull D t 1 h r.val a p.val.2 * b66f_gen_b66g_sliceD D t a p v = _
    rw [← b66f_gen_b66g_pullback_apply D t r.val h a p ha v, hformr]
    simpa only [A, B, u, LinearMap.comp_apply, LinearMap.proj_apply, b4_formAct, inv_inv] using
      (congrFun (ψ.property.2 h⁻¹ (Pi.single 0 1)) u).symm
  have hsum : (∑ h : b4b_Group,
      (b66f_pull D t 1 h q.val a p.val.2 * b66f_pull D t 1 h r.val a p.val.2) * d ^ 2) =
      ∑ h : b4b_Group, A (b65g_rep cj h⁻¹ (Pi.single 0 1)) *
        B (b65g_rep (!cj) h⁻¹ (Pi.single 0 1)) := by
    apply Finset.sum_congr rfl
    intro h hh
    rw [← hqpull h, ← hrpull h]
    ring
  change b66f_average D t (b66f_product D q.val r.val) a p.val.2 * d ^ 2 = _
  rw [b66f_gen_b66g_average_apply]
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul,
    b66f_gen_b66g_pull_product, b66f_product]
  rw [mul_assoc, Finset.sum_mul, hsum]
  have hreindex := Equiv.sum_comp (Equiv.inv b4b_Group)
    (fun h => A (b65g_rep cj h (Pi.single 0 1)) * B (b65g_rep (!cj) h (Pi.single 0 1)))
  simp only [Equiv.inv_apply] at hreindex
  rw [hreindex, b66d_bilinear_average]
  change (Fintype.card b4b_Group : ℂ)⁻¹ * ((38880 : ℂ) *
    ∑ i : Fin 4, A (Pi.single i 1) * B (Pi.single i 1)) =
      (1 / 4 : ℂ) * ∑ i : Fin 4, A (Pi.single i 1) * B (Pi.single i 1)
  norm_num [b63l_card_group, ← mul_assoc]

end HodgeLean.Foundations.Program
