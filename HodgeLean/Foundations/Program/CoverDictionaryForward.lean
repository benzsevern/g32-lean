import HodgeLean.Foundations.Program.CoverDictionaryInverse
import HodgeLean.Foundations.Program.CoverDictionaryLinearExtend

/-! Equivariant holomorphic extensions of the rational formulas. -/

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

set_option maxHeartbeats 200000 in
/-- A matrix formula with the contragredient deck law defines an equivariant holomorphic family. -/
theorem b65g_homG_of_matrix_formula {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c) {a b : ℂ}
    (hab : a * b ≠ 0) (hba : b - a ≠ 0) (poles : Fin 4 ⊕ Fin 12 → ℂ) (conj : Bool)
    (φ : (Fin 4 → ℂ) →ₗ[ℂ] (TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre c D.C t) → ℂ))
    (hφ : ∀ v, φ v ∈ b3_HolForm ℂ (b65z_fibre c D.C t))
    (M : b65z_fibre c D.C t → Matrix (Fin 4) (Fin 4) ℂ)
    (R : b65z_fibre c D.C t → Fin 4 → ℂ)
    (hM : ∀ x ∈ b65g_good D t a b poles, ∀ h : b4b_Group,
      M (h • x) = (b65g_mat conj h⁻¹)ᵀ * M x)
    (hR : ∀ x ∈ b65g_good D t a b poles, ∀ h : b4b_Group, R (h • x) = R x)
    (he : ∀ (v : Fin 4 → ℂ) (u : TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre c D.C t)), u.1 ∈ b65g_good D t a b poles →
      φ v u = (v ⬝ᵥ (M u.1 *ᵥ R u.1)) * b65g_ds D t a b u) :
    φ ∈ b65g_homG D t conj := by
  refine ⟨hφ, fun h v ↦ ?_⟩
  have hact : b4_formAct ℂ h (φ v) ∈ b3_HolForm ℂ (b65z_fibre c D.C t) :=
    b3_pullback_mem_holForm (E := ℂ) (E' := ℂ)
      (fun y : b65z_fibre c D.C t ↦ h⁻¹ • y) (D.hG t h⁻¹) (φ v) (hφ v)
  apply b65g_holForm_eq_of_good D t hab hba poles _ _ (hφ _) hact
  intro u hu
  obtain ⟨x, ξ⟩ := u
  change φ (b65g_rep conj h v) ⟨x, ξ⟩ =
    φ v ⟨h⁻¹ • x, mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
      (fun y : b65z_fibre c D.C t ↦ h⁻¹ • y) x ξ⟩
  have hhx := (b65g_goodSub D t a b poles).smul_mem h⁻¹ hu
  rw [he (b65g_rep conj h v) ⟨x, ξ⟩ hu,
    he v ⟨h⁻¹ • x, mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
      (fun y : b65z_fibre c D.C t ↦ h⁻¹ • y) x ξ⟩ hhx]
  rw [hM x hu h⁻¹, hR x hu h⁻¹, inv_inv,
    b65g_ds_deck D t hab hba poles x hu h⁻¹ ξ,
    ← Matrix.mulVec_mulVec]
  change ((b65g_mat conj h *ᵥ v) ⬝ᵥ (M x *ᵥ R x)) * b65g_ds D t a b ⟨x, ξ⟩ = _
  rw [Matrix.dotProduct_transpose_mulVec (b65g_mat conj h) v (M x *ᵥ R x),
    dotProduct_comm (M x *ᵥ R x) (b65g_mat conj h *ᵥ v)]

/-- The inverse of a representation matrix is the matrix of the inverse element. -/
theorem b65g_mat_inv (conj : Bool) (h : b4b_Group) :
    (b65g_mat conj h)⁻¹ = b65g_mat conj h⁻¹ := by
  apply Matrix.inv_eq_right_inv
  rw [← b65g_mat_mul, mul_inv_cancel, b65g_mat_one]

variable {p : Fin 12 → ℂ} {O : b65p_Outputs p} {g : Fin 13 → b4b_Group}
  {D : b65z_SharedFamily (b65z_centre p) g} (S : b65g_Solutions p O D)
  (θ : ℂ) (hθ : θ ∈ ball (0 : ℂ) S.radius)
  (t : b6t_polydisc (b65z_centre p)) (ht : t.val = b65p_curve p θ)
include hθ ht

/-- Any holomorphic extension of the r-form family is equivariant. -/
theorem b65g_homG_of_rRepresents (r : Fin 4 → RatFunc ℂ)
    (φ : (Fin 4 → ℂ) →ₗ[ℂ]
      (TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre (b65z_centre p) D.C t) → ℂ))
    (hφ : ∀ v, φ v ∈ b3_HolForm ℂ (b65z_fibre (b65z_centre p) D.C t))
    (he : b65g_rRepresents D t (b65p_moving p θ 10) (b65p_moving p θ 11)
      (b65p_poles p θ) (b65g_Y S θ t) r φ) : φ ∈ b65g_homG D t S.conj := by
  have hθO : θ ∈ ball (0 : ℂ) O.radius := ball_subset_ball S.radius_le hθ
  obtain ⟨ha, hb, hab⟩ := b65g_moving_ne p O θ hθO
  apply b65g_homG_of_matrix_formula D t (mul_ne_zero ha hb)
    (sub_ne_zero.mpr (Ne.symm hab)) (b65p_poles p θ) S.conj φ hφ
    (fun x ↦ (b65g_Y S θ t x)⁻¹)
    (fun x j ↦ b65q_eval (r j) (b65g_sFun D t (b65p_moving p θ 10) (b65p_moving p θ 11) x))
  · intro x hx h
    rw [b65g_Y_deck S θ hθ t ht x hx h, Matrix.mul_inv_rev,
      ← Matrix.transpose_nonsing_inv, b65g_mat_inv]
  · intro x hx h
    rw [b65g_sFun_deck D t h x]
  · exact he

/-- Any holomorphic extension of the q-form family is equivariant. -/
theorem b65g_homG_of_qRepresents (q : Fin 4 → RatFunc ℂ)
    (φ : (Fin 4 → ℂ) →ₗ[ℂ]
      (TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre (b65z_centre p) D.C t) → ℂ))
    (hφ : ∀ v, φ v ∈ b3_HolForm ℂ (b65z_fibre (b65z_centre p) D.C t))
    (he : b65g_qRepresents D t (b65p_moving p θ 10) (b65p_moving p θ 11)
      (b65p_poles p θ) (b65g_Y S θ t) q φ) : φ ∈ b65g_homG D t (!S.conj) := by
  have hθO : θ ∈ ball (0 : ℂ) O.radius := ball_subset_ball S.radius_le hθ
  obtain ⟨ha, hb, hab⟩ := b65g_moving_ne p O θ hθO
  apply b65g_homG_of_matrix_formula D t (mul_ne_zero ha hb)
    (sub_ne_zero.mpr (Ne.symm hab)) (b65p_poles p θ) (!S.conj) φ hφ
    (fun x ↦ (b65g_Y S θ t x)ᵀ)
    (fun x j ↦ b65q_eval (q j) (b65g_sFun D t (b65p_moving p θ 10) (b65p_moving p θ 11) x))
  · intro x hx h
    rw [b65g_Y_deck S θ hθ t ht x hx h, Matrix.transpose_mul,
      Matrix.transpose_transpose, b65g_mat_dual]
  · intro x hx h
    rw [b65g_sFun_deck D t h x]
  · exact he

end HodgeLean.Foundations.Program
