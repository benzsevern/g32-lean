import HodgeLean.Foundations.Program.CoverDictionaryRational

/-! Deck transformations of form coefficients. -/

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

section Fibre
variable {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group} (D : b65z_SharedFamily c g)
  (t : b6t_polydisc c) {a b : ℂ}

/-- The coordinate function is invariant under deck transformations. -/
theorem b65g_sFun_deck (h : b4b_Group) (x : b65z_fibre c D.C t) :
    b65g_sFun D t a b (h • x) = b65g_sFun D t a b x :=
  congrArg (b65g_sCoord a b) ((D.hgal t).1 h x)

/-- The differential of the coordinate function is invariant under deck pullback. -/
theorem b65g_ds_deck (hab : a * b ≠ 0) (hba : b - a ≠ 0)
    (poles : Fin 4 ⊕ Fin 12 → ℂ) (x : b65z_fibre c D.C t)
    (hx : x ∈ b65g_good D t a b poles) (h : b4b_Group) (ξ : ℂ) :
    b65g_ds D t a b ⟨h • x,
      mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (fun y : b65z_fibre c D.C t ↦ h • y) x ξ⟩ =
      b65g_ds D t a b ⟨x, ξ⟩ := by
  have hhx := (b65g_goodSub D t a b poles).smul_mem h hx
  obtain ⟨z, hz, hz', -⟩ := hhx
  have hs := (b65g_sFun_hasMFDerivAt D t hab hba (h • x) z hz hz').mdifferentiableAt
  have hd := mfderiv_comp x hs ((D.hG t h).mdifferentiable (by simp)).mdifferentiableAt
  have hfun : b65g_sFun D t a b ∘ (fun y : b65z_fibre c D.C t ↦ h • y) =
      b65g_sFun D t a b := funext (b65g_sFun_deck D t h)
  rw [hfun] at hd
  exact congrArg (fun L : ℂ →L[ℂ] ℂ ↦ L ξ) hd.symm

end Fibre

variable {p : Fin 12 → ℂ} {O : b65p_Outputs p} {g : Fin 13 → b4b_Group}
  {D : b65z_SharedFamily (b65z_centre p) g} (S : b65g_Solutions p O D)
  (θ : ℂ) (hθ : θ ∈ ball (0 : ℂ) S.radius)
  (t : b6t_polydisc (b65z_centre p)) (ht : t.val = b65p_curve p θ)

include hθ ht

/-- Dividing a holomorphic equivariant form family by `ds` gives the contragredient
transformation of its coordinate functionals. -/
theorem b65g_form_ratio_deck (conj : Bool)
    (φ : (Fin 4 → ℂ) →ₗ[ℂ]
      (TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre (b65z_centre p) D.C t) → ℂ))
    (hφ : φ ∈ b65g_homG D t conj)
    (x : b65z_fibre (b65z_centre p) D.C t)
    (hx : x ∈ b65g_good D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ))
    (h : b4b_Group) (v : Fin 4 → ℂ) :
    φ v ⟨h • x, (1 : ℂ)⟩ /
        b65g_ds D t (b65p_moving p θ 10) (b65p_moving p θ 11) ⟨h • x, (1 : ℂ)⟩ =
      φ (b65g_rep conj h⁻¹ v) ⟨x, (1 : ℂ)⟩ /
        b65g_ds D t (b65p_moving p θ 10) (b65p_moving p θ 11) ⟨x, (1 : ℂ)⟩ := by
  have hθO : θ ∈ ball (0 : ℂ) O.radius := ball_subset_ball S.radius_le hθ
  obtain ⟨ha, hb, hab⟩ := b65g_moving_ne p O θ hθO
  have hab' := mul_ne_zero ha hb
  have hba := sub_ne_zero.mpr (Ne.symm hab)
  have hhx := (b65g_goodSub D t (b65p_moving p θ 10) (b65p_moving p θ 11)
    (b65p_poles p θ)).smul_mem h hx
  let J : ℂ := mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
    (fun y : b65z_fibre (b65z_centre p) D.C t ↦ h • y) x (1 : ℂ)
  have he := congrFun (hφ.2 h⁻¹ v) ⟨x, (1 : ℂ)⟩
  change φ (b65g_rep conj h⁻¹ v) ⟨x, (1 : ℂ)⟩ =
    φ v ⟨h⁻¹⁻¹ • x, mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
      (fun y : b65z_fibre (b65z_centre p) D.C t ↦ h⁻¹⁻¹ • y) x (1 : ℂ)⟩ at he
  rw [inv_inv] at he
  have he' := he.trans (caf_holForm_apply_smul _ (hφ.1 v) (h • x) J)
  have hd := b65g_ds_deck D t hab' hba (b65p_poles p θ) x hx h (1 : ℂ)
  have hd' := (b65g_ds_smul D t (h • x) J).symm.trans hd
  apply (div_eq_div_iff (b65g_ds_ne_good O D θ hθO t ht (h • x) hhx)
    (b65g_ds_ne_good O D θ hθO t ht x hx)).2
  rw [he', ← hd']
  ring

/-- The coordinate vector of an equivariant family divided by `ds` transforms by the
transpose of the inverse representation matrix. -/
theorem b65g_form_ratio_vector_deck (conj : Bool)
    (φ : (Fin 4 → ℂ) →ₗ[ℂ]
      (TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre (b65z_centre p) D.C t) → ℂ))
    (hφ : φ ∈ b65g_homG D t conj)
    (x : b65z_fibre (b65z_centre p) D.C t)
    (hx : x ∈ b65g_good D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ))
    (h : b4b_Group) :
    (fun i ↦ φ (Pi.single i 1) ⟨h • x, (1 : ℂ)⟩ /
      b65g_ds D t (b65p_moving p θ 10) (b65p_moving p θ 11) ⟨h • x, (1 : ℂ)⟩) =
      (b65g_mat conj h⁻¹)ᵀ *ᵥ (fun i ↦ φ (Pi.single i 1) ⟨x, (1 : ℂ)⟩ /
        b65g_ds D t (b65p_moving p θ 10) (b65p_moving p θ 11) ⟨x, (1 : ℂ)⟩) := by
  funext i
  rw [b65g_form_ratio_deck S θ hθ t ht conj φ hφ x hx h]
  have hrep : b65g_rep conj h⁻¹ (Pi.single i 1) = fun j ↦ b65g_mat conj h⁻¹ j i := by
    change (b65g_mat conj h⁻¹) *ᵥ (Pi.single i 1) = _
    simp
    rfl
  rw [hrep, caf_linearMap_coordinates]
  simp only [
    Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.sum_div, mul_div_assoc]

omit hθ ht in
/-- The natural matrices, including their conjugates, multiply as a representation. -/
theorem b65g_mat_mul (conj : Bool) (h k : b4b_Group) :
    b65g_mat conj (h * k) = b65g_mat conj h * b65g_mat conj k := by
  cases conj <;> simp [b65g_mat, map_mul, Matrix.map_mul]

omit hθ ht in
/-- The natural matrix of the identity, including its conjugate, is the identity. -/
theorem b65g_mat_one (conj : Bool) : b65g_mat conj (1 : b4b_Group) = 1 := by
  cases conj <;> simp [b65g_mat]

/-- The matrix of a pulled-back fundamental solution transforms on the right. -/
theorem b65g_Y_deck (x : b65z_fibre (b65z_centre p) D.C t)
    (hx : x ∈ b65g_good D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ))
    (h : b4b_Group) :
    b65g_Y S θ t (h • x) = b65g_Y S θ t x * (b65g_mat S.conj h)ᵀ := by
  have he := congrArg b65q_mat (S.equivariant θ hθ t ht x hx h)
  change b65q_mat (S.Y θ (h • x).val) =
    b65q_mat (S.Y θ x.val * b65r_operator ((b65g_mat S.conj h)ᵀ)) at he
  rw [caf_mat_mul, b65q_mat_operator] at he
  exact he

/-- Multiplying the r-side coefficient vector by `Y` makes it invariant. -/
theorem b65g_r_coefficient_invariant
    (φ : (Fin 4 → ℂ) →ₗ[ℂ]
      (TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre (b65z_centre p) D.C t) → ℂ))
    (hφ : φ ∈ b65g_homG D t S.conj)
    (x : b65z_fibre (b65z_centre p) D.C t)
    (hx : x ∈ b65g_good D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ))
    (h : b4b_Group) :
    b65g_Y S θ t (h • x) *ᵥ (fun i ↦ φ (Pi.single i 1) ⟨h • x, (1 : ℂ)⟩ /
      b65g_ds D t (b65p_moving p θ 10) (b65p_moving p θ 11) ⟨h • x, (1 : ℂ)⟩) =
    b65g_Y S θ t x *ᵥ (fun i ↦ φ (Pi.single i 1) ⟨x, (1 : ℂ)⟩ /
      b65g_ds D t (b65p_moving p θ 10) (b65p_moving p θ 11) ⟨x, (1 : ℂ)⟩) := by
  rw [b65g_Y_deck S θ hθ t ht x hx h,
    b65g_form_ratio_vector_deck S θ hθ t ht S.conj φ hφ x hx h,
    Matrix.mulVec_mulVec, Matrix.mul_assoc, ← Matrix.transpose_mul,
    ← b65g_mat_mul, inv_mul_cancel, b65g_mat_one, Matrix.transpose_one, Matrix.mul_one]

omit hθ ht in
/-- Unitarity identifies the dual matrix with the conjugate representation. -/
theorem b65g_mat_dual (conj : Bool) (h : b4b_Group) :
    (b65g_mat (!conj) h⁻¹)ᵀ = b65g_mat conj h := by
  cases conj <;> ext i j <;>
    simp [b65g_mat, b63l_toMatrix_inv_eq_star, Matrix.star_apply]

omit hθ ht in
/-- Representation matrices have invertible determinants. -/
theorem b65g_mat_det_unit (conj : Bool) (h : b4b_Group) :
    IsUnit (b65g_mat conj h).det := by
  have he : b65g_mat conj h * b65g_mat conj h⁻¹ = 1 := by
    rw [← b65g_mat_mul, mul_inv_cancel, b65g_mat_one]
  have hd := congrArg Matrix.det he
  rw [Matrix.det_mul, Matrix.det_one] at hd
  apply isUnit_iff_ne_zero.mpr
  intro hz
  rw [hz, zero_mul] at hd
  exact zero_ne_one hd

/-- Multiplying the q-side coefficient vector by `Y⁻ᵀ` makes it invariant. -/
theorem b65g_q_coefficient_invariant
    (φ : (Fin 4 → ℂ) →ₗ[ℂ]
      (TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre (b65z_centre p) D.C t) → ℂ))
    (hφ : φ ∈ b65g_homG D t (!S.conj))
    (x : b65z_fibre (b65z_centre p) D.C t)
    (hx : x ∈ b65g_good D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ))
    (h : b4b_Group) :
    (b65g_Y S θ t (h • x))⁻¹ᵀ *ᵥ (fun i ↦ φ (Pi.single i 1) ⟨h • x, (1 : ℂ)⟩ /
      b65g_ds D t (b65p_moving p θ 10) (b65p_moving p θ 11) ⟨h • x, (1 : ℂ)⟩) =
    (b65g_Y S θ t x)⁻¹ᵀ *ᵥ (fun i ↦ φ (Pi.single i 1) ⟨x, (1 : ℂ)⟩ /
      b65g_ds D t (b65p_moving p θ 10) (b65p_moving p θ 11) ⟨x, (1 : ℂ)⟩) := by
  rw [b65g_Y_deck S θ hθ t ht x hx h,
    b65g_form_ratio_vector_deck S θ hθ t ht (!S.conj) φ hφ x hx h,
    b65g_mat_dual, Matrix.mul_inv_rev, Matrix.transpose_mul,
    ← Matrix.transpose_nonsing_inv, Matrix.transpose_transpose,
    Matrix.mulVec_mulVec, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ (b65g_mat_det_unit S.conj h), Matrix.mul_one]

end HodgeLean.Foundations.Program
