import HodgeLean.Foundations.Program.CoverDictionaryDefs

/-! # B6-5 stage 5d, geometric part: forms, evaluations and the numerator matrix

Evaluation of the rational vectors of the 5d systems away from the poles (additive and
multiplicative there), invertibility of the matrices of a record of solutions, the contraction
identity `Σ_i (Y⁻¹ r)_i (Yᵀ q)_i = qᵀ r`, and the numerator statement from the frames solving the
full systems. HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Metric Matrix Filter Polynomial Manifold
open scoped Topology ContDiff
open HodgeLean.Papers
namespace HodgeLean.Foundations.Program

/-- **`f` has no pole at `s`**: its reduced denominator does not vanish at `s`.
Source: Mathlib `RatFunc.denom`, `RatFunc.eval_add`, `RatFunc.eval_mul`. -/
def b65g_reg (s : ℂ) (f : RatFunc ℂ) : Prop := f.denom.eval s ≠ 0

/-- Sums of functions without a pole at `s` have no pole at `s`. -/
theorem b65g_reg_add {s : ℂ} {f g : RatFunc ℂ} (hf : b65g_reg s f) (hg : b65g_reg s g) :
    b65g_reg s (f + g) := fun h ↦ by
  have := Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero (RatFunc.denom_add_dvd f g) h
  rw [eval_mul] at this
  exact (mul_ne_zero hf hg) this

/-- Products of functions without a pole at `s` have no pole at `s`. -/
theorem b65g_reg_mul {s : ℂ} {f g : RatFunc ℂ} (hf : b65g_reg s f) (hg : b65g_reg s g) :
    b65g_reg s (f * g) := fun h ↦ by
  have := Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero (RatFunc.denom_mul_dvd f g) h
  rw [eval_mul] at this
  exact (mul_ne_zero hf hg) this

/-- The zero function has no pole. -/
theorem b65g_reg_zero (s : ℂ) : b65g_reg s 0 := by simp [b65g_reg]

/-- Finite sums of functions without a pole at `s` have no pole at `s`. -/
theorem b65g_reg_sum {ι : Type*} (S : Finset ι) {s : ℂ} {f : ι → RatFunc ℂ}
    (h : ∀ i ∈ S, b65g_reg s (f i)) : b65g_reg s (∑ i ∈ S, f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using b65g_reg_zero s
  | insert a S ha ih =>
    rw [Finset.sum_insert ha]
    exact b65g_reg_add (h a (Finset.mem_insert_self _ _))
      (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))

/-- Evaluation is additive away from the poles. -/
theorem b65g_eval_add {s : ℂ} {f g : RatFunc ℂ} (hf : b65g_reg s f) (hg : b65g_reg s g) :
    b65q_eval (f + g) s = b65q_eval f s + b65q_eval g s := by
  unfold b65q_eval
  exact RatFunc.eval_add (f := RingHom.id ℂ) (a := s) (by rw [eval₂_id]; exact hf) (by rw [eval₂_id]; exact hg)

/-- Evaluation is multiplicative away from the poles. -/
theorem b65g_eval_mul {s : ℂ} {f g : RatFunc ℂ} (hf : b65g_reg s f) (hg : b65g_reg s g) :
    b65q_eval (f * g) s = b65q_eval f s * b65q_eval g s := by
  unfold b65q_eval
  exact RatFunc.eval_mul (f := RingHom.id ℂ) (a := s) (by rw [eval₂_id]; exact hf) (by rw [eval₂_id]; exact hg)

/-- Evaluation commutes with finite sums away from the poles. -/
theorem b65g_eval_sum {ι : Type*} (S : Finset ι) {s : ℂ} {f : ι → RatFunc ℂ}
    (h : ∀ i ∈ S, b65g_reg s (f i)) : b65q_eval (∑ i ∈ S, f i) s = ∑ i ∈ S, b65q_eval (f i) s := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [b65q_eval]
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, b65g_eval_add (h a (Finset.mem_insert_self _ _))
      (b65g_reg_sum S fun i hi ↦ h i (Finset.mem_insert_of_mem hi)),
      ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi)]

/-- A principal part at `a` has no pole at `s ≠ a`. -/
theorem b65g_reg_frac {s a : ℂ} (c : ℂ) (k : ℕ) (h : s ≠ a) :
    b65g_reg s (RatFunc.C c / (RatFunc.X - RatFunc.C a) ^ k) := by
  have he : RatFunc.C c / (RatFunc.X - RatFunc.C a) ^ k =
      algebraMap ℂ[X] (RatFunc ℂ) (Polynomial.C c) /
        algebraMap ℂ[X] (RatFunc ℂ) ((X - Polynomial.C a) ^ k) := by
    simp [RatFunc.algebraMap_C, RatFunc.algebraMap_X]
  rw [b65g_reg, he]
  intro h0
  have := Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero (RatFunc.denom_div_dvd _ _) h0
  simp only [eval_pow, eval_sub, eval_X, eval_C] at this
  exact h (sub_eq_zero.mp (pow_eq_zero_iff'.mp this).1)

/-- The r-vectors have no pole off the pole configuration. -/
theorem b65g_reg_principal (t : Fin 4 ⊕ Fin 12 → ℂ) (c : Fin 36 → ℂ) (j : Fin 4) {s : ℂ}
    (hs : s ∉ Set.range t) : b65g_reg s (b65q_principal t c j) :=
  b65g_reg_sum _ fun _ _ ↦ b65g_reg_frac _ _ fun h ↦ hs ⟨_, h.symm⟩

/-- The q-vectors have no pole off the pole configuration. -/
theorem b65g_reg_qVector (t : Fin 4 ⊕ Fin 12 → ℂ) (node : Fin 12 → ℂ) (w : Fin 12 → Fin 4 → ℂ)
    (d : Fin 48 → ℂ) (j : Fin 4) {s : ℂ} (hs : s ∉ Set.range t) :
    b65g_reg s (b65q_qVector t node w d j) := by
  refine b65g_reg_add (b65g_reg_principal t _ j hs) (b65g_reg_sum _ fun x _ ↦ ?_)
  have h := b65g_reg_frac (s := s) (k := 1) ((∑ v : Fin 6,
    d ⟨36 + 6 * (b65q_fibreIndex x).val + v.val, by omega⟩ * node x ^ v.val) * w x j)
    (fun h ↦ hs ⟨Sum.inr x, h.symm⟩)
  rwa [pow_one] at h

/-- A continuous-linear unit has an invertible matrix. -/
theorem b65g_mat_det_ne {L : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)} (hL : IsUnit L) :
    IsUnit (b65q_mat L).det := by
  obtain ⟨u, rfl⟩ := hL
  have h : b65q_mat u.val * b65q_mat u.inv = 1 := by
    simp only [b65q_mat]
    rw [← LinearMap.toMatrix'_mul]
    have : ((u.val : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 4 → ℂ)) * (u.inv : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 4 → ℂ)))
        = 1 := by
      ext v i
      exact congrFun (congrArg (fun L : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ) ↦ L (Pi.single v 1)) u.val_inv) i
    rw [this, LinearMap.toMatrix'_one]
  exact Matrix.isUnit_det_of_right_inverse h

/-- The contraction convention `Σ_i (Y⁻¹ r)_i (Yᵀ q)_i = qᵀ r`. -/
theorem b65g_contract_identity (Y : Matrix (Fin 4) (Fin 4) ℂ) (hY : IsUnit Y.det) (r q : Fin 4 → ℂ) :
    ∑ i : Fin 4, (Y⁻¹ *ᵥ r) i * (Yᵀ *ᵥ q) i = q ⬝ᵥ r := by
  have h : ∑ i : Fin 4, (Y⁻¹ *ᵥ r) i * (Yᵀ *ᵥ q) i = (Yᵀ *ᵥ q) ⬝ᵥ (Y⁻¹ *ᵥ r) := by
    simp only [dotProduct]; exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
  rw [h, ← vecMul_transpose, transpose_transpose, ← dotProduct_mulVec, mulVec_mulVec,
    mul_nonsing_inv _ hY, one_mulVec]

end HodgeLean.Foundations.Program

namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.totalChart
  b65z_SharedFamily.totalMan b65z_SharedFamily.fibreChart b65z_SharedFamily.fibreMan
  b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact b65z_SharedFamily.fibreConnected
  b65z_SharedFamily.fibreFaithful

/-- The `s`-coordinate of a regular point is not a pole. -/
theorem b65g_good_sFun {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group} {D : b65z_SharedFamily c g}
    {t : b6t_polydisc c} {a b : ℂ} {poles : Fin 4 ⊕ Fin 12 → ℂ} {x : b65z_fibre c D.C t}
    (hx : x ∈ b65g_good D t a b poles) : b65g_sFun D t a b x ∉ Set.range poles := by
  obtain ⟨z, hz, -, hzs⟩ := hx
  simpa [b65g_sFun, hz] using hzs

/-- At a regular point, the contraction of the forms of `r` and `q` is the quadratic
differential of a numerator of `D qᵀ r`. -/
theorem b65g_numerator_pointwise {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c) (a b : ℂ) (poles : Fin 4 ⊕ Fin 12 → ℂ)
    (Y : b65z_fibre c D.C t → Matrix (Fin 4) (Fin 4) ℂ) (r q : Fin 4 → RatFunc ℂ)
    (φ ψ : (Fin 4 → ℂ) →ₗ[ℂ] (TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre c D.C t) → ℂ))
    (hr : b65g_rRepresents D t a b poles Y r φ) (hq : b65g_qRepresents D t a b poles Y q ψ)
    (N : Fin 10 → ℂ)
    (hN : (∑ j : Fin 10, RatFunc.C (N j) * RatFunc.X ^ j.val) =
      algebraMap ℂ[X] (RatFunc ℂ) (b65q_denominator poles) * ∑ j : Fin 4, q j * r j)
    (u : TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre c D.C t)) (hu : u.1 ∈ b65g_good D t a b poles)
    (hY : IsUnit (Y u.1).det)
    (hreg : ∀ j, b65g_reg (b65g_sFun D t a b u.1) (r j) ∧ b65g_reg (b65g_sFun D t a b u.1) (q j)) :
    b65g_contract φ ψ u = b65g_quadratic D t a b poles N u := by
  have hD : algebraMap ℂ[X] (RatFunc ℂ) (b65q_denominator poles) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (Monic.ne_zero (by
      unfold b65q_denominator
      exact monic_X.mul (monic_prod_of_monic _ _ fun x _ ↦ monic_X_sub_C _)))
  have hq' : (∑ j : Fin 10, RatFunc.C (N j) * RatFunc.X ^ j.val) /
      algebraMap ℂ[X] (RatFunc ℂ) (b65q_denominator poles) = ∑ j : Fin 4, q j * r j := by
    rw [hN, mul_div_cancel_left₀ _ hD]
  simp only [b65g_contract, b65g_quadratic, hq']
  rw [b65g_eval_sum _ fun j _ ↦ b65g_reg_mul (hreg j).2 (hreg j).1]
  simp only [hr _ u hu, hq _ u hu, b65g_rForm, b65g_qForm, single_one_dotProduct]
  simp only [fun i ↦ b65g_eval_mul (hreg i).2 (hreg i).1]
  have h := b65g_contract_identity (Y u.1) hY (fun j ↦ b65q_eval (r j) (b65g_sFun D t a b u.1))
    (fun j ↦ b65q_eval (q j) (b65g_sFun D t a b u.1))
  simp only [dotProduct] at h
  rw [← h, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- The numerator statement from the frames solving the full systems. -/
theorem b65g_numerator_of_kernels (p : Fin 12 → ℂ) (O : b65p_Outputs p) {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily (b65z_centre p) g) (S : b65g_Solutions p O D) (ε : ℝ) (hε : 0 < ε)
    (hεS : ε ≤ S.radius) (hk : ∀ θ ∈ ball (0 : ℂ) ε,
      b65q_rFamily p O.residue θ * b65q_rFrame p O.residue θ = 0 ∧
      b65q_qFamily p O.residue θ * b65q_qFrame p O.residue θ = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ S.radius ∧ ∀ θ ∈ ball (0 : ℂ) ε,
      ∀ t : b6t_polydisc (b65z_centre p), t.val = b65p_curve p θ →
      ∀ (a b : Fin 3) (φ ψ : (Fin 4 → ℂ) →ₗ[ℂ] (TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre (b65z_centre p) D.C t) → ℂ)),
        φ ∈ b65g_homG D t S.conj → ψ ∈ b65g_homG D t (!S.conj) →
        b65g_rRepresents D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) (b65g_Y S θ t)
          (b65q_principal (b65p_poles p θ) (fun i ↦ b65q_rFrame p O.residue θ i a)) φ →
        b65g_qRepresents D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) (b65g_Y S θ t)
          (b65q_qVector (b65p_poles p θ) p (b65q_left O.residue θ) (fun i ↦ b65q_qFrame p O.residue θ i b)) ψ →
        ∀ u : TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre (b65z_centre p) D.C t), u.1 ∈ b65g_good D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) →
          b65g_contract φ ψ u = b65g_quadratic D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ)
            (b65q_numMatrix p O.residue θ (finProdFinEquiv (a, b))) u := by
  obtain ⟨ε2, hε2, -, -, hnum, -⟩ := b65q_family_numerators p O
  refine ⟨min ε ε2, lt_min hε hε2, (min_le_left _ _).trans hεS, ?_⟩
  intro θ hθ t ht a b φ ψ _ _ hr hq u hu
  have hθ1 : θ ∈ ball (0 : ℂ) ε := ball_subset_ball (min_le_left _ _) hθ
  have hθ2 : θ ∈ ball (0 : ℂ) ε2 := ball_subset_ball (min_le_right _ _) hθ
  have hθS : θ ∈ ball (0 : ℂ) S.radius := ball_subset_ball hεS hθ1
  obtain ⟨hkr, hkq⟩ := hk θ hθ1
  have hN := hnum θ hθ2 hkr hkq a b
  refine b65g_numerator_pointwise D t _ _ _ _ _ _ φ ψ hr hq _ ?_ u hu
    (b65g_mat_det_ne (S.unit θ hθS t ht u.1 hu)) fun j ↦
      ⟨b65g_reg_principal _ _ _ (b65g_good_sFun hu), b65g_reg_qVector _ _ _ _ _ (b65g_good_sFun hu)⟩
  rw [hN]
  rfl

end HodgeLean.Foundations.Program
