import HodgeLean.Foundations.Program.KernelFramesFamilyBase

/-! # B6-5 stage 5d, family part: the Schlesinger flow conjugates the residues

Uniqueness for linear equations on a disc (Grönwall), applied to the Schlesinger equations of a
5c record: every polynomial identity of an initial residue persists along the path
(`b65q_aeval_flow`), and the traces of the residues are constant (`b65q_trace_flow`).
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Metric Matrix Filter Polynomial
open scoped Topology
namespace HodgeLean.Foundations.Program

/-- **Uniqueness for linear equations on a disc.** A solution of `M' = L(θ) M` on a disc about
`0`, with `L` continuous there and `M 0 = 0`, vanishes on the disc. -/
theorem b65q_linear_flow_zero {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] {r : ℝ}
    (M : ℂ → F) (L : ℂ → F →L[ℂ] F) (hM : ∀ θ ∈ ball (0 : ℂ) r, HasDerivAt M (L θ (M θ)) θ)
    (hL : ContinuousOn L (ball 0 r)) (h0 : M 0 = 0) : ∀ θ ∈ ball (0 : ℂ) r, M θ = 0 := by
  intro θ₀ hθ₀
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, (t : ℂ) * θ₀ ∈ ball (0 : ℂ) r := by
    intro t ht
    rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
    rw [mem_ball_zero_iff] at hθ₀
    calc t * ‖θ₀‖ ≤ 1 * ‖θ₀‖ := by gcongr; exact ht.2
      _ < r := by rw [one_mul]; exact hθ₀
  have hLc : ContinuousOn (fun t : ℝ ↦ L ((t : ℂ) * θ₀)) (Icc 0 1) :=
    hL.comp (by fun_prop) hseg
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hLc
  set g : ℝ → F := fun t ↦ M ((t : ℂ) * θ₀)
  have hg : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt g (θ₀ • L ((t : ℂ) * θ₀) (g t)) t := by
    intro t ht
    have hh : HasDerivAt (fun t : ℝ ↦ (t : ℂ) * θ₀) θ₀ t := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const θ₀
    exact (hM _ (hseg t ht)).scomp t hh
  have hz := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right (K := ‖θ₀‖ * C)
    (f := g) (a := 0) (b := 1)
    (fun t ht ↦ (hg t ht).continuousAt.continuousWithinAt)
    (fun t ht ↦ (hg t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (by simp [g, h0])
    (fun t ht ↦ by
      rw [norm_smul, mul_assoc]
      gcongr
      exact ((L _).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (hC t (Ico_subset_Icc_self ht)) (norm_nonneg _)))
  have := hz 1 ⟨zero_le_one, le_rfl⟩
  simpa [g] using this

local notation "𝔼" => (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)

/-- The matrix of a residue operator, as an algebra map. -/
def b65q_matAlg : 𝔼 →ₐ[ℂ] Matrix (Fin 4) (Fin 4) ℂ where
  toFun := b65q_mat
  map_one' := by simp [b65q_mat]
  map_mul' a b := by simp [b65q_mat, ContinuousLinearMap.coe_mul, LinearMap.toMatrix'_mul]
  map_zero' := by simp [b65q_mat]
  map_add' a b := by simp [b65q_mat]
  commutes' c := by
    simp [b65q_mat, Algebra.algebraMap_eq_smul_one, Matrix.smul_one_eq_diagonal]

theorem b65q_matAlg_apply (T : 𝔼) : b65q_matAlg T = b65q_mat T := rfl

theorem b65q_mat_injective : Function.Injective b65q_mat := by
  intro T₁ T₂ h
  exact ContinuousLinearMap.coe_injective (LinearMap.toMatrix'.injective h)

/-- The entry `(i, j)` of the matrix of an operator, as a continuous linear functional. -/
def b65q_entryCLM (i j : Fin 4) : 𝔼 →L[ℂ] ℂ :=
  (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.apply ℂ (Fin 4 → ℂ) (Pi.single j 1))

theorem b65q_entryCLM_apply (i j : Fin 4) (T : 𝔼) : b65q_entryCLM i j T = b65q_mat T i j := by
  simp [b65q_entryCLM, b65q_mat, LinearMap.toMatrix'_apply]

/-- The coefficient of the Schlesinger equation at the pole `q`:
`S_q = Σ_{q' ≠ q} (v_q − v_{q'})/(t_q − t_{q'}) A_{q'}`. -/
def b65q_S (p : Fin 12 → ℂ) (R : ℂ → Fin 4 ⊕ Fin 12 → 𝔼) (θ : ℂ) (q : Fin 4 ⊕ Fin 12) : 𝔼 :=
  ∑ q', if q' = q then 0 else
    ((b65p_velocity p q - b65p_velocity p q') / (b65p_poles p θ q - b65p_poles p θ q')) • R θ q'

theorem b65q_field_eq (p : Fin 12 → ℂ) (R : ℂ → Fin 4 ⊕ Fin 12 → 𝔼) (θ : ℂ)
    (q : Fin 4 ⊕ Fin 12) :
    b65p_schlesingerField (Fin 4 → ℂ) (b65p_velocity p) (b65p_poles p θ) (R θ) q =
      b65q_S p R θ q * R θ q - R θ q * b65q_S p R θ q := by
  rw [b65p_schlesingerField, b65q_S, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun q' _ ↦ ?_
  split_ifs <;> simp [smul_mul_assoc, mul_smul_comm, smul_sub]

theorem b65q_poles_continuous (p : Fin 12 → ℂ) (q : Fin 4 ⊕ Fin 12) :
    Continuous fun θ ↦ b65p_poles p θ q := by
  rcases q with k | x
  · simp only [b65p_poles, Sum.elim_inl]; exact continuous_const
  · simp only [b65p_poles, Sum.elim_inr]; fun_prop

theorem b65q_S_continuousOn {p : Fin 12 → ℂ} (O : b65p_Outputs p) (q : Fin 4 ⊕ Fin 12) :
    ContinuousOn (fun θ ↦ b65q_S p O.residue θ q) (ball 0 O.radius) := by
  apply continuousOn_finset_sum
  intro q' _
  split_ifs with h
  · exact continuousOn_const
  · refine ContinuousOn.smul (f := fun θ ↦ (b65p_velocity p q - b65p_velocity p q') /
      (b65p_poles p θ q - b65p_poles p θ q')) ?_ (O.residue_analytic q').continuousOn
    refine continuousOn_const.div ((b65q_poles_continuous p q).sub
      (b65q_poles_continuous p q')).continuousOn fun θ hθ ↦ ?_
    exact sub_ne_zero.mpr fun he ↦ h (O.poles_injective θ hθ he).symm

theorem b65q_pow_deriv {p : Fin 12 → ℂ} (O : b65p_Outputs p) (q : Fin 4 ⊕ Fin 12) {θ : ℂ}
    (hθ : θ ∈ ball (0 : ℂ) O.radius) (n : ℕ) :
    HasDerivAt (fun θ ↦ O.residue θ q ^ n)
      (b65q_S p O.residue θ q * O.residue θ q ^ n - O.residue θ q ^ n * b65q_S p O.residue θ q) θ := by
  have hA := O.schlesinger θ hθ q
  rw [b65q_field_eq] at hA
  induction n with
  | zero => simpa using hasDerivAt_const θ (1 : 𝔼)
  | succ n ih =>
    have := ih.mul hA
    simp only [pow_succ]
    convert this using 1
    noncomm_ring

theorem b65q_aeval_deriv {p : Fin 12 → ℂ} (O : b65p_Outputs p) (q : Fin 4 ⊕ Fin 12) {θ : ℂ}
    (hθ : θ ∈ ball (0 : ℂ) O.radius) (f : ℂ[X]) :
    HasDerivAt (fun θ ↦ aeval (O.residue θ q) f)
      (b65q_S p O.residue θ q * aeval (O.residue θ q) f -
        aeval (O.residue θ q) f * b65q_S p O.residue θ q) θ := by
  simp only [aeval_eq_sum_range]
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  apply HasDerivAt.fun_sum
  intro i _
  convert (b65q_pow_deriv O q hθ i).const_smul (f.coeff i) using 1
  rw [smul_sub, mul_smul_comm, smul_mul_assoc]

/-- **Polynomial identities propagate along the Schlesinger flow.** -/
theorem b65q_aeval_flow {p : Fin 12 → ℂ} (O : b65p_Outputs p) (q : Fin 4 ⊕ Fin 12) (f : ℂ[X])
    (h0 : aeval (b65q_res O.residue 0 q) f = 0) :
    ∀ θ ∈ ball (0 : ℂ) O.radius, aeval (b65q_res O.residue θ q) f = 0 := by
  have hop : ∀ θ, aeval (b65q_res O.residue θ q) f = b65q_mat (aeval (O.residue θ q) f) := by
    intro θ
    rw [b65q_res, ← b65q_matAlg_apply, ← b65q_matAlg_apply, aeval_algHom_apply]
  have h0' : aeval (O.residue 0 q) f = 0 :=
    b65q_mat_injective (by rw [← hop, h0]; simp [b65q_mat])
  intro θ hθ
  rw [hop, b65q_linear_flow_zero (fun θ ↦ aeval (O.residue θ q) f)
    (fun θ ↦ ContinuousLinearMap.mul ℂ 𝔼 (b65q_S p O.residue θ q) -
      (ContinuousLinearMap.mul ℂ 𝔼).flip (b65q_S p O.residue θ q))
    (fun θ hθ ↦ by simpa using b65q_aeval_deriv O q hθ f) ?_ h0' θ hθ]
  · simp [b65q_mat]
  · exact ((ContinuousLinearMap.mul ℂ 𝔼).continuous.comp_continuousOn (b65q_S_continuousOn O q)).sub
      ((ContinuousLinearMap.mul ℂ 𝔼).flip.continuous.comp_continuousOn (b65q_S_continuousOn O q))

/-- The trace of the matrix of an operator, as a continuous linear functional. -/
def b65q_traceCLM : 𝔼 →L[ℂ] ℂ := ∑ i : Fin 4, b65q_entryCLM i i

theorem b65q_traceCLM_apply (T : 𝔼) : b65q_traceCLM T = Matrix.trace (b65q_mat T) := by
  simp [b65q_traceCLM, b65q_entryCLM_apply, Matrix.trace]

/-- **The traces of the residues are constant along the flow.** -/
theorem b65q_trace_flow {p : Fin 12 → ℂ} (O : b65p_Outputs p) (q : Fin 4 ⊕ Fin 12) :
    ∀ θ ∈ ball (0 : ℂ) O.radius,
      Matrix.trace (b65q_res O.residue θ q) = Matrix.trace (b65q_res O.residue 0 q) := by
  intro θ hθ
  have := b65q_linear_flow_zero
    (fun θ ↦ b65q_traceCLM (O.residue θ q) - b65q_traceCLM (O.residue 0 q)) (fun _ ↦ 0)
    (fun θ hθ ↦ by
      have h := (b65q_traceCLM.hasFDerivAt.comp_hasDerivAt θ (O.schlesinger θ hθ q)).sub_const
        (b65q_traceCLM (O.residue 0 q))
      have hz : b65q_traceCLM (b65q_S p O.residue θ q * O.residue θ q -
          O.residue θ q * b65q_S p O.residue θ q) = 0 := by
        rw [map_sub, b65q_traceCLM_apply, b65q_traceCLM_apply, ← b65q_matAlg_apply,
          ← b65q_matAlg_apply, map_mul, map_mul, Matrix.trace_mul_comm, sub_self]
      rw [b65q_field_eq, hz] at h
      simpa using h)
    continuousOn_const (by simp) θ hθ
  rw [sub_eq_zero, b65q_traceCLM_apply, b65q_traceCLM_apply] at this
  exact this

end HodgeLean.Foundations.Program
