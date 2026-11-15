import HodgeLean.Foundations.Program.PeriodBasisAlignmentDefs

/-! Open bodies for ordered-product transport and the constructed-marking comparison. -/
noncomputable section
open Set Filter Topology Manifold
open scoped TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local instance] Classical.propDecidable
attribute [local instance] rf8_SharedFamily.topC rf8_SharedFamily.chartC
  rf8_SharedFamily.manC rf8_SharedFamily.t2C rf8_SharedFamily.compactC
  rf8_SharedFamily.connectedC rf8_SharedFamily.actionC rf8_SharedFamily.totalChart
  rf8_SharedFamily.totalMan rf8_SharedFamily.fibreChart rf8_SharedFamily.fibreMan
  rf8_SharedFamily.fibreT2 rf8_SharedFamily.fibreCompact rf8_SharedFamily.fibreConnected
  rf8_SharedFamily.fibreFaithful

theorem b66e_productChange_unit_aux (P R : Matrix (Fin 3) (Fin 3) ℂ)
    (hP : IsUnit P) (hR : IsUnit R) :
    IsUnit (b66e_productChange P R) := by
  have hK : b66e_productChange P R =
      (Matrix.kroneckerMap (· * ·) P.transpose R.transpose).submatrix
        (finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm
        (finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm := by
    ext u w
    simp [b66e_productChange, Matrix.kroneckerMap_apply]
  rw [hK, Matrix.isUnit_iff_isUnit_det, Matrix.det_submatrix_equiv_self,
    Matrix.det_kronecker, Matrix.det_transpose, Matrix.det_transpose]
  rw [Matrix.isUnit_iff_isUnit_det] at hP hR
  exact (hP.pow _).mul (hR.pow _)

theorem b66e_productChange_analytic_aux (P R : ℂ → Matrix (Fin 3) (Fin 3) ℂ)
    (hP : ∀ i j, AnalyticAt ℂ (fun θ => P θ i j) 0)
    (hR : ∀ i j, AnalyticAt ℂ (fun θ => R θ i j) 0)
    (huP : IsUnit (P 0)) (huR : IsUnit (R 0)) :
    (∀ i j, AnalyticAt ℂ (fun θ => b66e_productChange (P θ) (R θ) i j) 0) ∧
    ∀ᶠ θ in 𝓝 (0 : ℂ), IsUnit (P θ) ∧ IsUnit (R θ) ∧
      IsUnit (b66e_productChange (P θ) (R θ)) := by
  refine ⟨fun u w => (hP _ _).mul (hR _ _), ?_⟩
  have hunit : ∀ M : ℂ → Matrix (Fin 3) (Fin 3) ℂ,
      (∀ i j, AnalyticAt ℂ (fun θ => M θ i j) 0) → IsUnit (M 0) →
        ∀ᶠ θ in 𝓝 (0 : ℂ), IsUnit (M θ) := by
    intro M hM hu
    have hc : ContinuousAt M 0 :=
      continuousAt_pi.2 fun i => continuousAt_pi.2 fun j => (hM i j).continuousAt
    have hdet : ContinuousAt (fun θ => (M θ).det) 0 :=
      (continuous_id.matrix_det).continuousAt.comp hc
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] at hu
    filter_upwards [hdet.eventually_ne hu] with θ hθ
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    exact hθ
  filter_upwards [hunit P hP huP, hunit R hR huR] with θ h1 h2
  exact ⟨h1, h2, b66e_productChange_unit_aux _ _ h1 h2⟩

/-- Coefficients of holomorphic differentials are holomorphic in every retained chart. -/
theorem b66e_forms_analytic (D : rf8_SharedFamily) (t : b6t_polydisc mr_base) (m : ℕ)
    (Q : b66g_Coeff D) (hQ : Q ∈ b66g_forms D t m) (a : b66k_Index D) :
    AnalyticOnNhd ℂ (fun z => Q a ((D.atlas.A a).symm (t.val, z)).2)
      (b66k_domain D t a) := by
  induction hQ using Submodule.span_induction with
  | mem Q hQ => exact hQ.1 a
  | zero => exact analyticOnNhd_const
  | add Q Q' _ _ h h' => exact h.add h'
  | smul c Q _ h => exact fun z hz => analyticAt_const.mul (h z hz)

/-- The centre of a retained chart lies in its fibre-coordinate domain. -/
theorem b66e_centre_mem (D : rf8_SharedFamily) (t : b6t_polydisc mr_base) (x : D.C) :
    (D.atlas.A (t, x) (t, x)).2 ∈ b66k_domain D t (t, x) := by
  have hs := (D.atlas.hA (t, x)).1
  have hp := D.atlas.hparam (t, x) (t, x) hs
  have hm := (D.atlas.A (t, x)).map_source hs
  change (t.val, (D.atlas.A (t, x) (t, x)).2) ∈ (D.atlas.A (t, x)).target
  rw [← hp]
  exact hm

/-- The residue sum is linear on holomorphic quadratic coefficients for a meromorphic splitting. -/
theorem b66e_residueSum_sum (D : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (S : Finset D.C) (v : b66k_Index D → ℂ → ℂ)
    (hmero : ∀ a z, z ∈ b66k_domain D t a → MeromorphicAt (v a) z)
    {ι : Type*} (s : Finset ι) (c : ι → ℂ) (Q : ι → b66g_Coeff D)
    (hQ : ∀ k, Q k ∈ b66g_forms D t 2) :
    b66g_residueSum D t S v (∑ k ∈ s, c k • Q k) =
      ∑ k ∈ s, c k * b66g_residueSum D t S v (Q k) := by
  unfold b66g_residueSum
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hz := b66e_centre_mem D t x
  have hfun : (fun z => v (t, x) z *
      (∑ k ∈ s, c k • Q k) (t, x) ((D.atlas.A (t, x)).symm (t.val, z)).2) =
      ∑ k ∈ s, fun z => c k * (v (t, x) z *
        Q k (t, x) ((D.atlas.A (t, x)).symm (t.val, z)).2) := by
    funext z
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hfun, TauCeti.Contour.residue_sum]
  · simp only [TauCeti.Contour.residue_const_mul]
  · intro k _
    exact analyticAt_const.meromorphicAt.mul
      ((hmero _ _ hz).mul (b66e_forms_analytic D t 2 (Q k) (hQ k) _ _ hz).meromorphicAt)

theorem b66e_multiplication_transport_aux (D : rf8_SharedFamily) (t : b6t_polydisc mr_base)
    (q r : Fin 3 → b66g_primitiveForms D t)
    (P R : Matrix (Fin 3) (Fin 3) ℂ)
    (S : Fin 10 → Finset D.C) (v : Fin 10 → b66k_Index D → ℂ → ℂ)
    (hmero : ∀ j a z, z ∈ b66k_domain D t a → MeromorphicAt (v j a) z) :
    b66m_multiplicationMatrix D t (b66e_reframe D t q P)
      (b66e_reframe D t r R) S v =
        b66e_productChange P R * b66m_multiplicationMatrix D t q r S v := by
  have hmul : ∀ i j, b66m_multiply D t (b66e_reframe D t q P i) (b66e_reframe D t r R j) =
      ∑ ab : Fin 3 × Fin 3, (P ab.1 i * R ab.2 j) • b66m_multiply D t (q ab.1) (r ab.2) := by
    intro i j
    have hprod : b66g_product D (b66e_reframe D t q P i).val (b66e_reframe D t r R j).val =
        ∑ ab : Fin 3 × Fin 3, (P ab.1 i * R ab.2 j) •
          b66g_product D (q ab.1).val (r ab.2).val := by
      funext a x
      simp only [b66e_reframe, b66g_product, Submodule.coe_sum, Submodule.coe_smul,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fintype.sum_prod_type,
        Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun b' _ => ?_
      ring
    simp only [b66m_multiply, hprod, map_sum, map_smul]
  ext u j
  rw [Matrix.mul_apply]
  simp only [b66m_multiplicationMatrix, hmul]
  have h := b66e_residueSum_sum D t (S j) (v j) (hmero j) Finset.univ
    (fun ab : Fin 3 × Fin 3 => P ab.1 ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm u).1 *
      R ab.2 ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm u).2)
    (fun ab => b66m_multiply D t (q ab.1) (r ab.2))
    (fun ab => (b66m_symmetric_product D t (q ab.1) (r ab.2)).2.1)
  rw [h]
  rw [← (finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).sum_comp]
  refine Fintype.sum_congr _ _ fun ab => ?_
  simp only [b66e_productChange, Equiv.symm_apply_apply]

theorem b66e_marked_codiff_aux (D : rf8_SharedFamily)
    (u₀ : D.atlas.π ⁻¹' {b63gP_basePoint})
    (hroot : ∀ i, D.atlas.hπ.fundamentalGroupToMulOpposite u₀ (b63gP_loops i) =
      MulOpposite.op (b4b_root i))
    (curve : ℂ → Fin 10 → ℂ) (hcurve : ContinuousAt curve 0)
    (hzero : curve 0 ∈ b6t_polydisc mr_base) :
    ∃ (q r : (t : b6t_polydisc mr_base) → Fin 3 → b66g_primitiveForms D t)
      (S : (t : b6t_polydisc mr_base) → Fin 10 → Finset D.C)
      (v : (t : b6t_polydisc mr_base) → Fin 10 → b66k_Index D → ℂ → ℂ),
      (∀ t, LinearIndependent ℂ
        (fun ij : Fin 2 × Fin 3 => if ij.1 = 0 then q t ij.2 else r t ij.2)) ∧
      (∀ t j a z, z ∈ b66k_domain D t a → MeromorphicAt (v t j a) z) ∧
      (∀ t j a z, z ∈ b66k_domain D t a →
        ((D.atlas.A a).symm (t.val, z)).2 ∉ S t j → AnalyticAt ℂ (v t j a) z) ∧
      (∀ t j a b x, x ∉ S t j → (t, x) ∈ (D.atlas.A a).source →
        (t, x) ∈ (D.atlas.A b).source →
        b66k_cocycle D t (Pi.single j 1) a b x = b66k_boundary D t (v t j) a b x) ∧
      (∀ᶠ θ in 𝓝 (0 : ℂ), ∃ L : Matrix (Fin 9) (Fin 9) ℂ,
        ∃ T : Matrix (Fin 10) (Fin 10) ℂ, IsUnit L ∧ IsUnit T ∧
          b66m_jet D q r S v curve θ = L * LinearMap.toMatrix'
            (fderiv ℂ (b64i_period D b63gP_s₀
              (b63gW_marking D u₀ hroot)) (curve θ) :
                (Fin 10 → ℂ) →ₗ[ℂ] Fin 9 → ℂ) * T) ∧
      (∀ᶠ θ in 𝓝 (0 : ℂ), ∃ κ : ℂ,
        (κ = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ ∨
          κ = -(2 * (Real.pi : ℂ) * Complex.I)⁻¹) ∧
        IsUnit (b66m_leftMatrix (b64i_period D b63gP_s₀
          (b63gW_marking D u₀ hroot) (curve θ)) κ) ∧
        b66m_jet D q r S v curve θ =
          b66m_leftMatrix (b64i_period D b63gP_s₀
            (b63gW_marking D u₀ hroot) (curve θ)) κ *
          LinearMap.toMatrix' (fderiv ℂ (b64i_period D b63gP_s₀
            (b63gW_marking D u₀ hroot)) (curve θ) :
              (Fin 10 → ℂ) →ₗ[ℂ] Fin 9 → ℂ) * (1 : Matrix (Fin 10) (Fin 10) ℂ)) := by
  obtain ⟨q, r, S, v, hind, hmero, hreg, hv, hev⟩ :=
    b66m_jet_codiff D b63gP_s₀ (b63gW_marking D u₀ hroot)
      (b63gW_marking_hJ D u₀ hroot) (b63gW_marking_hpair D u₀ hroot)
      curve hcurve hzero
  refine ⟨q, r, S, v, hind, hmero, hreg, hv, ?_, ?_⟩
  · filter_upwards [hev] with θ hθ
    obtain ⟨L, T, hL, hT, -, -, heq⟩ := hθ
    exact ⟨L, T, hL, hT, heq⟩
  · filter_upwards [hev] with θ hθ
    obtain ⟨L, T, hL, -, ⟨κ, hκ, hLκ⟩, hT1, heq⟩ := hθ
    subst hLκ hT1
    exact ⟨κ, hκ, hL, heq⟩

end HodgeLean.Foundations.Program
