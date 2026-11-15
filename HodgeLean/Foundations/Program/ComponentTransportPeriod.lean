import HodgeLean.Foundations.Program.ComponentTransportDefs
import HodgeLean.Foundations.Program.PeriodMarkingHermitianTransport
noncomputable section
open Set Manifold Filter Topology HodgeLean.Papers
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint HodgeLean.RealDefs
open HodgeLean.Foundations HodgeLean.Foundations.Symplectic HodgeLean.Adapters TopologicalSpace
open scoped ContDiff TensorProduct
namespace HodgeLean.Foundations.Program
set_option backward.isDefEq.respectTransparency false
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.totalChart
  b65z_SharedFamily.totalMan b65z_SharedFamily.fibreChart b65z_SharedFamily.fibreMan
  b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact b65z_SharedFamily.fibreConnected
  b65z_SharedFamily.fibreFaithful


attribute [local instance] rf8_SharedFamily.topC rf8_SharedFamily.chartC
  rf8_SharedFamily.manC rf8_SharedFamily.t2C rf8_SharedFamily.compactC
  rf8_SharedFamily.connectedC rf8_SharedFamily.actionC rf8_SharedFamily.totalChart
  rf8_SharedFamily.totalMan rf8_SharedFamily.fibreChart rf8_SharedFamily.fibreMan
  rf8_SharedFamily.fibreT2 rf8_SharedFamily.fibreCompact rf8_SharedFamily.fibreConnected
  rf8_SharedFamily.fibreFaithful


set_option maxHeartbeats 400000 in
theorem b65y_complexMarking_trans (M : Type*) [AddCommGroup M]
    (m : (ℚ ⊗[ℤ] M) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (u : (ℚ ⊗[ℤ] b60_Lattice) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice)) :
    b64b_complexMarking M (m.trans u) =
      (b64b_complexMarking M m).trans (b64b_complexMarking b60_Lattice u) := by
  simp only [b64b_complexMarking, LinearEquiv.baseChange_trans]
  ext x
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]

def b65y_domain_action (u : (ℚ ⊗[ℤ] b60_Lattice) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (z : Fin 9 → ℂ) : Fin 9 → ℂ :=
  b64_coordOf ((b60_F z).map (b64b_complexMarking b60_Lattice u).toLinearMap)

set_option maxHeartbeats 400000 in
theorem b65y_domain_action_chart
    (u : (ℚ ⊗[ℤ] b60_Lattice) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hA : ∀ x, u (b60_omega.baseChange ℚ x) = b60_omega.baseChange ℚ (u x))
    (hE : ∀ x y, b60_E.baseChange ℚ (u x) (u y) = b60_E.baseChange ℚ x y)
    (z : Fin 9 → ℂ) (hz : z ∈ g32m_Domain) :
    b65y_domain_action u z ∈ g32m_Domain ∧
      b60_F (b65y_domain_action u z) =
        (b60_F z).map (b64b_complexMarking b60_Lattice u).toLinearMap := by
  have hdim : Module.finrank ℂ (b60_F z) = 6 := by
    rw [b60_F, finrank_span_eq_card (b60_frame_independent z)]
    rfl
  obtain ⟨hR, hd, hn, hp⟩ := b64b_marking_riemann b60_Lattice b60_E b60_omega u hA hE
    (b60_F z) ((b60_riemann_iff z).2 hz) hdim
    (b60_weil_dimensions z).2 (b60_weil_dimensions z).1
  obtain ⟨τ, hτ⟩ := b60c_fixed_filtration_chart _ hd hn hp hR
  have hc : b65y_domain_action u z = τ := by
    unfold b65y_domain_action
    rw [hτ, b64_coordOf_eq]
  exact ⟨hc ▸ τ.property, by rw [hc]; exact hτ.symm⟩

set_option maxHeartbeats 400000 in
theorem b65y_domain_action_analytic
    (u : (ℚ ⊗[ℤ] b60_Lattice) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hA : ∀ x, u (b60_omega.baseChange ℚ x) = b60_omega.baseChange ℚ (u x))
    (hE : ∀ x y, b60_E.baseChange ℚ (u x) (u y) = b60_E.baseChange ℚ x y) :
    AnalyticOnNhd ℂ (b65y_domain_action u) g32m_Domain := by
  apply b64_coordOf_analyticOnNhd
    (fun z k ↦ b64b_complexMarking b60_Lattice u (b60_frame z k)) _ _ g32m_Domain.isOpen
  · intro k p
    rcases k with ⟨a, i⟩
    fin_cases a <;>
      simp only [b60_frame, Fin.zero_eta, Fin.mk_one, Fin.isValue, ite_true, ite_false,
        one_ne_zero, map_add, map_sum, map_smul, Finsupp.add_apply,
        Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
    all_goals
      apply AnalyticOnNhd.add analyticOnNhd_const
      apply Finset.analyticOnNhd_fun_sum
      intro j _
      apply AnalyticOnNhd.mul _ analyticOnNhd_const
      first
      | exact fun t _ ↦ (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 9 ↦ ℂ)
          (finProdFinEquiv (j, i))).analyticAt t
      | exact fun t _ ↦ (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 9 ↦ ℂ)
          (finProdFinEquiv (i, j))).analyticAt t
  · intro z hz
    rw [b60_F, Submodule.map_span, ← Set.range_comp]
    rfl
  · intro z hz
    exact ⟨_, (b65y_domain_action_chart u hA hE z hz).2.symm⟩

theorem b65y_unitary_inverse_action
    (u : (ℚ ⊗[ℤ] b60_Lattice) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hA : ∀ x, u (b60_omega.baseChange ℚ x) = b60_omega.baseChange ℚ (u x))
    (hE : ∀ x y, b60_E.baseChange ℚ (u x) (u y) = b60_E.baseChange ℚ x y) :
    (∀ x, u.symm (b60_omega.baseChange ℚ x) = b60_omega.baseChange ℚ (u.symm x)) ∧
    ∀ x y, b60_E.baseChange ℚ (u.symm x) (u.symm y) = b60_E.baseChange ℚ x y := by
  constructor
  · intro x
    apply u.injective
    rw [u.apply_symm_apply, hA, u.apply_symm_apply]
  · intro x y
    simpa only [u.apply_symm_apply] using (hE (u.symm x) (u.symm y)).symm

set_option maxHeartbeats 400000 in
theorem b65y_domain_action_inverse
    (u : (ℚ ⊗[ℤ] b60_Lattice) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hA : ∀ x, u (b60_omega.baseChange ℚ x) = b60_omega.baseChange ℚ (u x))
    (hE : ∀ x y, b60_E.baseChange ℚ (u x) (u y) = b60_E.baseChange ℚ x y)
    (z : Fin 9 → ℂ) (hz : z ∈ g32m_Domain) :
    b65y_domain_action u.symm (b65y_domain_action u z) = z := by
  obtain ⟨hiA, hiE⟩ := b65y_unitary_inverse_action u hA hE
  apply b60_F_injective
  rw [(b65y_domain_action_chart u.symm hiA hiE _
    (b65y_domain_action_chart u hA hE z hz).1).2,
    (b65y_domain_action_chart u hA hE z hz).2, ← Submodule.map_comp]
  have hc : (b64b_complexMarking b60_Lattice u.symm).toLinearMap ∘ₗ
      (b64b_complexMarking b60_Lattice u).toLinearMap = LinearMap.id := by
    ext x
    simp [b64b_complexMarking, LinearEquiv.baseChange_symm]
  rw [hc, Submodule.map_id]

set_option maxHeartbeats 400000 in
theorem b65y_derivative_unit_of_inverse
    (Φ Ψ : (Fin 9 → ℂ) → Fin 9 → ℂ)
    (hΦ : AnalyticOnNhd ℂ Φ g32m_Domain) (hΨ : AnalyticOnNhd ℂ Ψ g32m_Domain)
    (hm : MapsTo Φ g32m_Domain g32m_Domain)
    (hi : ∀ z ∈ g32m_Domain, Ψ (Φ z) = z)
    (z : Fin 9 → ℂ) (hz : z ∈ g32m_Domain) : IsUnit (fderiv ℂ Φ z) := by
  have heq : (Ψ ∘ Φ) =ᶠ[𝓝 z] id := by
    filter_upwards [g32m_Domain.isOpen.mem_nhds hz] with w hw
    exact hi w hw
  have hc : (fderiv ℂ Ψ (Φ z)).comp (fderiv ℂ Φ z) = ContinuousLinearMap.id ℂ _ := by
    rw [← fderiv_comp z (hΨ _ (hm hz)).differentiableAt (hΦ z hz).differentiableAt,
      heq.fderiv_eq, fderiv_id]
  have hinj : Function.Injective (fderiv ℂ Φ z) := by
    intro x y hxy
    have h := congrArg (fderiv ℂ Ψ (Φ z)) hxy
    have he (v) : fderiv ℂ Ψ (Φ z) (fderiv ℂ Φ z v) = v :=
      congrArg (fun L ↦ L v) hc
    rwa [he, he] at h
  exact ContinuousLinearMap.isUnit_iff_bijective.mpr
    ⟨hinj, LinearMap.surjective_of_injective (f := (fderiv ℂ Φ z).toLinearMap) hinj⟩

end HodgeLean.Foundations.Program
