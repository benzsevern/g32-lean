import HodgeLean.Foundations.Program.ComponentTransportGeometry
import HodgeLean.Foundations.Program.ComponentTransportPolarization
import HodgeLean.Foundations.Program.ComponentTransportPeriod
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
theorem b65y_component_transport_aux (H : b65y_HurwitzChain) :
    ∃ e : b65y_lattice (H.chart 0) ≃ₗ[ℤ] b65y_lattice (H.chart (Fin.last H.n)),
      (∀ x, e ((H.chart 0).2.2.A (b65z_s₀ (H.chart 0).1) x) =
        (H.chart (Fin.last H.n)).2.2.A (b65z_s₀ (H.chart (Fin.last H.n)).1) (e x)) ∧
      ∀ x y, b65y_pairing (H.chart (Fin.last H.n)) (e x) (e y) =
        b65y_pairing (H.chart 0) x y := by
  have hi : ∀ i : Fin (H.n + 1),
      ∃ e : b65y_lattice (H.chart 0) ≃ₗ[ℤ] b65y_lattice (H.chart i),
        (∀ x, e ((H.chart 0).2.2.A (b65z_s₀ (H.chart 0).1) x) =
          (H.chart i).2.2.A (b65z_s₀ (H.chart i).1) (e x)) ∧
        ∀ x y, b65y_pairing (H.chart i) (e x) (e y) = b65y_pairing (H.chart 0) x y := by
    intro i
    induction i using Fin.induction with
    | zero => exact ⟨LinearEquiv.refl ℤ _, fun _ ↦ rfl, fun _ _ ↦ rfl⟩
    | succ i ih =>
      obtain ⟨a, ha, hEa⟩ := ih
      obtain ⟨b, hb, hEb⟩ := b65y_edge_transport H i
      refine ⟨a.trans b, ?_, ?_⟩
      · intro x
        simp only [LinearEquiv.trans_apply]
        rw [ha, hb]
      · intro x y
        exact (hEb _ _).trans (hEa x y)
  exact hi (Fin.last H.n)

set_option maxHeartbeats 400000 in
theorem b65y_change_marking_aux (c : Fin 10 → ℂ) (g : Fin 13 → b4b_Group)
    (hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g i))) (D : b65z_SharedFamily c g)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Subset.refl _) (b65z_s₀ c)) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ y, m ((D.A (b65z_s₀ c)).baseChange ℚ y) = b60_omega.baseChange ℚ (m y))
    (hpair : ∀ y z, b60_E.baseChange ℚ (m y) (m z) =
      (b63e_singularQ c D.C D.hC (b6t_polydisc c) (Subset.refl _) (b65z_s₀ c)
        (D.P (b65z_s₀ c)) (D.Q (b65z_s₀ c))).baseChange ℚ y z)
    (m' : (ℚ ⊗[ℤ] b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Subset.refl _) (b65z_s₀ c)) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ' : ∀ y, m' ((D.A (b65z_s₀ c)).baseChange ℚ y) = b60_omega.baseChange ℚ (m' y))
    (hpair' : ∀ y z, b60_E.baseChange ℚ (m' y) (m' z) =
      (b63e_singularQ c D.C D.hC (b6t_polydisc c) (Subset.refl _) (b65z_s₀ c)
        (D.P (b65z_s₀ c)) (D.Q (b65z_s₀ c))).baseChange ℚ y z) :
    ∃ Φ : (Fin 9 → ℂ) → (Fin 9 → ℂ),
    ∃ Ψ : (Fin 9 → ℂ) → (Fin 9 → ℂ),
      AnalyticOnNhd ℂ Φ g32m_Domain ∧ AnalyticOnNhd ℂ Ψ g32m_Domain ∧
      MapsTo Φ g32m_Domain g32m_Domain ∧ MapsTo Ψ g32m_Domain g32m_Domain ∧
      (∀ z ∈ g32m_Domain, Ψ (Φ z) = z ∧ Φ (Ψ z) = z) ∧
      (∀ z ∈ g32m_Domain, IsUnit (fderiv ℂ Φ z)) ∧
      ∀ t ∈ b6t_polydisc c,
        b65z_period D (b65z_s₀ c) m' t = Φ (b65z_period D (b65z_s₀ c) m t) ∧
        fderiv ℂ (b65z_period D (b65z_s₀ c) m') t =
          (fderiv ℂ Φ (b65z_period D (b65z_s₀ c) m t)).comp
            (fderiv ℂ (b65z_period D (b65z_s₀ c) m) t) := by
  let u := m.symm.trans m'
  have huA : ∀ x, u (b60_omega.baseChange ℚ x) = b60_omega.baseChange ℚ (u x) := by
    intro x
    change m' (m.symm (b60_omega.baseChange ℚ x)) = b60_omega.baseChange ℚ (m' (m.symm x))
    have hi : m.symm (b60_omega.baseChange ℚ x) = (D.A (b65z_s₀ c)).baseChange ℚ (m.symm x) := by
      apply m.injective
      rw [m.apply_symm_apply, hJ, m.apply_symm_apply]
    rw [hi, hJ']
  have huE : ∀ x y, b60_E.baseChange ℚ (u x) (u y) = b60_E.baseChange ℚ x y := by
    intro x y
    exact (hpair' (m.symm x) (m.symm y)).trans
      ((hpair (m.symm x) (m.symm y)).symm.trans (by rw [m.apply_symm_apply, m.apply_symm_apply]))
  obtain ⟨hiA, hiE⟩ := b65y_unitary_inverse_action u huA huE
  have hΦ := b65y_domain_action_analytic u huA huE
  have hΨ := b65y_domain_action_analytic u.symm hiA hiE
  have hm : MapsTo (b65y_domain_action u) g32m_Domain g32m_Domain :=
    fun z hz ↦ (b65y_domain_action_chart u huA huE z hz).1
  have hmi : MapsTo (b65y_domain_action u.symm) g32m_Domain g32m_Domain :=
    fun z hz ↦ (b65y_domain_action_chart u.symm hiA hiE z hz).1
  have hperiod : ∀ t ∈ b6t_polydisc c,
      b65z_period D (b65z_s₀ c) m' t =
        b65y_domain_action u (b65z_period D (b65z_s₀ c) m t) := by
    intro t ht
    have hchart := b65z_period_chart hg D (b65z_s₀ c) m hJ hpair t ht
    apply b60_F_injective
    dsimp only [b65z_period]
    rw [(b65z_period_chart hg D (b65z_s₀ c) m' hJ' hpair' t ht).2,
      (b65y_domain_action_chart u huA huE _ hchart.1).2, hchart.2]
    unfold b64c_markedF
    rw [← Submodule.map_comp]
    change _ = (b65z_transportedFamily D (b65z_s₀ c) t).map
      (((b64b_complexMarking _ m).trans (b64b_complexMarking _ u)).toLinearMap)
    rw [← b65y_complexMarking_trans]
    have hmu : m.trans u = m' := by
      ext y
      exact congrArg m' (m.symm_apply_apply y)
    rw [hmu]
    rfl
  refine ⟨b65y_domain_action u, b65y_domain_action u.symm, hΦ, hΨ, hm, hmi, ?_, ?_, ?_⟩
  · intro z hz
    exact ⟨b65y_domain_action_inverse u huA huE z hz,
      by simpa only [LinearEquiv.symm_symm] using b65y_domain_action_inverse u.symm hiA hiE z hz⟩
  · exact b65y_derivative_unit_of_inverse _ _ hΦ hΨ hm
      (b65y_domain_action_inverse u huA huE)
  · intro t ht
    refine ⟨hperiod t ht, ?_⟩
    have heq : b65z_period D (b65z_s₀ c) m' =ᶠ[𝓝 t]
        (b65y_domain_action u) ∘ b65z_period D (b65z_s₀ c) m := by
      filter_upwards [(b65z_polydisc_open c).mem_nhds ht] with w hw
      exact hperiod w hw
    rw [heq.fderiv_eq]
    exact fderiv_comp t
      (hΦ _ (b65z_period_chart hg D (b65z_s₀ c) m hJ hpair t ht).1).differentiableAt
      (b65z_period_analytic hg D (b65z_s₀ c) m hJ hpair t ht).differentiableAt

end HodgeLean.Foundations.Program
