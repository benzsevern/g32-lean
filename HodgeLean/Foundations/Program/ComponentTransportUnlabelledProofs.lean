import HodgeLean.Foundations.Program.ComponentTransport
import HodgeLean.Foundations.Program.ComponentTransportUnlabelledDefs
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
theorem b65y_edge_transport_u (H : b65y_UnlabelledHurwitzChain) (i : Fin H.n) :
    ∃ f : b65y_lattice (H.chart i.castSucc) ≃ₗ[ℤ] b65y_lattice (H.chart i.succ),
      (∀ x, f ((H.chart i.castSucc).2.2.A (b65z_s₀ (H.chart i.castSucc).1) x) =
        (H.chart i.succ).2.2.A (b65z_s₀ (H.chart i.succ).1) (f x)) ∧
      ∀ x y, b65y_pairing (H.chart i.succ) (f x) (f y) =
        b65y_pairing (H.chart i.castSucc) x y := by
  obtain ⟨a, ha, hEa⟩ := b65y_chart_transport (H.chart i.castSucc).2.2
    (b65z_s₀ (H.chart i.castSucc).1) (H.overlap i).1
  obtain ⟨b, hb, hEb⟩ := b65y_overlap_transport (H.chart i.castSucc).2.2
    (H.chart i.succ).2.2 (H.overlap i).1 (H.overlap i).2 (H.glue i) (H.hol i) (H.inv_hol i)
    (H.equivariant i)
  obtain ⟨d, hd, hEd⟩ := b65y_chart_transport (H.chart i.succ).2.2 (H.overlap i).2
    (b65z_s₀ (H.chart i.succ).1)
  refine ⟨(a.trans b).trans d, ?_, ?_⟩
  · intro x
    simp only [LinearEquiv.trans_apply]
    rw [ha, hb, hd]
  · intro x y
    simp only [LinearEquiv.trans_apply]
    exact (hEd _ _).trans ((hEb _ _).trans (hEa x y))

set_option maxHeartbeats 400000 in
theorem b65y_component_transport_u_aux (H : b65y_UnlabelledHurwitzChain) :
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
      obtain ⟨b, hb, hEb⟩ := b65y_edge_transport_u H i
      refine ⟨a.trans b, ?_, ?_⟩
      · intro x
        simp only [LinearEquiv.trans_apply]
        rw [ha, hb]
      · intro x y
        exact (hEb _ _).trans (hEa x y)
  exact hi (Fin.last H.n)

set_option maxHeartbeats 400000 in
/-- Rational extension followed by the retained reference marking preserves the original
pairing, for any unlabelled chain between the retained reference chart and the chart at the
centre.
Source: `b65y_component_transport_u_aux`; b63gW_marking_hJ, b63gW_marking_hpair (F-2248). -/
theorem b65y_rational_composition_of_chain_u (p : Fin 12 → ℂ)
    (g : Fin 13 → b4b_Group) (D : b65z_SharedFamily (b65z_centre p) g)
    (R : rf8_SharedFamily) (v₀ : R.atlas.π ⁻¹' {b63gP_basePoint})
    (hroot : ∀ i, R.atlas.hπ.fundamentalGroupToMulOpposite v₀ (b63gP_loops i) =
      MulOpposite.op (b4b_root i))
    (H : b65y_UnlabelledHurwitzChain)
    (hH : H.chart 0 = (⟨mr_base, b4b_root, b65z_ofRetained R⟩ : b65y_Chart) ∧
      H.chart (Fin.last H.n) = (⟨b65z_centre p, g, D⟩ : b65y_Chart)) :
    ∃ e : b65y_lattice (⟨b65z_centre p, g, D⟩ : b65y_Chart) ≃ₗ[ℤ] b65y_lattice (⟨mr_base, b4b_root, b65z_ofRetained R⟩ : b65y_Chart),
      (∀ x, e (D.A (b65z_s₀ (b65z_centre p)) x) = R.A b63gP_s₀ (e x)) ∧
      (∀ x y, b65y_pairing (⟨mr_base, b4b_root, b65z_ofRetained R⟩ : b65y_Chart) (e x) (e y) = b65y_pairing (⟨b65z_centre p, g, D⟩ : b65y_Chart) x y) ∧
      ∀ x y, b60_E.baseChange ℚ
        (b63gW_marking R v₀ hroot (e.baseChange ℤ ℚ _ _ x))
        (b63gW_marking R v₀ hroot (e.baseChange ℤ ℚ _ _ y)) =
        (b65y_pairing (⟨b65z_centre p, g, D⟩ : b65y_Chart)).baseChange ℚ x y := by
  obtain ⟨h₀, h₁⟩ := hH
  have h := b65y_component_transport_u_aux H
  rw [h₀, h₁] at h
  dsimp only [b65y_lattice, b65y_pairing, b65z_ofRetained] at h
  obtain ⟨f, hfA, hfE⟩ := h
  dsimp only [b65y_lattice, b65y_pairing, b65z_ofRetained]
  change ∀ x, f (R.A b63gP_s₀ x) = D.A (b65z_s₀ (b65z_centre p)) (f x) at hfA
  refine ⟨f.symm, ?_, ?_, ?_⟩
  · intro x
    apply f.injective
    rw [LinearEquiv.apply_symm_apply]
    simpa only [LinearEquiv.apply_symm_apply] using (hfA (f.symm x)).symm
  · intro x y
    simpa only [LinearEquiv.apply_symm_apply] using (hfE (f.symm x) (f.symm y)).symm
  · intro x y
    rw [b63gW_marking_hpair]
    apply b64b_integral_pairing_transport _ _ f.symm
    intro u v
    have h := (hfE (f.symm u) (f.symm v)).symm
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h
    exact h

example := @b65y_rational_composition_of_chain_u

set_option maxHeartbeats 400000 in
/-- The G32-centre marking supplier, for any unlabelled chain from the retained reference
chart to the chart at the centre.
Source: G32 v0.16, Lemma 3.4 and Proposition 6.3; `b65y_rational_composition_of_chain_u`;
b63gW_marking, b63gW_marking_hJ. -/
theorem b65y_marking_of_chain_u (p : Fin 12 → ℂ)
    (g : Fin 13 → b4b_Group) (D : b65z_SharedFamily (b65z_centre p) g)
    (R : rf8_SharedFamily) (v₀ : R.atlas.π ⁻¹' {b63gP_basePoint})
    (hroot : ∀ i, R.atlas.hπ.fundamentalGroupToMulOpposite v₀ (b63gP_loops i) =
      MulOpposite.op (b4b_root i))
    (H : b65y_UnlabelledHurwitzChain)
    (hH : H.chart 0 = (⟨mr_base, b4b_root, b65z_ofRetained R⟩ : b65y_Chart) ∧
      H.chart (Fin.last H.n) = (⟨b65z_centre p, g, D⟩ : b65y_Chart)) :
    ∃ m : (ℚ ⊗[ℤ] b63l_parameterLattice (b65z_centre p) D.C D.hC (b6t_polydisc (b65z_centre p)) (Subset.refl _) (b65z_s₀ (b65z_centre p))) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice),
      (∀ y, m ((D.A (b65z_s₀ (b65z_centre p))).baseChange ℚ y) = b60_omega.baseChange ℚ (m y)) ∧
      ∀ y z, b60_E.baseChange ℚ (m y) (m z) =
        (b63e_singularQ (b65z_centre p) D.C D.hC (b6t_polydisc (b65z_centre p)) (Subset.refl _)
          (b65z_s₀ (b65z_centre p)) (D.P (b65z_s₀ (b65z_centre p)))
          (D.Q (b65z_s₀ (b65z_centre p)))).baseChange ℚ y z := by
  obtain ⟨f, hfA, -, hfE⟩ :=
    b65y_rational_composition_of_chain_u p g D R v₀ hroot H hH
  refine ⟨(f.baseChange ℤ ℚ _ _).trans (b63gW_marking R v₀ hroot), ?_, hfE⟩
  intro y
  change b63gW_marking R v₀ hroot (f.toLinearMap.baseChange ℚ ((D.A _).baseChange ℚ y)) = _
  have hc : f.toLinearMap.baseChange ℚ ∘ₗ (D.A _).baseChange ℚ =
      ((R.A b63gP_s₀).baseChange ℚ) ∘ₗ f.toLinearMap.baseChange ℚ := by
    rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp]
    congr 1
    exact LinearMap.ext hfA
  rw [← LinearMap.comp_apply, hc]
  exact b63gW_marking_hJ R v₀ hroot _

example := @b65y_marking_of_chain_u

set_option maxHeartbeats 400000 in
/-- Model discriminant at every parameter of the centre polydisc, for any unlabelled chain from
the retained reference chart to the chart at the centre.
Source: G32 v0.16, Lemma 3.4 and Proposition 6.3; `b65y_rational_composition_of_chain_u`;
b63hp_model_discriminant, b65y_disc_of_comparisons. -/
theorem b65y_model_discriminant_of_chain_u (p : Fin 12 → ℂ)
    (g : Fin 13 → b4b_Group) (D : b65z_SharedFamily (b65z_centre p) g)
    (R : rf8_SharedFamily) (v₀ : R.atlas.π ⁻¹' {b63gP_basePoint})
    (hroot : ∀ i, R.atlas.hπ.fundamentalGroupToMulOpposite v₀ (b63gP_loops i) =
      MulOpposite.op (b4b_root i))
    (H : b65y_UnlabelledHurwitzChain)
    (hH : H.chart 0 = (⟨mr_base, b4b_root, b65z_ofRetained R⟩ : b65y_Chart) ∧
      H.chart (Fin.last H.n) = (⟨b65z_centre p, g, D⟩ : b65y_Chart))
    (B : Module.Basis (Fin 12) ℤ (b63l_parameterLattice (b65z_centre p) D.C D.hC (b6t_polydisc (b65z_centre p)) (Subset.refl _) (b65z_s₀ (b65z_centre p))))
    (P : g32h_PrymFamily) (j : b6t_polydisc (b65z_centre p) ≃ P.S)
    (hj : ∀ t, P.tuple (j t) = (fun i ↦ b4b_toMatrix (g i)) ∧ P.fiber (j t) = b65z_fiber D B t) :
    ∀ s, g32t_disc (g32h_fiber_polarized P s) = classNegTwo := by
  obtain ⟨f, hfA, hfE, -⟩ :=
    b65y_rational_composition_of_chain_u p g D R v₀ hroot H hH
  intro s
  obtain ⟨t, rfl⟩ := j.surjective s
  obtain ⟨T, hTA, hTE⟩ := b65y_chart_transport D t (b65z_s₀ (b65z_centre p))
  obtain ⟨ε, hεA, r, rfl, -, hεE⟩ := b65y_normalization D B t (P.fiber (j t))
    (hj t).2 (P.nondegenerate (j t))
  obtain ⟨ε₀, hε₀A, r, rfl, -, hε₀E⟩ := b63hp_normalization R b63gP_s₀
  have hFA : ∀ v, (T.trans f) (D.A t v) = R.A b63gP_s₀ ((T.trans f) v) := by
    intro v
    change f (T (D.A t v)) = _
    rw [hTA, hfA]
    rfl
  have hFE : ∀ v w,
      b65y_pairing (⟨mr_base, b4b_root, b65z_ofRetained R⟩ : b65y_Chart)
        ((T.trans f) v) ((T.trans f) w) =
      b63e_singularQ (b65z_centre p) D.C D.hC (b6t_polydisc (b65z_centre p))
        (Subset.refl _) t (D.P t) (D.Q t) v w := by
    intro v w
    exact (hfE (T v) (T w)).trans (hTE v w)
  have hd := b65y_disc_of_comparisons ((D.A t).baseChange ℚ)
    ((R.A b63gP_s₀).baseChange ℚ) _ _ ((T.trans f).baseChange ℤ ℚ _ _)
    (b64b_integral_intertwines _ _ (T.trans f) hFA)
    (b64b_integral_pairing_transport _ _ (T.trans f) hFE)
    (P.fiber (j t)) ((b63gR_family R).fiber b63gP_s₀)
    (g32h_fiber_polarized P (j t)) (g32h_fiber_polarized (b63gR_family R) b63gP_s₀)
    ε ε₀ hεA hε₀A (fun v w ↦ (hεE v w).trans (one_mul _))
    (fun v w ↦ (hε₀E v w).trans (one_mul _))
  exact hd.trans (b63hp_model_discriminant R v₀ hroot b63gP_s₀)

example := @b65y_model_discriminant_of_chain_u

set_option maxHeartbeats 400000 in
/-- The G32-centre all-parameter polarization supplier, for any unlabelled chain from the
retained reference chart to the chart at the centre.
Source: G32 v0.16, Lemma 3.4 and Proposition 6.3; `b65y_model_discriminant_of_chain_u`;
b65y_normalization, hp_parabolicPolarization_of_disc. -/
theorem b65y_polarization_of_chain_u (p : Fin 12 → ℂ)
    (g : Fin 13 → b4b_Group) (D : b65z_SharedFamily (b65z_centre p) g)
    (R : rf8_SharedFamily) (v₀ : R.atlas.π ⁻¹' {b63gP_basePoint})
    (hroot : ∀ i, R.atlas.hπ.fundamentalGroupToMulOpposite v₀ (b63gP_loops i) =
      MulOpposite.op (b4b_root i))
    (H : b65y_UnlabelledHurwitzChain)
    (hH : H.chart 0 = (⟨mr_base, b4b_root, b65z_ofRetained R⟩ : b65y_Chart) ∧
      H.chart (Fin.last H.n) = (⟨b65z_centre p, g, D⟩ : b65y_Chart))
    (B : Module.Basis (Fin 12) ℤ (b63l_parameterLattice (b65z_centre p) D.C D.hC (b6t_polydisc (b65z_centre p)) (Subset.refl _) (b65z_s₀ (b65z_centre p))))
    (P : g32h_PrymFamily) (j : b6t_polydisc (b65z_centre p) ≃ P.S)
    (hj : ∀ t, P.tuple (j t) = (fun i ↦ b4b_toMatrix (g i)) ∧ P.fiber (j t) = b65z_fiber D B t) :
    (∀ t : b6t_polydisc (b65z_centre p),
      let Λ := b63l_parameterLattice (b65z_centre p) D.C D.hC (b6t_polydisc (b65z_centre p)) (Subset.refl _) t
      let E := b63e_singularQ (b65z_centre p) D.C D.hC (b6t_polydisc (b65z_centre p)) (Subset.refl _) t
        (D.P t) (D.Q t)
      let X := (P.fiber (j t)).X
      let h := g32h_fiber_polarized P (j t)
      letI := (torusCohomology_cupProductOf X).finite
      ∃ ε : (ℚ ⊗[ℤ] Λ) ≃ₗ[ℚ] HQ X 1,
        (∀ y, ε ((D.A t).baseChange ℚ y) = -(P.fiber (j t)).W.J (ε y)) ∧
        ∃ r : ℚ, r = 1 ∧ 0 < r ∧
          ∀ y z, polarizationForm (torusCohomology_cupProductOf X) h.nondegenerate
            (ε y) (ε z) = r * E.baseChange ℚ y z) ∧
    ∀ s, g32d_ParabolicPolarization (g32h_fiber_polarized P s) := by
  refine ⟨?_, fun s ↦ hp_parabolicPolarization_of_disc _ _
    (b65y_model_discriminant_of_chain_u p g D R v₀ hroot H hH B P j hj s)⟩
  intro t
  exact b65y_normalization D B t (P.fiber (j t)) (hj t).2 (P.nondegenerate (j t))

example := @b65y_polarization_of_chain_u

/-- The archived-signature marking supplier, for any unlabelled chain from the retained
reference chart to the chart at the centre.
Source: `b65y_marking_of_chain_u`; docs/specs/PathCoverFamily.md, set-aside signature. -/
theorem b65z_marking_of_chain_u (p : Fin 12 → ℂ)
    (g : Fin 13 → b4b_Group) (D : b65z_SharedFamily (b65z_centre p) g)
    (R : rf8_SharedFamily) (v₀ : R.atlas.π ⁻¹' {b63gP_basePoint})
    (hroot : ∀ i, R.atlas.hπ.fundamentalGroupToMulOpposite v₀ (b63gP_loops i) =
      MulOpposite.op (b4b_root i))
    (H : b65y_UnlabelledHurwitzChain)
    (hH : H.chart 0 = (⟨mr_base, b4b_root, b65z_ofRetained R⟩ : b65y_Chart) ∧
      H.chart (Fin.last H.n) = (⟨b65z_centre p, g, D⟩ : b65y_Chart)) :
    ∃ m : (ℚ ⊗[ℤ] b63l_parameterLattice (b65z_centre p) D.C D.hC (b6t_polydisc (b65z_centre p)) (Subset.refl _) (b65z_s₀ (b65z_centre p))) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice),
      (∀ y, m ((D.A (b65z_s₀ (b65z_centre p))).baseChange ℚ y) = b60_omega.baseChange ℚ (m y)) ∧
      ∀ y z, b60_E.baseChange ℚ (m y) (m z) =
        (b63e_singularQ (b65z_centre p) D.C D.hC (b6t_polydisc (b65z_centre p)) (Subset.refl _)
          (b65z_s₀ (b65z_centre p)) (D.P (b65z_s₀ (b65z_centre p)))
          (D.Q (b65z_s₀ (b65z_centre p)))).baseChange ℚ y z :=
  b65y_marking_of_chain_u p g D R v₀ hroot H hH

example := @b65z_marking_of_chain_u

/-- The archived-signature polarization supplier, for any unlabelled chain from the retained
reference chart to the chart at the centre.
Source: `b65y_polarization_of_chain_u`; docs/specs/PathCoverFamily.md, set-aside signature. -/
theorem b65z_polarization_of_chain_u (p : Fin 12 → ℂ)
    (g : Fin 13 → b4b_Group) (D : b65z_SharedFamily (b65z_centre p) g)
    (R : rf8_SharedFamily) (v₀ : R.atlas.π ⁻¹' {b63gP_basePoint})
    (hroot : ∀ i, R.atlas.hπ.fundamentalGroupToMulOpposite v₀ (b63gP_loops i) =
      MulOpposite.op (b4b_root i))
    (H : b65y_UnlabelledHurwitzChain)
    (hH : H.chart 0 = (⟨mr_base, b4b_root, b65z_ofRetained R⟩ : b65y_Chart) ∧
      H.chart (Fin.last H.n) = (⟨b65z_centre p, g, D⟩ : b65y_Chart))
    (B : Module.Basis (Fin 12) ℤ (b63l_parameterLattice (b65z_centre p) D.C D.hC (b6t_polydisc (b65z_centre p)) (Subset.refl _) (b65z_s₀ (b65z_centre p))))
    (P : g32h_PrymFamily) (j : b6t_polydisc (b65z_centre p) ≃ P.S)
    (hj : ∀ t, P.tuple (j t) = (fun i ↦ b4b_toMatrix (g i)) ∧ P.fiber (j t) = b65z_fiber D B t) :
    (∀ t : b6t_polydisc (b65z_centre p),
      let Λ := b63l_parameterLattice (b65z_centre p) D.C D.hC (b6t_polydisc (b65z_centre p)) (Subset.refl _) t
      let E := b63e_singularQ (b65z_centre p) D.C D.hC (b6t_polydisc (b65z_centre p)) (Subset.refl _) t
        (D.P t) (D.Q t)
      let X := (P.fiber (j t)).X
      let h := g32h_fiber_polarized P (j t)
      letI := (torusCohomology_cupProductOf X).finite
      ∃ ε : (ℚ ⊗[ℤ] Λ) ≃ₗ[ℚ] HQ X 1,
        (∀ y, ε ((D.A t).baseChange ℚ y) = -(P.fiber (j t)).W.J (ε y)) ∧
        ∃ r : ℚ, r = 1 ∧ 0 < r ∧
          ∀ y z, polarizationForm (torusCohomology_cupProductOf X) h.nondegenerate
            (ε y) (ε z) = r * E.baseChange ℚ y z) ∧
    ∀ s, g32d_ParabolicPolarization (g32h_fiber_polarized P s) :=
  b65y_polarization_of_chain_u p g D R v₀ hroot H hH B P j hj

example := @b65z_polarization_of_chain_u

end HodgeLean.Foundations.Program
