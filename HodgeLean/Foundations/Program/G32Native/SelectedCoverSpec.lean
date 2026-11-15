import HodgeLean.Foundations.Program.G32SelectedRealizationSecond

noncomputable section
set_option maxRecDepth 2000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Papers HodgeLean.Foundations
open HodgeLean.Foundations.Symplectic
open scoped TensorProduct CategoryTheory.MonObj
namespace HodgeLean.Foundations.Program
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.fibreChart
  b65z_SharedFamily.fibreMan b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact
  b65z_SharedFamily.fibreConnected b65z_SharedFamily.totalChart b65z_SharedFamily.totalMan

/-- Retain the group structure and the selected deck lift in the cover export. -/
theorem g32y_cover_spec {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c)
    (hg : g32h_Nielsen (fun j ↦ b4b_toMatrix (g j)))
    (B : Module.Basis (Fin 12) ℤ
      (b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Set.Subset.refl _) (b65z_s₀ c))) :
    ∃ R : g32p_Cover (b65z_fiber D B t),
      R.J = g32x_J D t ∧
      HEq R.grp (inferInstance : GrpObj (g32x_J D t)) ∧
      HEq R.aut (fun a ↦ ((Classical.choose (g32x_deck_realization D t)) a).hom) := by
  classical
  let f := Classical.choose (g32x_deck_realization D t)
  have hf := Classical.choose_spec (g32x_deck_realization D t)
  obtain ⟨h1, hmul⟩ := g32x_deck_laws D t f hf
  obtain ⟨hn, hp, hinv⟩ := g32x_theta_invariant D t f hf
  obtain ⟨i, q, N, hN, hi, hq, hr, hz, hR, a, ha, hw⟩ :=
    g32y_marked_comparison_aux D t hg B f hf
  have hd : Module.finrank ℚ (HQ (b65z_fiber D B t).X 1) = 12 := by
    rw [(torusCohomology_cupProductOf (b65z_fiber D B t).X).finrank_eq]
    let := Module.Free.of_basis B
    let := Module.Finite.of_basis B
    have W := b63e_weight_one_riemann c D.C D.hC (b6t_polydisc c)
      (Set.Subset.refl _) D.hG D.atlas.hb D.atlas.f D.atlas.hf D.atlas.hsurj
      D.hk D.Q₀ D.hQ₀ D.Q D.hQ D.P D.hP (b65z_s₀ c) t
    have h := b63g_model_finrank _ _ W.1 _ W.2
    rw [Module.finrank_eq_card_basis B, Fintype.card_fin] at h
    exact h.symm
  refine ⟨{
    J := g32x_J D t
    aut := fun a ↦ (f a).hom
    aut_hom := fun a ↦ (f a).isMonHom
    aut_one := h1
    aut_mul := hmul
    mult := g32x_multiplicity D t hg f hf
    pol := g32x_theta D t
    pol_nondeg := hn
    pol_pos := hp
    pol_inv := hinv
    inclA := i
    projA := q
    inclA_hom := hi
    projA_hom := hq
    NA := N
    NA_pos := hN
    retractA := hr
    groupRing := hz
    rhoBlock := ?_
    dimA := hd
    centre := a
    centre_eq := ha
    weil := hw
    part := fun S hS ↦ Classical.choice (g32y_part_aux D t hg f hf S hS)
  }, rfl, HEq.rfl, HEq.rfl⟩
  intro x
  apply g32x_rho_image D t f hf
  rw [← hR]
  exact ⟨x, rfl⟩


#print axioms g32y_cover_spec
end HodgeLean.Foundations.Program
