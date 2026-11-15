import HodgeLean.Foundations.Program.BraidBridgesTwoDefs
import HodgeLean.Foundations.Program.BraidBridgesTwoCutBasis
import HodgeLean.Foundations.Program.BraidBridges
import HodgeLean.Foundations.Program.BraidBridgesTwoTrace
import HodgeLean.Foundations.Program.RigidStartingSystem

/-! # Downstairs geometric comparison bodies. -/

noncomputable section
namespace HodgeLean.Foundations.Program

theorem b65x_trace_crossings_aux (x : b65s_regular) (δ : Fin 13 → Path x x)
    (hδ : ∀ i s, (δ i s).val = b65b_inverseNormalization (b65b_lasso i s)) (i : Fin 13) :
    b65x_CrossesAs ((δ i).map b65x_phiMap.continuous) (b65x_rawWord i) :=
  b65x_tc_trace x δ hδ i

theorem b65x_cut_generators_aux (y : b65x_Down) (hy : ∀ k, ¬ b65x_OnCut k y.val) :
    ∃ g : Fin 3 → Path y y, ∀ j, b65x_CrossesAs (g j) [(j, 1)] := by
  obtain ⟨x, rfl⟩ := b65x_cbConj.surjective y
  obtain ⟨ℓ, hℓ, -⟩ := b65x_cutBasis x (b65x_cb_offCut x hy)
  exact ⟨ℓ, hℓ⟩

theorem b65x_cut_peripheral_aux (y : b65x_Down) (g : Fin 3 → Path y y)
    (hg : ∀ j, b65x_CrossesAs (g j) [(j, 1)]) :
    (List.ofFn (b65x_peripheral y g)).prod = 1 ∧
    (∀ (G : Type) [Group G] (v : Fin 4 → G), (List.ofFn v).prod = 1 →
      ∃! φ : FundamentalGroup b65x_Down y →* G,
        ∀ i, φ (b65x_peripheral y g i) = v i) ∧
    (∀ (M : FundamentalGroup b65x_Down y →*
        ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ),
      (∀ p : Path y y, (M (FundamentalGroup.fromPath ⟦p⟧)).val =
        b65f_transport (Fin 4 → ℂ) b65r_A (fun t ↦ (p.extend t).val)) →
      ∀ i, IsConj (b65r_printedOperatorHom (b4b_generators i))
        (M (b65x_peripheral y g i))) := by
  have hy : ∀ k, ¬ b65x_OnCut k y.val := by
    intro k hk
    obtain ⟨u, -, hu01, -, hcut, -⟩ := hg 0
    obtain ⟨m, -, hm⟩ := (hcut k 0).mp (by simpa using hk)
    have h := (hu01 m).1
    rw [← hm] at h
    simp at h
  obtain ⟨x, rfl⟩ := b65x_cbConj.surjective y
  obtain ⟨ℓ, hℓ, hfree, hloc⟩ := b65x_cutBasis x (b65x_cb_offCut x hy)
  have hgℓ : ∀ j, FundamentalGroup.fromPath ⟦g j⟧ = FundamentalGroup.fromPath ⟦ℓ j⟧ := by
    intro j
    have h := b65x_cut_word g hg (ℓ j) [(j, 1)] (hℓ j)
    simpa using h.symm
  refine ⟨?_, ?_, ?_⟩
  · change FundamentalGroup.fromPath ⟦g 0⟧ *
      (FundamentalGroup.fromPath ⟦g 1⟧ *
        (((FundamentalGroup.fromPath ⟦g 1⟧)⁻¹ * FundamentalGroup.fromPath ⟦g 2⟧ *
          FundamentalGroup.fromPath ⟦g 1⟧) *
          ((FundamentalGroup.fromPath ⟦g 0⟧ * FundamentalGroup.fromPath ⟦g 2⟧ *
            FundamentalGroup.fromPath ⟦g 1⟧)⁻¹ * 1))) = 1
    group
  · intro G _ v hv
    simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one] at hv
    have hv3 : v 3 = (v 0 * v 1 * v 2)⁻¹ := by
      apply eq_inv_of_mul_eq_one_right
      rw [mul_assoc, mul_assoc]
      exact hv
    obtain ⟨φ, hφ, huniq⟩ := hfree G ![v 0, v 1, v 1 * v 2 * (v 1)⁻¹]
    have h0 : φ (FundamentalGroup.fromPath ⟦g 0⟧) = v 0 := by rw [hgℓ]; exact hφ 0
    have h1 : φ (FundamentalGroup.fromPath ⟦g 1⟧) = v 1 := by rw [hgℓ]; exact hφ 1
    have h2 : φ (FundamentalGroup.fromPath ⟦g 2⟧) = v 1 * v 2 * (v 1)⁻¹ := by
      rw [hgℓ]; exact hφ 2
    refine ⟨φ, ?_, ?_⟩
    · intro i
      fin_cases i
      · exact h0
      · exact h1
      · change φ ((FundamentalGroup.fromPath ⟦g 1⟧)⁻¹ * FundamentalGroup.fromPath ⟦g 2⟧ *
          FundamentalGroup.fromPath ⟦g 1⟧) = v 2
        rw [map_mul, map_mul, map_inv, h1, h2]
        group
      · change φ (FundamentalGroup.fromPath ⟦g 0⟧ * FundamentalGroup.fromPath ⟦g 2⟧ *
          FundamentalGroup.fromPath ⟦g 1⟧)⁻¹ = v 3
        rw [map_inv, map_mul, map_mul, h0, h1, h2, hv3]
        group
    · intro ψ hψ
      apply huniq
      have k0 : ψ (FundamentalGroup.fromPath ⟦g 0⟧) = v 0 := hψ 0
      have k1 : ψ (FundamentalGroup.fromPath ⟦g 1⟧) = v 1 := hψ 1
      have k2 : ψ ((FundamentalGroup.fromPath ⟦g 1⟧)⁻¹ * FundamentalGroup.fromPath ⟦g 2⟧ *
          FundamentalGroup.fromPath ⟦g 1⟧) = v 2 := hψ 2
      rw [map_mul, map_mul, map_inv, k1] at k2
      intro j
      rw [← hgℓ]
      fin_cases j
      · exact k0
      · exact k1
      · change ψ (FundamentalGroup.fromPath ⟦g 2⟧) = v 1 * v 2 * (v 1)⁻¹
        rw [← k2]
        group
  · intro M hM
    obtain ⟨hfin, hinf⟩ := hloc M hM
    intro i
    fin_cases i
    · change IsConj _ (M (FundamentalGroup.fromPath ⟦g 0⟧))
      rw [hgℓ]
      exact hfin 0
    · change IsConj _ (M (FundamentalGroup.fromPath ⟦g 1⟧))
      rw [hgℓ]
      exact hfin 1
    · change IsConj _ (M ((FundamentalGroup.fromPath ⟦g 1⟧)⁻¹ * FundamentalGroup.fromPath ⟦g 2⟧ *
        FundamentalGroup.fromPath ⟦g 1⟧))
      rw [hgℓ, hgℓ]
      refine (hfin 2).trans (isConj_iff.mpr ⟨(M (FundamentalGroup.fromPath ⟦ℓ 1⟧))⁻¹, ?_⟩)
      rw [map_mul, map_mul, map_inv, inv_inv]
    · change IsConj _ (M (FundamentalGroup.fromPath ⟦g 0⟧ * FundamentalGroup.fromPath ⟦g 2⟧ *
        FundamentalGroup.fromPath ⟦g 1⟧)⁻¹)
      rw [hgℓ, hgℓ, hgℓ]
      exact hinf

theorem b65x_downstairs_marking_aux (y : b65x_Down) (g : Fin 3 → Path y y)
    (hg : ∀ j, b65x_CrossesAs (g j) [(j, 1)]) :
    ∃ κ : FundamentalGroup b65x_Down y →* b4b_Group,
      (∀ j, κ (FundamentalGroup.fromPath ⟦g j⟧) = b65b_cut j) ∧
      ∃ C : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ, ∀ γ : Path y y,
        b65f_transport (Fin 4 → ℂ) b65r_A (fun t ↦ (γ.extend t).val) =
          C.val * b65r_operator (b4b_toMatrix (κ (FundamentalGroup.fromPath ⟦γ⟧))) *
            (C⁻¹).val := by
  have hreg : ∃ M : FundamentalGroup b65x_Down y →* ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ,
      ∀ p : Path y y, (M (FundamentalGroup.fromPath ⟦p⟧)).val =
        b65f_transport (Fin 4 → ℂ) b65r_A (fun t ↦ (p.extend t).val) :=
    b65r_regular_monodromy (Fin 4 → ℂ) b65r_sourceDomain b65r_sourceDomain_open b65r_A
      b65r_A_analytic y
  obtain ⟨M, hM⟩ := hreg
  obtain ⟨hγ, hu, hloc⟩ := b65x_cut_peripheral_aux y g hg
  have hcls := hloc M hM
  let γ := b65x_peripheral y g
  let T := fun i ↦ b65r_printedUnitHom (b4b_generators i)
  let S := fun i ↦ b65r_operatorUnitsEquiv.symm (M (γ i))
  have hT : (List.ofFn T).prod = 1 := by
    rw [show List.ofFn T = (List.ofFn b4b_generators).map b65r_printedUnitHom by
      rw [List.map_ofFn]; rfl, ← map_list_prod, b65r_printed_generators_prod, map_one]
  have hS : (List.ofFn S).prod = 1 := by
    rw [show List.ofFn S = (List.ofFn γ).map (b65r_operatorUnitsEquiv.symm.toMonoidHom.comp M) by
      rw [List.map_ofFn]; rfl, ← map_list_prod, hγ, map_one]
  have hL : ∀ i, ∃ C : (Matrix (Fin 4) (Fin 4) ℂ)ˣ, C * T i * C⁻¹ = S i := by
    intro i
    obtain ⟨C, hC⟩ := isConj_iff.mp (hcls i)
    refine ⟨b65r_operatorUnitsEquiv.symm C, ?_⟩
    have hh := congrArg b65r_operatorUnitsEquiv.symm hC
    simpa only [map_mul, map_inv, b65r_printedOperatorHom, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] using hh
  obtain ⟨D, hD⟩ := b65r_rigidity 4 4 (by norm_num) T S hT hS
    b65r_four_point_irreducible b65r_printed_index hL
  let C := b65r_operatorUnitsEquiv D
  have hC (i : Fin 4) : C * b65r_printedOperatorHom (b4b_generators i) * C⁻¹ = M (γ i) := by
    have hh := congrArg b65r_operatorUnitsEquiv (hD i)
    simpa [T, S, C, b65r_printedOperatorHom] using hh
  obtain ⟨ρ, hρ, -⟩ := hu b4b_Group b4b_generators b65r_printed_generators_prod
  let N : FundamentalGroup b65x_Down y →* ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ :=
    (MulAut.conj C).toMonoidHom.comp (b65r_printedOperatorHom.comp ρ)
  have hN : ∀ i, N (γ i) = M (γ i) := by
    intro i
    change C * b65r_printedOperatorHom (ρ (γ i)) * C⁻¹ = M (γ i)
    rw [show ρ (γ i) = b4b_generators i from hρ i]
    exact hC i
  obtain ⟨φ, -, huniq⟩ := hu _ (fun i ↦ M (γ i)) (by
    have hp := congrArg M hγ
    simpa only [map_list_prod, List.map_ofFn, Function.comp_def, map_one] using hp)
  have heq : M = N := (huniq M (fun _ ↦ rfl)).trans (huniq N hN).symm
  refine ⟨ρ, ?_, C, fun γ' ↦ ?_⟩
  · intro j
    have h0 := hρ 0
    have h1 := hρ 1
    have h2 := hρ 2
    change ρ (FundamentalGroup.fromPath ⟦g 0⟧) = b4b_generators 0 at h0
    change ρ (FundamentalGroup.fromPath ⟦g 1⟧) = b4b_generators 1 at h1
    change ρ ((FundamentalGroup.fromPath ⟦g 1⟧)⁻¹ *
      FundamentalGroup.fromPath ⟦g 2⟧ * FundamentalGroup.fromPath ⟦g 1⟧) =
        b4b_generators 2 at h2
    rw [map_mul, map_mul, map_inv, h1] at h2
    fin_cases j
    · exact h0
    · exact h1
    · change ρ (FundamentalGroup.fromPath ⟦g 2⟧) =
        b4b_generators 1 * b4b_generators 2 * (b4b_generators 1)⁻¹
      rw [← h2]
      group
  · rw [← hM γ', heq]
    change (C * b65r_printedOperatorHom (ρ _) * C⁻¹).val = _
    simp only [Units.val_mul, b65r_printedOperatorHom_val]

end HodgeLean.Foundations.Program
