import HodgeLean.Foundations.Program.BraidBridgesThree
import HodgeLean.Foundations.Program.PathCoverFamilyExists
import HodgeLean.Foundations.Program.PathCoverFamily
import HodgeLean.Foundations.Program.SchlesingerPathMobius
import HodgeLean.Foundations.Program.NamedLoopFamilyCover

/-! # Specified named-loop family: open bodies. -/

noncomputable section
open Set Manifold Filter Topology HodgeLean.Papers
open scoped ContDiff TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.totalChart
  b65z_SharedFamily.totalMan b65z_SharedFamily.fibreChart b65z_SharedFamily.fibreMan
  b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact b65z_SharedFamily.fibreConnected
  b65z_SharedFamily.fibreFaithful

theorem b65w_root_mem (p : Fin 12 → ℂ)
    (hp : ∀ k : Fin 12,
      |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
      |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
      b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0) (j : Fin 12) :
    ((p j : ℂ) : OnePoint ℂ) ∈ b65s_branch := by
  have key : ∀ m, ((p (b65b_boxIndex m) : ℂ) : OnePoint ℂ) ∈ b65s_branch := by
    intro m
    have h := (hp m).2.2
    refine ⟨_, rfl, Or.inr ?_⟩
    fin_cases m <;> simp [b65b_boxFibre] at h ⊢ <;> simp [h]
  fin_cases j
  · simpa [b65b_boxIndex] using key 7
  · simpa [b65b_boxIndex] using key 3
  · simpa [b65b_boxIndex] using key 8
  · simpa [b65b_boxIndex] using key 1
  · simpa [b65b_boxIndex] using key 9
  · simpa [b65b_boxIndex] using key 2
  · simpa [b65b_boxIndex] using key 5
  · simpa [b65b_boxIndex] using key 11
  · simpa [b65b_boxIndex] using key 10
  · simpa [b65b_boxIndex] using key 4
  · simpa [b65b_boxIndex] using key 0
  · simpa [b65b_boxIndex] using key 6

theorem b65w_branch_eq (p : Fin 12 → ℂ)
    (hp : ∀ k : Fin 12,
      |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
      |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
      b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0) (w : OnePoint ℂ) :
    w ∈ b65s_branch ↔ w ∈ Set.range (b65p_source p 0) := by
  have hmov : b65p_moving p 0 = p := by
    funext j
    simp [b65p_moving, b65p_poles]
  constructor
  · rintro ⟨z, rfl, hz⟩
    by_cases h0 : z = 0
    · exact ⟨12, by simp [b65p_source, h0, Fin.append, Fin.addCases]⟩
    have hreg : z ∉ b65s_regular := by
      intro hr
      rcases hz with hz | hz | hz
      · exact h0 hz
      · exact hr.2.2.2.2.1 hz
      · exact hr.2.2.2.2.2 hz
    have hex : ∃ q, z = b65p_poles p 0 q := by
      by_contra hne
      push Not at hne
      exact hreg (((b65p_base_system p hp).2.1 z).2 hne)
    obtain ⟨q, rfl⟩ := hex
    rcases q with k | j
    · exfalso
      fin_cases k
      · exact h0 (by simp [b65p_poles, b65p_fixedPole])
      all_goals
        rcases hz with hz | hz | hz <;>
          norm_num [b65p_poles, b65p_fixedPole, b65r_P] at hz
    · rw [b65p_source, hmov]
      fin_cases j
      · exact ⟨0, by simp [b65p_poles, Fin.append, Fin.addCases]⟩
      · exact ⟨1, by simp [b65p_poles, Fin.append, Fin.addCases]⟩
      · exact ⟨2, by simp [b65p_poles, Fin.append, Fin.addCases]⟩
      · exact ⟨3, by simp [b65p_poles, Fin.append, Fin.addCases]⟩
      · exact ⟨4, by simp [b65p_poles, Fin.append, Fin.addCases]⟩
      · exact ⟨5, by simp [b65p_poles, Fin.append, Fin.addCases]⟩
      · exact ⟨6, by simp [b65p_poles, Fin.append, Fin.addCases]⟩
      · exact ⟨7, by simp [b65p_poles, Fin.append, Fin.addCases]⟩
      · exact ⟨8, by simp [b65p_poles, Fin.append, Fin.addCases]⟩
      · exact ⟨9, by simp [b65p_poles, Fin.append, Fin.addCases]⟩
      · exact ⟨10, by simp [b65p_poles, Fin.append, Fin.addCases]⟩
      · exact ⟨11, by simp [b65p_poles, Fin.append, Fin.addCases]⟩
  · rintro ⟨k, rfl⟩
    rw [b65p_source, hmov]
    fin_cases k
    iterate 12 (· simpa [Fin.append, Fin.addCases] using b65w_root_mem p hp _)
    · exact ⟨0, by simp [Fin.append, Fin.addCases], Or.inl rfl⟩

theorem b65w_mobius_restriction_aux (p : Fin 12 → ℂ)
    (hp : ∀ k : Fin 12,
      |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
      |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
      b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0) :
    ∃ e : b65s_sphere ≃ₜ b6t_punctured (b65z_centre p),
      (∀ z, (e z : OnePoint ℂ) = b65p_mobius (p 10) (p 11) z) ∧
      ∀ k, b65p_mobius (p 10) (p 11) (b65p_source p 0 k) =
        b6_branch (b65z_centre p) k := by
  obtain ⟨M, hM, hlab⟩ := ((b65p_normalized_path p hp).1.self_of_nhds).2
  have hmov : b65p_moving p 0 = p := by
    funext j
    simp [b65p_moving, b65p_poles]
  rw [hmov] at hM
  have hlab' : ∀ k, b65p_mobius (p 10) (p 11) (b65p_source p 0 k) =
      b6_branch (b65z_centre p) k := by
    intro k
    rw [← hM]
    exact hlab k
  have hiff : ∀ w, w ∈ b65s_sphere ↔ M w ∈ b6t_punctured (b65z_centre p) := by
    intro w
    simp only [b65s_sphere, b6t_punctured, Set.mem_compl_iff, not_iff_not]
    rw [b65w_branch_eq p hp]
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k, (hlab k).symm⟩
    · rintro ⟨k, hk⟩
      refine ⟨k, M.injective ?_⟩
      rw [← hk]
      exact hlab k
  refine ⟨M.subtype hiff, fun z ↦ ?_, hlab'⟩
  change M z.val = _
  rw [hM]

theorem b65w_inclusion_surjective (x : b65s_regular) :
    Function.Surjective (FundamentalGroup.map b65s_inclusion x) := by
  have hfill := (b65t_puncture_fill b65s_sphere b65t_sphere_open b65t_F (b65t_chart x)).1
  have hchart : Function.Surjective (FundamentalGroup.map b65t_chart x) := by
    intro d
    refine ⟨FundamentalGroup.map b65t_unchart (b65t_chart x) d, ?_⟩
    obtain ⟨γ, hγ⟩ := Quotient.exists_rep d.asHom
    have hd : d = FundamentalGroup.fromPath ⟦γ⟧ := by
      rw [show (⟦γ⟧ : Path.Homotopic.Quotient _ _) = d.asHom from hγ]
    rw [hd]
    change FundamentalGroup.fromPath ⟦(γ.map b65t_unchart.continuous).map b65t_chart.continuous⟧ =
      FundamentalGroup.fromPath ⟦γ⟧
    congr 2
    ext t
    exact (b65t_elim_mem (γ t)).2
  intro d
  obtain ⟨d', rfl⟩ := hfill d
  obtain ⟨c, rfl⟩ := hchart d'
  exact ⟨c, b65t_inclusion_map x c⟩

theorem b65w_conj_eq_one (g : b4b_Group) (C : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ) :
    C.val * b65r_operator (b4b_toMatrix g) * (C⁻¹).val = 1 ↔ g = 1 := by
  have hone : b65r_operator (b4b_toMatrix (1 : b4b_Group)) = 1 := map_one b65s_action
  constructor
  · intro h
    have e : b65r_operator (b4b_toMatrix g) =
        (C⁻¹).val * (C.val * b65r_operator (b4b_toMatrix g) * (C⁻¹).val) * C.val := by
      simp only [mul_assoc, Units.inv_mul, mul_one]
      simp only [← mul_assoc, Units.inv_mul, one_mul]
    rw [h, mul_one, Units.inv_mul, ← hone] at e
    exact Subtype.val_injective ((b65t_operator_injective e).trans (map_one b4b_toMatrix))
  · rintro rfl
    rw [hone, mul_one, Units.mul_inv]

theorem b65w_marking_surjective_aux (x : b65s_regular) (ρ : FundamentalGroup b65s_sphere (b65s_inclusion x) →* b4b_Group)
    (C : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ)
    (hT : ∀ η : Path x x,
      b65f_transport (Fin 4 → ℂ) b65r_pullback (fun t ↦ (η.extend t).val) =
        C.val * b65r_operator (b4b_toMatrix
          (ρ (FundamentalGroup.map b65s_inclusion x (FundamentalGroup.fromPath ⟦η⟧)))) *
            (C⁻¹).val) :
    Function.Surjective ρ := by
  obtain ⟨ρ', hρ', C', hT'⟩ := b65t_pullback_monodromy x
  set φ := FundamentalGroup.map b65s_inclusion x
  have hφ : Function.Surjective φ := b65w_inclusion_surjective x
  have hker : (ρ.comp φ).ker = (ρ'.comp φ).ker := by
    ext c
    obtain ⟨η, hη⟩ := Quotient.exists_rep c.asHom
    have hc : c = FundamentalGroup.fromPath ⟦η⟧ := by
      rw [show (⟦η⟧ : Path.Homotopic.Quotient x x) = c.asHom from hη]
    rw [hc, MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.comp_apply,
      ← b65w_conj_eq_one _ C, ← b65w_conj_eq_one _ C', ← hT η, hT' η]
  have htop : (ρ'.comp φ).range = ⊤ :=
    MonoidHom.range_eq_top.mpr (hρ'.comp hφ)
  have hcard : Nat.card (ρ.comp φ).range = Nat.card b4b_Group := by
    rw [← Subgroup.card_top (G := b4b_Group), ← htop]
    exact Nat.card_congr ((QuotientGroup.quotientKerEquivRange (ρ.comp φ)).symm.toEquiv.trans
      ((QuotientGroup.quotientMulEquivOfEq hker).toEquiv.trans
        (QuotientGroup.quotientKerEquivRange (ρ'.comp φ)).toEquiv))
  have hr := Subgroup.eq_top_of_card_eq _ hcard
  intro g
  obtain ⟨c, hc⟩ := (MonoidHom.range_eq_top.mp hr) g
  exact ⟨φ c, hc⟩

theorem b65w_named_family_aux (p : Fin 12 → ℂ)
    (hp : ∀ k : Fin 12,
      |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
      |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
      b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0)
    (e : b65s_sphere ≃ₜ b6t_punctured (b65z_centre p))
    (he : ∀ z, (e z : OnePoint ℂ) = b65p_mobius (p 10) (p 11) z)
    (x : b65s_regular) (δ : Fin 13 → Path x x)
    (hδ : ∀ i s, (δ i s).val = b65b_inverseNormalization (b65b_lasso (b65x_slot i) s))
    (ρ : FundamentalGroup b65s_sphere (b65s_inclusion x) →* b4b_Group)
    (hρ : Function.Surjective ρ)
    (hnamed : ∀ i, ρ (FundamentalGroup.map b65s_inclusion x
      (FundamentalGroup.fromPath ⟦δ i⟧)) = b65b_initial i) :
    ∃ g : Fin 13 → b4b_Group, g32h_Nielsen (fun i ↦ b4b_toMatrix (g i)) ∧
    ∃ D : b65z_SharedFamily (b65z_centre p) g,
    ∃ u₀ : D.atlas.π ⁻¹' {e (b65s_inclusion x)},
      ∀ a : FundamentalGroup b65s_sphere (b65s_inclusion x),
        D.atlas.hπ.fundamentalGroupToMulOpposite u₀
          ((FundamentalGroup.map (⟨e, e.continuous⟩ : C(b65s_sphere, b6t_punctured (b65z_centre p))) (b65s_inclusion x)) a) = MulOpposite.op (ρ a)⁻¹ :=
  b65w_named_family_core p hp e he x δ hδ ρ hρ hnamed

theorem b65w_column_conversion_aux (Γ : Type*) [Group Γ] (ρ : Γ →* b4b_Group)
    (μ : Γ →* b4b_Groupᵐᵒᵖ)
    (hμ : ∀ a, μ a = MulOpposite.op (ρ a)⁻¹) :
    ∀ a, (b65s_column μ a).val = b65r_operator (b4b_toMatrix (ρ a)) := by
  intro a
  change b65r_operator (b4b_toMatrix ((MulOpposite.unop (μ a))⁻¹)) = _
  rw [hμ a, MulOpposite.unop_op, inv_inv]

theorem b65z_schlesinger_identification_aux (p : Fin 12 → ℂ)
    (hp : ∀ k : Fin 12,
      |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
      |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
      b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0) :
    ∃ g : Fin 13 → b4b_Group, g32h_Nielsen (fun i ↦ b4b_toMatrix (g i)) ∧
    ∃ D : b65z_SharedFamily (b65z_centre p) g,
    ∃ e : b65s_sphere ≃ₜ b6t_punctured (b65z_centre p),
      (∀ z, (e z : OnePoint ℂ) = b65p_mobius (p 10) (p 11) z) ∧
    ∃ x : b65s_regular, ∃ u₀ : D.atlas.π ⁻¹' {e (b65s_inclusion x)},
    ∃ δ : Fin 13 → Path x x,
      (∀ i s, (δ i s).val = b65b_inverseNormalization (b65b_lasso (b65x_slot i) s)) ∧
      (∀ i, ((D.atlas.hπ.fundamentalGroupToMulOpposite u₀).comp
          (FundamentalGroup.map ((⟨e, e.continuous⟩ : C(b65s_sphere, b6t_punctured (b65z_centre p))).comp b65s_inclusion) x))
            (FundamentalGroup.fromPath ⟦δ i⟧) = MulOpposite.op (b65b_initial i)⁻¹) ∧
    ∃ C : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ, ∀ η : Path x x,
      b65f_transport (Fin 4 → ℂ) b65r_pullback (fun t ↦ (η.extend t).val) =
        C.val * (b65s_column ((D.atlas.hπ.fundamentalGroupToMulOpposite u₀).comp
          (FundamentalGroup.map ((⟨e, e.continuous⟩ : C(b65s_sphere, b6t_punctured (b65z_centre p))).comp b65s_inclusion) x))
            (FundamentalGroup.fromPath ⟦η⟧)).val * (C⁻¹).val := by
  obtain ⟨x, δ, -, -, ρ, C, hδ, -, hnamed, -, hT, -, -⟩ := b65b_transported_identification p hp
  have hρ := b65w_marking_surjective_aux x ρ C hT
  obtain ⟨e, he, -⟩ := b65w_mobius_restriction_aux p hp
  obtain ⟨g, hg, D, u₀, hD⟩ := b65w_named_family_aux p hp e he x δ hδ ρ hρ hnamed
  set μ := (D.atlas.hπ.fundamentalGroupToMulOpposite u₀).comp
    (FundamentalGroup.map ((⟨e, e.continuous⟩ : C(b65s_sphere, b6t_punctured (b65z_centre p))).comp
      b65s_inclusion) x) with hμdef
  have hμ : ∀ a, μ a = MulOpposite.op (ρ.comp (FundamentalGroup.map b65s_inclusion x) a)⁻¹ := by
    intro a
    obtain ⟨η, hη⟩ := Quotient.exists_rep a.asHom
    have ha : a = FundamentalGroup.fromPath ⟦η⟧ := by
      rw [show (⟦η⟧ : Path.Homotopic.Quotient x x) = a.asHom from hη]
    rw [ha]
    exact hD (FundamentalGroup.map b65s_inclusion x (FundamentalGroup.fromPath ⟦η⟧))
  refine ⟨g, hg, D, e, he, x, u₀, δ, hδ, fun i ↦ ?_, C, fun η ↦ ?_⟩
  · rw [hμ]
    exact congrArg (fun z ↦ MulOpposite.op z⁻¹) (hnamed i)
  · rw [b65w_column_conversion_aux _ (ρ.comp (FundamentalGroup.map b65s_inclusion x)) μ hμ]
    exact hT η

end HodgeLean.Foundations.Program
