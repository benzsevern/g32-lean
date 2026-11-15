import HodgeLean.Foundations.Program.ComponentTransportRelabelDefs

/-! # Proof obligations for the relabelling edge and the certificate endpoint -/
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
attribute [local instance] rf8_SharedFamily.topC rf8_SharedFamily.chartC
  rf8_SharedFamily.manC rf8_SharedFamily.t2C rf8_SharedFamily.compactC
  rf8_SharedFamily.connectedC rf8_SharedFamily.actionC rf8_SharedFamily.totalChart
  rf8_SharedFamily.totalMan rf8_SharedFamily.fibreChart rf8_SharedFamily.fibreMan
  rf8_SharedFamily.fibreT2 rf8_SharedFamily.fibreCompact rf8_SharedFamily.fibreConnected
  rf8_SharedFamily.fibreFaithful

theorem b65u_relabel_edge_aux {c₁ c₂ : Fin 10 → ℂ} {g₁ g₂ : Fin 13 → b4b_Group}
    (D₁ : b65z_SharedFamily c₁ g₁) (D₂ : b65z_SharedFamily c₂ g₂)
    (M : OnePoint ℂ ≃ₜ OnePoint ℂ)
    (hM : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω M) (hM' : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω M.symm)
    (Φ : b6t_punctured c₁ ≃ₜ b6t_punctured c₂) (hΦ : ∀ x, (Φ x : OnePoint ℂ) = M x)
    (y : b6t_punctured c₁) (u₁ : D₁.atlas.π ⁻¹' {y}) (u₂ : D₂.atlas.π ⁻¹' {Φ y})
    (h : (D₂.atlas.hπ.fundamentalGroupToMulOpposite u₂).comp
        (FundamentalGroup.map ⟨Φ, Φ.continuous⟩ y) =
      D₁.atlas.hπ.fundamentalGroupToMulOpposite u₁) :
    ∃ E : b65y_UnlabelledEdge ⟨c₁, g₁, D₁⟩ ⟨c₂, g₂, D₂⟩,
      E.t₀ = b65z_s₀ c₁ ∧ E.t₁ = b65z_s₀ c₂ ∧
      ∀ z, b63d_projection c₂ D₂.C D₂.atlas.f (b6t_polydisc c₂) (Set.Subset.refl _) E.t₁
          (E.glue z) =
        M (b63d_projection c₁ D₁.C D₁.atlas.f (b6t_polydisc c₁) (Set.Subset.refl _) E.t₀ z) := by
  have hb₂ : c₂ ∈ b6_chart := D₂.atlas.hb
  -- `M` carries the marks of `c₁` exactly onto the marks of `c₂`
  have hmem : ∀ z, z ∈ b6t_punctured c₁ ↔ M z ∈ b6t_punctured c₂ := by
    intro z
    constructor
    · intro hz
      rw [← hΦ ⟨z, hz⟩]
      exact (Φ ⟨z, hz⟩).property
    · intro hz
      obtain ⟨x, hx⟩ := Φ.surjective ⟨M z, hz⟩
      have hx' : M x = M z := by rw [← hΦ x, hx]
      rw [← M.injective hx']
      exact x.property
  have hπΦ := D₁.atlas.hπ.homeomorph_comp Φ
  have hmono : hπΦ.fundamentalGroupToMulOpposite ⟨u₁.val, congrArg Φ u₁.property⟩ =
      D₂.atlas.hπ.fundamentalGroupToMulOpposite u₂ := by
    ext a
    obtain ⟨b, rfl⟩ := b65y_map_surjective Φ y a
    have h1 := DFunLike.congr_fun (b65y_homeomorph_comp_monodromy _ D₁.atlas.hπ Φ y u₁) b
    have h2 := DFunLike.congr_fun h b
    simp only [MonoidHom.comp_apply] at h1 h2
    rw [h1, h2]
  obtain ⟨hι₁, hr₁⟩ := b63g5_fibre_filling c₁ D₁.atlas.hb D₁.atlas.f D₁.atlas.ι D₁.atlas.hι
    D₁.atlas.hrange (b6t_polydisc c₁) (Subset.refl _) (b65z_s₀ c₁)
  obtain ⟨hι₂, hr₂⟩ := b63g5_fibre_filling c₂ D₂.atlas.hb D₂.atlas.f D₂.atlas.ι D₂.atlas.hι
    D₂.atlas.hrange (b6t_polydisc c₂) (Subset.refl _) (b65z_s₀ c₂)
  obtain ⟨-, -, -, -, E, hE, hE', -, hEk, hEg, -⟩ := b6m_based_filling_comparison c₂ hb₂
    b4b_Group D₁.atlas.U D₂.atlas.U (Φ ∘ D₁.atlas.π) D₂.atlas.π hπΦ D₂.atlas.hπ (Φ y)
    ⟨u₁.val, congrArg Φ u₁.property⟩ u₂ hmono
    (b65z_fibre c₁ D₁.C (b65z_s₀ c₁)) (b65z_fibre c₂ D₂.C (b65z_s₀ c₂))
    (M ∘ b63d_projection c₁ D₁.C D₁.atlas.f (b6t_polydisc c₁) (Subset.refl _) (b65z_s₀ c₁))
    (b63d_projection c₂ D₂.C D₂.atlas.f (b6t_polydisc c₂) (Subset.refl _) (b65z_s₀ c₂))
    (b63g5_fibreMap c₁ D₁.atlas.ι (b6t_polydisc c₁) (Subset.refl _) (b65z_s₀ c₁))
    (b63g5_fibreMap c₂ D₂.atlas.ι (b6t_polydisc c₂) (Subset.refl _) (b65z_s₀ c₂))
    (hM.comp (D₁.hk (b65z_s₀ c₁))) (D₂.hk (b65z_s₀ c₂)) hι₁ hι₂
    (by
      rw [hr₁]
      ext z
      exact hmem _)
    hr₂
    (fun u ↦ by
      rw [Function.comp_apply, Function.comp_apply, hΦ]
      congr 1
      simp only [b63d_projection, b63g5_fibreMap, b6a_map, D₁.atlas.hproj]
      exact congrFun (b6t_identity c₁) _)
    (fun u ↦ by
      simp only [b63d_projection, b63g5_fibreMap, b6a_map, D₂.atlas.hproj]
      exact congrFun (b6t_identity c₂) _)
    (fun g u ↦ Subtype.ext (Prod.ext rfl (D₁.atlas.hequiv g u)))
    (fun g u ↦ Subtype.ext (Prod.ext rfl (D₂.atlas.hequiv g u)))
    (fun g ↦ (D₁.hG _ g).continuous) (fun g ↦ (D₂.hG _ g).continuous)
  exact ⟨⟨b65z_s₀ c₁, b65z_s₀ c₂, E, hE, hE', hEg⟩, rfl, rfl, hEk⟩

/-- The restriction of a sphere homeomorphism to punctured spheres it maps onto each other. -/
def b65u_restrict {c₁ c₂ : Fin 10 → ℂ} (M : OnePoint ℂ ≃ₜ OnePoint ℂ)
    (hMc : M '' b6t_punctured c₁ = b6t_punctured c₂) :
    b6t_punctured c₁ ≃ₜ b6t_punctured c₂ :=
  (M.image _).trans (Homeomorph.setCongr hMc)

/-- The restriction agrees with `M` on points. -/
theorem b65u_restrict_apply {c₁ c₂ : Fin 10 → ℂ} (M : OnePoint ℂ ≃ₜ OnePoint ℂ)
    (hMc : M '' b6t_punctured c₁ = b6t_punctured c₂) (x : b6t_punctured c₁) :
    (b65u_restrict M hMc x : OnePoint ℂ) = M x := rfl

/-- A radial walk from a retained chart followed by one relabelling edge through `M`, when the
radial composite followed by `M` carries the based monodromy of the first chart to that of the
last. -/
theorem b65u_walk_of_radial_relabel {g₁ g₂ : Fin 13 → b4b_Group} (hne : ∀ j, g₁ j ≠ 1)
    {c₀ c₁ c₂ : Fin 10 → ℂ} (c : ℕ → Fin 10 → ℂ) (N : ℕ) (h0 : c 0 = c₀) (hN : c N = c₁)
    (hc : ∀ k < N, c (k + 1) ∈ b6t_polydisc (c k))
    (D₀ : b65z_SharedFamily c₀ g₁) (D : b65z_SharedFamily c₂ g₂)
    (y₀ : b6t_punctured c₀) (u₀ : D₀.atlas.π ⁻¹' {y₀})
    (M : OnePoint ℂ ≃ₜ OnePoint ℂ)
    (hM : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω M) (hM' : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω M.symm)
    (hMc : M '' b6t_punctured c₁ = b6t_punctured c₂)
    (Ψ : b6t_punctured c₀ ≃ₜ b6t_punctured c₂)
    (hΨ : ∀ x, (Ψ x : OnePoint ℂ) = M (b65y_radial c N x))
    (w : D.atlas.π ⁻¹' {Ψ y₀})
    (hw : (D.atlas.hπ.fundamentalGroupToMulOpposite w).comp
      (FundamentalGroup.map ⟨Ψ, Ψ.continuous⟩ y₀) =
      D₀.atlas.hπ.fundamentalGroupToMulOpposite u₀) :
    Nonempty (b65y_UnlabelledWalk ⟨c₀, g₁, D₀⟩ ⟨c₂, g₂, D⟩) := by
  subst h0 hN
  obtain ⟨Φ, hΦ, D', u', hmon, ⟨wk⟩⟩ := b65y_walk_radial hne c N hc D₀ y₀ u₀
  have hΨΦ : Ψ = Φ.trans (b65u_restrict M hMc) := by
    ext x
    change (Ψ x : OnePoint ℂ) = M (Φ x)
    rw [hΨ, hΦ]
  subst hΨΦ
  have h : (D.atlas.hπ.fundamentalGroupToMulOpposite w).comp
      (FundamentalGroup.map ⟨b65u_restrict M hMc, (b65u_restrict M hMc).continuous⟩ (Φ y₀)) =
      D'.atlas.hπ.fundamentalGroupToMulOpposite u' := by
    ext a
    obtain ⟨b, rfl⟩ := b65y_map_surjective Φ y₀ a
    have h1 := DFunLike.congr_fun hmon b
    have h2 := DFunLike.congr_fun hw b
    rw [b65y_map_trans] at h2
    simp only [MonoidHom.comp_apply] at h1 h2 ⊢
    rw [h1]
    exact h2
  obtain ⟨E, -, -, -⟩ := b65u_relabel_edge_aux D' D M hM hM' (b65u_restrict M hMc)
    (b65u_restrict_apply M hMc) (Φ y₀) u' w h
  exact ⟨(b65y_unlabelledWalk_of_walk wk).append (.cons E (.nil _))⟩

theorem b65u_chain_unlabelled_of_path_aux (p : Fin 12 → ℂ)
    (g : Fin 13 → b4b_Group) (D : b65z_SharedFamily (b65z_centre p) g)
    (R : rf8_SharedFamily) (v₀ : R.atlas.π ⁻¹' {b63gP_basePoint})
    (c : Fin 10 → ℂ) (γ : C(unitInterval, Fin 10 → ℂ)) (hγ : ∀ τ, γ τ ∈ b6_chart)
    (hγ0 : γ 0 = mr_base) (hγ1 : γ 1 = c)
    (M : OnePoint ℂ ≃ₜ OnePoint ℂ)
    (hM : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω M) (hM' : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω M.symm)
    (hMc : M '' b6t_punctured c = b6t_punctured (b65z_centre p))
    (hmon : ∀ N : ℕ, 0 < N →
      (∀ k < N, b65y_sample γ N (k + 1) ∈ b6t_polydisc (b65y_sample γ N k)) →
      ∀ Ψ : b6t_punctured mr_base ≃ₜ b6t_punctured (b65z_centre p),
        (∀ x, (Ψ x : OnePoint ℂ) = M (b65y_radial (b65y_sample γ N) N x)) →
        ∃ w : D.atlas.π ⁻¹' {Ψ b63gP_basePoint},
          (D.atlas.hπ.fundamentalGroupToMulOpposite w).comp
            (FundamentalGroup.map ⟨Ψ, Ψ.continuous⟩ b63gP_basePoint) =
          R.atlas.hπ.fundamentalGroupToMulOpposite v₀) :
    ∃ H : b65y_UnlabelledHurwitzChain,
      H.chart 0 = (⟨mr_base, b4b_root, b65z_ofRetained R⟩ : b65y_Chart) ∧
      H.chart (Fin.last H.n) = (⟨b65z_centre p, g, D⟩ : b65y_Chart) := by
  obtain ⟨N, hN, hsub⟩ := b65y_path_subdivision γ hγ
  have hc : ∀ k < N, b65y_sample γ N (k + 1) ∈ b6t_polydisc (b65y_sample γ N k) := by
    intro k hk
    have h := hsub k hk
    simp only [b65y_sample, Nat.cast_add, Nat.cast_one]
    exact h
  have h0 : b65y_sample γ N 0 = mr_base := by
    simp only [b65y_sample, Nat.cast_zero, zero_div, Set.projIcc_left]
    exact hγ0
  have hN1 : b65y_sample γ N N = c := by
    have : ((N : ℝ) / N) = 1 := div_self (by exact_mod_cast hN.ne')
    simp only [b65y_sample, this, Set.projIcc_right]
    exact hγ1
  obtain ⟨Φ, hΦ⟩ := b65y_radial_homeomorph (b65y_sample γ N) N h0 hN1 mr_base_mem_chart hc
  let Ψ := Φ.trans (b65u_restrict M hMc)
  have hΨ : ∀ x, (Ψ x : OnePoint ℂ) = M (b65y_radial (b65y_sample γ N) N x) := fun x ↦ by
    change M (Φ x) = _
    rw [hΦ]
  obtain ⟨w, hw⟩ := hmon N hN hc Ψ hΨ
  have hne : ∀ j, b4b_root j ≠ 1 := b65z_nielsen_ne_one b4b_root b63d_root_nielsen
  obtain ⟨wk⟩ := b65u_walk_of_radial_relabel hne (b65y_sample γ N) N h0 hN1 hc
    (b65z_ofRetained R) D b63gP_basePoint v₀ M hM hM' hMc Ψ hΨ w hw
  exact b65y_unlabelled_chain_of_walk wk

/-- One elementary move sends entry `k` to a conjugate of entry `b65u_moveSwap m k`. -/
theorem b65u_step_isConj (m : b65s_Move) (t : Fin 13 → b4b_Group) (k : Fin 13) :
    IsConj (b65s_step m t k) (t (b65u_moveSwap m k)) := by
  cases m with
  | positive i =>
    simp only [b65s_step, b4_braid, b65u_moveSwap]
    by_cases hk : k = i.castSucc
    · subst hk
      rw [Function.update_self, Equiv.swap_apply_left]
      exact isConj_iff.2 ⟨(t i.castSucc)⁻¹, by group⟩
    · rw [Function.update_of_ne hk]; rfl
  | negative i =>
    simp only [b65s_step, b65u_moveSwap]
    by_cases hk : k = i.succ
    · subst hk
      rw [Function.update_self, Equiv.swap_apply_right]
      exact isConj_iff.2 ⟨t i.succ, by group⟩
    · rw [Function.update_of_ne hk]; rfl
  | conjugate g =>
    exact isConj_iff.2 ⟨g⁻¹, by simp [b65s_step, b4_conjTuple, b65u_moveSwap, mul_assoc]⟩

/-- A word sends entry `k` to a conjugate of entry `b65u_movePerm w k`. -/
theorem b65u_word_isConj (w : List b65s_Move) (t : Fin 13 → b4b_Group) (k : Fin 13) :
    IsConj (b65s_word w t k) (t (b65u_movePerm w k)) := by
  induction w generalizing t with
  | nil => rfl
  | cons m w ih =>
    exact (ih (b65s_step m t)).trans (b65u_step_isConj m t _)

/-- Conjugacy passes to inverses. -/
theorem b65u_isConj_inv {a b : b4b_Group} (h : IsConj a b) : IsConj a⁻¹ b⁻¹ := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  exact isConj_iff.2 ⟨c, by rw [← hc]; group⟩

theorem b65u_endpoint_equation_aux (p : Fin 12 → ℂ)
    (hp : ∀ k : Fin 12,
      |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
      |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
      b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0)
    (g : Fin 13 → b4b_Group) (D : b65z_SharedFamily (b65z_centre p) g)
    (e : b65s_sphere ≃ₜ b6t_punctured (b65z_centre p))
    (he : ∀ z, (e z : OnePoint ℂ) = b65p_mobius (p 10) (p 11) z)
    (x : b65s_regular) (u₀ : D.atlas.π ⁻¹' {e (b65s_inclusion x)})
    (δ : Fin 13 → Path x x)
    (hδ : ∀ i s, (δ i s).val = b65b_inverseNormalization (b65b_lasso (b65x_slot i) s))
    (hmono : ∀ i, ((D.atlas.hπ.fundamentalGroupToMulOpposite u₀).comp
        (FundamentalGroup.map ((⟨e, e.continuous⟩ :
          C(b65s_sphere, b6t_punctured (b65z_centre p))).comp b65s_inclusion) x))
          (FundamentalGroup.fromPath ⟦δ i⟧) = MulOpposite.op (b65b_initial i)⁻¹) :
    let μ : Fin 13 → b4b_Group := fun i ↦ MulOpposite.unop
      (((D.atlas.hπ.fundamentalGroupToMulOpposite u₀).comp
        (FundamentalGroup.map ((⟨e, e.continuous⟩ :
          C(b65s_sphere, b6t_punctured (b65z_centre p))).comp b65s_inclusion) x))
          (FundamentalGroup.fromPath ⟦δ i⟧))
    b65s_word b65b_word b65s_columnRoot =
        b4_conjTuple (b4b_generators 1)⁻¹ (b65s_word b65b_pathWord (fun i ↦ (μ i)⁻¹)) ∧
      ∀ j : Fin 13, IsConj (μ (b65u_slotPerm.symm j.rev)) (b4b_root (b65u_endpointPerm j)) := by
  intro μ
  have hμ : ∀ i, μ i = (b65b_initial i)⁻¹ := fun i ↦ by
    simp only [μ, hmono, MulOpposite.unop_op]
  have hμ' : (fun i ↦ (μ i)⁻¹) = b65b_initial := funext fun i ↦ by rw [hμ, inv_inv]
  have hrep := b65b_replay.1
  rw [← b65b_path_replay] at hrep
  refine ⟨by rw [hμ', hrep], fun j ↦ ?_⟩
  -- entry `k` of both sides of the tuple equation
  have hsrc : ∀ k, IsConj (b65b_initial (b65u_movePerm b65b_pathWord k))
      (b65s_columnRoot (b65u_movePerm b65b_word k)) := fun k ↦ by
    have h1 := b65u_word_isConj b65b_word b65s_columnRoot k
    have h2 := b65u_word_isConj b65b_pathWord b65b_initial k
    rw [hrep] at h1
    have h3 : IsConj (b4_conjTuple (b4b_generators 1)⁻¹
        (b65s_word b65b_pathWord b65b_initial) k) (b65s_word b65b_pathWord b65b_initial k) :=
      isConj_iff.2 ⟨b4b_generators 1, by simp [b4_conjTuple, mul_assoc]⟩
    exact h2.symm.trans (h3.symm.trans h1)
  set i := b65u_slotPerm.symm j.rev
  have hk := hsrc ((b65u_movePerm b65b_pathWord).symm i)
  rw [Equiv.apply_symm_apply] at hk
  rw [hμ]
  have hτ : b65u_endpointPerm j =
      (b65u_movePerm b65b_word ((b65u_movePerm b65b_pathWord).symm i)).rev := by
    simp [b65u_endpointPerm, b65u_sourcePerm, i, Equiv.Perm.mul_apply, Equiv.Perm.inv_def]
  rw [hτ]
  have := b65u_isConj_inv hk
  simpa [b65s_columnRoot] using this

theorem b65u_endpoint_classes_aux :
    (∀ k, b65u_movePerm b65b_word k = b65y_wordPerm k) ∧
    (∀ j, b65u_endpointPerm j =
      (![4, 1, 0, 9, 2, 7, 3, 6, 10, 5, 11, 8, 12] : Fin 13 → Fin 13) j) ∧
    (∀ j, b65y_rootClasses (b65u_endpointPerm j) = b65y_rootClasses (b65y_classLabelPerm j)) ∧
    (∀ j, (b4b_toMatrix (b4b_root (b65u_endpointPerm j))).det =
      (b4b_toMatrix (b65b_initial (b65u_slotPerm.symm j.rev))⁻¹).det) ∧
    b65u_endpointPerm 0 ≠ b65y_classLabelPerm 0 := by
  have hcl : ∀ j : Fin 13, b65y_initialInvClasses (b65u_slotPerm.symm j.rev) =
      b65y_rootClasses (b65u_endpointPerm j) := by decide +kernel
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, fun j ↦ ?_, by decide +kernel⟩
  rw [b65y_root_classes, b65y_initial_classes, hcl]

theorem b65u_loops_closure_aux : Subgroup.closure (Set.range b63gP_loops) = ⊤ := by
  have hγ : ∀ i, mr_IsLoop mr_base b63gP_basePoint i (b63gP_loops i) := fun i ↦
    (mr_loop_existsUnique mr_base b63gP_s₀.property b63gP_basePoint rfl i).exists.choose_spec
  exact b64b_peripheral_generates _ b63gP_loops
    (mr_loops_product mr_base b63gP_s₀.property b63gP_basePoint b63gP_loops hγ)
    (mr_loops_universal mr_base b63gP_s₀.property b63gP_basePoint b63gP_loops hγ)

theorem b65u_lift_adjust_aux {X U G : Type} [TopologicalSpace X] [TopologicalSpace U]
    [Group G] [MulAction G U] (π : U → X) (hπ : IsQuotientCoveringMap π G)
    (y : X) (u : π ⁻¹' {y}) {r : ℕ} (γ : Fin r → FundamentalGroup X y)
    (hγ : Subgroup.closure (Set.range γ) = ⊤) (φ : FundamentalGroup X y →* Gᵐᵒᵖ) (a : G)
    (h : ∀ i, MulOpposite.unop (hπ.fundamentalGroupToMulOpposite u (γ i)) =
      a * MulOpposite.unop (φ (γ i)) * a⁻¹) :
    ∃ w : π ⁻¹' {y}, hπ.fundamentalGroupToMulOpposite w = φ := by
  refine ⟨hπ.toPermFiber y a⁻¹ u, MonoidHom.eq_of_eqOn_dense hγ ?_⟩
  rintro _ ⟨i, rfl⟩
  rw [hπ.fundamentalGroupToMulOpposite_toPermFiber, h i]
  simp [mul_assoc]

theorem b65u_basepoint_adjust_aux {X U G : Type} [TopologicalSpace X] [TopologicalSpace U]
    [Group G] [MulAction G U] (π : U → X) (hπ : IsQuotientCoveringMap π G)
    {y y' : X} (β : Path y y') (u : π ⁻¹' {y}) :
    ∃ u' : π ⁻¹' {y'}, ∀ η : Path y y,
      hπ.fundamentalGroupToMulOpposite u'
          (FundamentalGroup.fromPath ⟦β.symm.trans (η.trans β)⟧) =
        hπ.fundamentalGroupToMulOpposite u (FundamentalGroup.fromPath ⟦η⟧) := by
  refine ⟨hπ.isCoveringMap.monodromy (.mk β) u, fun η ↦ ?_⟩
  rw [hπ.fundamentalGroupToMulOpposite_apply_eq_iff]
  have hb : hπ.isCoveringMap.monodromy (.mk β.symm)
      (hπ.isCoveringMap.monodromy (.mk β) u) = u := by
    rw [← IsCoveringMap.monodromy_trans_apply, Path.Homotopic.Quotient.mk_symm,
      Path.Homotopic.Quotient.trans_symm, IsCoveringMap.monodromy_refl]; rfl
  have hk := hπ.unop_fundamentalGroupToMulOpposite_smul (e := u)
    (γ := FundamentalGroup.fromPath (.mk η))
  change _ = (hπ.isCoveringMap.monodromy (Path.Homotopic.Quotient.mk (β.symm.trans (η.trans β)))
    (hπ.isCoveringMap.monodromy (.mk β) u) : U)
  rw [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_trans,
    IsCoveringMap.monodromy_trans_apply, IsCoveringMap.monodromy_trans_apply, hb]
  have he : hπ.isCoveringMap.monodromy (.mk η) u = hπ.toPermFiber y
      (hπ.fundamentalGroupToMulOpposite u (FundamentalGroup.fromPath (.mk η))).unop u :=
    Subtype.ext (by rw [hπ.toPermFiber_apply_apply_coe]; exact hk.symm)
  rw [he, hπ.monodromy_toPermFiber, hπ.toPermFiber_apply_apply_coe]
  rfl

end HodgeLean.Foundations.Program
