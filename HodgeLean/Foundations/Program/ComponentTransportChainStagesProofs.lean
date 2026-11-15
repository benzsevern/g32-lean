import HodgeLean.Foundations.Program.ComponentTransportNormalized

/-! # Proof obligations for the chain stages S4 and S5 -/
noncomputable section
open Set Manifold Filter Topology HodgeLean.Papers
open scoped ContDiff
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

theorem b65v_relabel_map_exists_aux (p : Fin 12 → ℂ) (hc : b65z_centre p ∈ b6_chart) :
    ∃ M : OnePoint ℂ ≃ₜ OnePoint ℂ,
      (∀ z : ℂ, M z = ((b65z_centre p 8 * (1 - z) : ℂ) : OnePoint ℂ)) ∧
      M OnePoint.infty = OnePoint.infty := by
  have h8 : b65z_centre p 8 ≠ 0 := by
    intro hz
    have he : b6_branch (b65z_centre p) 8 = b6_branch (b65z_centre p) 10 := by
      change ((b65z_centre p 8 : ℂ) : OnePoint ℂ) = ((0 : ℂ) : OnePoint ℂ)
      exact congrArg (fun z : ℂ ↦ (z : OnePoint ℂ)) hz
    have hbad := hc he
    norm_num at hbad
  let A : ℂ ≃ₜ ℂ := (Homeomorph.neg ℂ).trans
    ((Homeomorph.addLeft (1 : ℂ)).trans (Homeomorph.mulLeft₀ (b65z_centre p 8) h8))
  refine ⟨A.onePointCongr, ?_, rfl⟩
  intro z
  change ((b65z_centre p 8 * (1 + -z) : ℂ) : OnePoint ℂ) = _
  rw [sub_eq_add_neg]

theorem b65v_hmon_of_values_aux {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (R : rf8_SharedFamily) (v₀ : R.atlas.π ⁻¹' {b63gP_basePoint})
    (hroot : ∀ i, R.atlas.hπ.fundamentalGroupToMulOpposite v₀ (b63gP_loops i) =
      MulOpposite.op (b4b_root i))
    (Ψ : b6t_punctured mr_base ≃ₜ b6t_punctured c)
    (w₁ : D.atlas.π ⁻¹' {Ψ b63gP_basePoint}) (a : b4b_Group)
    (h : ∀ k, MulOpposite.unop ((D.atlas.hπ.fundamentalGroupToMulOpposite w₁)
        (FundamentalGroup.map ⟨Ψ, Ψ.continuous⟩ b63gP_basePoint (b63gP_loops k))) =
      a * b4b_root k * a⁻¹) :
    ∃ w : D.atlas.π ⁻¹' {Ψ b63gP_basePoint},
      (D.atlas.hπ.fundamentalGroupToMulOpposite w).comp
        (FundamentalGroup.map ⟨Ψ, Ψ.continuous⟩ b63gP_basePoint) =
      R.atlas.hπ.fundamentalGroupToMulOpposite v₀ := by
  obtain ⟨χ, hχ⟩ := RiemannRochTop_homeomorph_pi1_map Ψ b63gP_basePoint
  have hmap : FundamentalGroup.map ⟨Ψ, Ψ.continuous⟩ b63gP_basePoint = χ.toMonoidHom := by
    apply MonoidHom.ext
    intro b
    obtain ⟨η, hη⟩ := Quotient.exists_rep b.asHom
    have hb : b = FundamentalGroup.fromPath ⟦η⟧ := by
      rw [show (⟦η⟧ : Path.Homotopic.Quotient _ _) = b.asHom from hη]
    change _ = χ b
    rw [hb, hχ]
    rfl
  let γ := fun k ↦ χ (b63gP_loops k)
  have hγ : Subgroup.closure (Set.range γ) = ⊤ := by
    rw [show Set.range γ = χ.toMonoidHom '' Set.range b63gP_loops from
      Set.range_comp χ b63gP_loops]
    rw [← MonoidHom.map_closure, b65u_loops_closure,
      Subgroup.map_top_of_surjective _ χ.surjective]
  let φ := (R.atlas.hπ.fundamentalGroupToMulOpposite v₀).comp χ.symm.toMonoidHom
  obtain ⟨w, hw⟩ := b65u_lift_adjust D.atlas.π D.atlas.hπ
    (Ψ b63gP_basePoint) w₁ γ hγ φ a (by
      intro k
      simpa only [γ, φ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        χ.symm_apply_apply, hroot, MulOpposite.unop_op, hmap] using h k)
  refine ⟨w, ?_⟩
  rw [hw, hmap]
  apply MonoidHom.ext
  intro b
  exact congrArg (R.atlas.hπ.fundamentalGroupToMulOpposite v₀) (χ.symm_apply_apply b)

theorem b65v_chain_of_normalized_path_aux (p : Fin 12 → ℂ)
    (g : Fin 13 → b4b_Group) (D : b65z_SharedFamily (b65z_centre p) g)
    (e : b65s_sphere ≃ₜ b6t_punctured (b65z_centre p))
    (x : b65s_regular) (u₀ : D.atlas.π ⁻¹' {e (b65s_inclusion x)})
    (δ : Fin 13 → Path x x)
    (hmono : ∀ i, ((D.atlas.hπ.fundamentalGroupToMulOpposite u₀).comp
        (FundamentalGroup.map ((⟨e, e.continuous⟩ :
          C(b65s_sphere, b6t_punctured (b65z_centre p))).comp b65s_inclusion) x))
          (FundamentalGroup.fromPath ⟦δ i⟧) = MulOpposite.op (b65b_initial i)⁻¹)
    (R : rf8_SharedFamily)
    (v₀ : R.atlas.π ⁻¹' {b63gP_basePoint})
    (hroot : ∀ i, R.atlas.hπ.fundamentalGroupToMulOpposite v₀ (b63gP_loops i) =
      MulOpposite.op (b4b_root i))
    (hpath : ∀ M : OnePoint ℂ ≃ₜ OnePoint ℂ,
      (∀ z : ℂ, M z = ((b65z_centre p 8 * (1 - z) : ℂ) : OnePoint ℂ)) →
      M OnePoint.infty = OnePoint.infty →
      ∃ γ : C(unitInterval, Fin 10 → ℂ), (∀ τ, γ τ ∈ b6_chart) ∧ γ 0 = mr_base ∧
        γ 1 = b65v_relabelCentre p ∧
        ∀ N : ℕ, 0 < N →
          (∀ k < N, b65y_sample γ N (k + 1) ∈ b6t_polydisc (b65y_sample γ N k)) →
          ∀ Ψ : b6t_punctured mr_base ≃ₜ b6t_punctured (b65z_centre p),
            (∀ z, (Ψ z : OnePoint ℂ) = M (b65y_radial (b65y_sample γ N) N z)) →
            (∀ j, M (b65y_radial (b65y_sample γ N) N (b6_branch mr_base (b65u_endpointPerm j))) =
              b6_branch (b65z_centre p) j) ∧
            ∃ β : Path (Ψ b63gP_basePoint) (e (b65s_inclusion x)),
              ∀ ρ : (FundamentalGroup (b6t_punctured (b65z_centre p)) (e (b65s_inclusion x)))ᵐᵒᵖ →*
                  b4b_Group,
                b65s_word b65b_word (fun k ↦ ρ (MulOpposite.op
                  (FundamentalGroup.fundamentalGroupMulEquivOfPath β
                    (FundamentalGroup.map ⟨Ψ, Ψ.continuous⟩ b63gP_basePoint
                      (MulOpposite.unop (b66h_loop k)))))) =
                b65s_word b65b_pathWord (fun j ↦ (ρ (MulOpposite.op
                  (FundamentalGroup.map ((⟨e, e.continuous⟩ :
                    C(b65s_sphere, b6t_punctured (b65z_centre p))).comp b65s_inclusion) x
                    (FundamentalGroup.fromPath ⟦δ j⟧))))⁻¹)) :
    ∃ H : b65y_UnlabelledHurwitzChain,
      H.chart 0 = (⟨mr_base, b4b_root, b65z_ofRetained R⟩ : b65y_Chart) ∧
      H.chart (Fin.last H.n) = (⟨b65z_centre p, g, D⟩ : b65y_Chart) := by
  obtain ⟨M, hMz, hMinf⟩ := b65v_relabel_map_exists_aux p D.atlas.hb
  obtain ⟨_, _, hM, hM', hMc⟩ := b65v_relabel_normalization p D.atlas.hb M hMz hMinf
  obtain ⟨γ, hγ, hγ0, hγ1, htransport⟩ := hpath M hMz hMinf
  apply b65u_chain_unlabelled_of_path p g D R v₀ (b65v_relabelCentre p)
    γ hγ hγ0 hγ1 M hM hM' hMc
  intro N hN hc Ψ hΨ
  obtain ⟨_, β, hword⟩ := htransport N hN hc Ψ hΨ
  obtain ⟨w₁, a, ha⟩ := b65v_generator_values D (e (b65s_inclusion x)) u₀
    (fun j ↦ FundamentalGroup.map ((⟨e, e.continuous⟩ :
      C(b65s_sphere, b6t_punctured (b65z_centre p))).comp b65s_inclusion) x
      (FundamentalGroup.fromPath ⟦δ j⟧)) hmono Ψ β hword
  exact b65v_hmon_of_values_aux D R v₀ hroot Ψ w₁ a ha

end HodgeLean.Foundations.Program
