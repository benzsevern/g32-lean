import HodgeLean.Foundations.Program.RelativeTorusKernelDefs

/-! # Track B2: topology and complex structure of the fibre torus

Helper lemmas for the topological statements of `RelativeTorusKernel.lean`. The key fact is that a
local section `σ` of the quotient map `G → G ⧸ Γ` by a discrete subgroup is, near each point,
`w ↦ w + c` for a fixed `c ∈ Γ` (`b2t_eventually_symm_mk`). Hence the charts of
`b2_torus_chartedSpace` differ by translations, and the covering map and the morphisms of tori are
affine in charts.
-/

noncomputable section

open CategoryTheory Manifold Filter Topology Set
open scoped TensorProduct ContDiff

namespace HodgeLean.Foundations.Program


/-- A local section of the quotient map by a discrete subgroup `Γ` is, near each point of its
domain, a translation by a fixed element of `Γ`. -/
theorem b2t_eventually_symm_mk {G : Type*} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] (Γ : AddSubgroup G) [DiscreteTopology Γ]
    (σ : OpenPartialHomeomorph G (G ⧸ Γ)) (hσ : ⇑σ = QuotientAddGroup.mk)
    {w₀ : G} (hw₀ : (w₀ : G ⧸ Γ) ∈ σ.target) :
    ∃ c ∈ Γ, ∀ᶠ w in 𝓝 w₀, σ.symm (QuotientAddGroup.mk w : G ⧸ Γ) = w + c := by
  set h : G → G := fun w ↦ σ.symm (QuotientAddGroup.mk w : G ⧸ Γ) - w with hh
  have hmk : Continuous (QuotientAddGroup.mk : G → G ⧸ Γ) := continuous_quotient_mk'
  have hmem : ∀ᶠ w in 𝓝 w₀, (QuotientAddGroup.mk w : G ⧸ Γ) ∈ σ.target :=
    hmk.continuousAt.preimage_mem_nhds (σ.open_target.mem_nhds hw₀)
  have hΓ : ∀ w : G, (QuotientAddGroup.mk w : G ⧸ Γ) ∈ σ.target → h w ∈ Γ := by
    intro w hw
    have h1 := σ.right_inv hw
    rw [hσ] at h1
    have h2 := (QuotientAddGroup.eq (s := Γ)).1 h1.symm
    simpa [hh, sub_eq_neg_add] using h2
  have hcont : ContinuousAt h w₀ :=
    ((σ.continuousAt_symm hw₀).comp hmk.continuousAt).sub continuousAt_id
  have h₀ := hΓ w₀ hw₀
  obtain ⟨V, hV, hVeq⟩ := isOpen_induced_iff.1 (isOpen_discrete ({⟨h w₀, h₀⟩} : Set Γ))
  have hVmem : h w₀ ∈ V := by
    have : (⟨h w₀, h₀⟩ : Γ) ∈ Subtype.val ⁻¹' V := by rw [hVeq]; rfl
    exact this
  refine ⟨h w₀, h₀, ?_⟩
  filter_upwards [hmem, hcont.preimage_mem_nhds (hV.mem_nhds hVmem)] with w hw hwV
  have : (⟨h w, hΓ w hw⟩ : Γ) ∈ Subtype.val ⁻¹' V := hwV
  rw [hVeq] at this
  have e : h w = h w₀ := congrArg Subtype.val (Set.mem_singleton_iff.1 this)
  rw [← e]; simp only [hh]; abel

section Torus

variable {Λ : Type*} [AddCommGroup Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ))

/-- `(ℂ ⊗ Λ) ⧸ F` is Hausdorff for finite `Λ`: it is homeomorphic to `ℂ^g`. -/
theorem b2t_quot_t2Space [Module.Finite ℤ Λ] : T2Space ((ℂ ⊗[ℤ] Λ) ⧸ F) :=
  (b2_coordHomeomorph Λ F).symm.t2Space

/-- The torus of a finite lattice with discrete image is Hausdorff: it is the quotient of a
Hausdorff group by a discrete subgroup. -/
theorem b2t_torus_t2Space [Module.Finite ℤ Λ] [DiscreteTopology (b2_latticeMap Λ F).range] :
    T2Space (b2_torus Λ F) := by
  have := b2t_quot_t2Space F
  have : IsClosed ((b2_latticeMap Λ F).range : Set ((ℂ ⊗[ℤ] Λ) ⧸ F)) :=
    AddSubgroup.isClosed_of_discreteTopology
  infer_instance

/-- The cover `ℂ^g → T` is a covering map: Mathlib's quotient covering composed with linear
coordinates. -/
theorem b2t_torusCover_isCoveringMap [Module.Finite ℤ Λ]
    [DiscreteTopology (b2_latticeMap Λ F).range] : IsCoveringMap (b2_torusCover Λ F) :=
  (AddSubgroup.isAddQuotientCoveringMap_of_comm (b2_latticeMap Λ F).range
    (SetLike.isDiscrete_iff_discreteTopology.2 inferInstance)).isCoveringMap.comp_homeomorph
    (b2_coordHomeomorph Λ F).symm

/-- The inverse of a chart of the torus is the quotient map in linear coordinates. -/
theorem b2t_torusChart_symm_apply [Module.Finite ℤ Λ] [DiscreteTopology (b2_latticeMap Λ F).range]
    (t : b2_torus Λ F) (y) :
    (b2_torusChart Λ F t).symm y = QuotientAddGroup.mk ((b2_coordHomeomorph Λ F).symm y) := by
  have h := (Classical.choose_spec (b2_isLocalHomeomorph_mk Λ F t.out)).2
  simp only [b2_torusChart, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.symm_symm, OpenPartialHomeomorph.coe_trans, Function.comp_apply,
    Homeomorph.toOpenPartialHomeomorph_symm_apply]
  rw [← h]

/-- Near a point where it is defined, a chart of the torus applied to `[f x]` is `coord (f x)` plus
a constant. -/
theorem b2t_torusChart_eventually [Module.Finite ℤ Λ] [DiscreteTopology (b2_latticeMap Λ F).range]
    (t : b2_torus Λ F) {X : Type*} [TopologicalSpace X] {f : X → (ℂ ⊗[ℤ] Λ) ⧸ F} {x₀ : X}
    (hf : ContinuousAt f x₀)
    (hx₀ : (QuotientAddGroup.mk (f x₀) : b2_torus Λ F) ∈ (b2_torusChart Λ F t).source) :
    ∃ a, ∀ᶠ x in 𝓝 x₀, b2_torusChart Λ F t (QuotientAddGroup.mk (f x)) =
      b2_coord _ (f x) + a := by
  set σ := Classical.choose (b2_isLocalHomeomorph_mk Λ F t.out)
  have hσ : ⇑σ = QuotientAddGroup.mk :=
    (Classical.choose_spec (b2_isLocalHomeomorph_mk Λ F t.out)).2.symm
  have hsrc : (b2_torusChart Λ F t).source = σ.target := by
    simp [b2_torusChart, σ]
  rw [hsrc] at hx₀
  obtain ⟨c, -, hc⟩ := b2t_eventually_symm_mk _ σ hσ hx₀
  refine ⟨b2_coord _ c, ?_⟩
  filter_upwards [hf.eventually hc] with x hx
  simp only [b2_torusChart, OpenPartialHomeomorph.coe_trans, Function.comp_apply,
    Homeomorph.toOpenPartialHomeomorph_apply]
  rw [← map_add, ← hx]
  rfl

/-- The torus is a complex manifold: its chart transitions are locally translations. -/
theorem b2t_isManifold [Module.Finite ℤ Λ] [DiscreteTopology (b2_latticeMap Λ F).range] :
    IsManifold 𝓘(ℂ, Fin (Module.finrank ℂ ((ℂ ⊗[ℤ] Λ) ⧸ F)) → ℂ) ω (b2_torus Λ F) := by
  apply isManifold_of_contDiffOn
  rintro e e' ⟨t, rfl⟩ ⟨t', rfl⟩
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.range_id,
    Set.preimage_id, Set.inter_univ, Function.id_comp, Function.comp_id]
  intro y hy
  have hy' : y ∈ (b2_torusChart Λ F t).target ∧
      (b2_torusChart Λ F t).symm y ∈ (b2_torusChart Λ F t').source := by
    simpa [OpenPartialHomeomorph.trans_source] using hy
  rw [b2t_torusChart_symm_apply] at hy'
  obtain ⟨a, ha⟩ := b2t_torusChart_eventually F t'
    (b2_coordHomeomorph Λ F).symm.continuous.continuousAt hy'.2
  refine ContDiffAt.contDiffWithinAt ?_
  have : (fun y ↦ y + a) =ᶠ[𝓝 y] ((b2_torusChart Λ F t).symm ≫ₕ b2_torusChart Λ F t') := by
    filter_upwards [ha] with z hz
    simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply, b2t_torusChart_symm_apply, hz]
    congr 1
    exact ((b2_coordHomeomorph Λ F).apply_symm_apply z).symm
  exact (contDiffAt_id.add contDiffAt_const).congr_of_eventuallyEq this.symm

/-- The cover `ℂ^g → T` is holomorphic: in charts it is locally a translation. -/
theorem b2t_torusCover_contMDiff [Module.Finite ℤ Λ] [DiscreteTopology (b2_latticeMap Λ F).range] :
    ContMDiff 𝓘(ℂ, Fin (Module.finrank ℂ ((ℂ ⊗[ℤ] Λ) ⧸ F)) → ℂ)
      𝓘(ℂ, Fin (Module.finrank ℂ ((ℂ ⊗[ℤ] Λ) ⧸ F)) → ℂ) ω (b2_torusCover Λ F) := by
  intro v
  rw [contMDiffAt_iff]
  refine ⟨(continuous_quotient_mk'.comp (b2_coordHomeomorph Λ F).symm.continuous).continuousAt,
    ?_⟩
  simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_symm, PartialEquiv.refl_coe,
    Function.comp_id, extChartAt_coe, modelWithCornersSelf_coe, Function.id_comp, Set.range_id,
    id_eq, contDiffWithinAt_univ]
  obtain ⟨a, ha⟩ := b2t_torusChart_eventually F (b2_torusCover Λ F v)
    (b2_coordHomeomorph Λ F).symm.continuous.continuousAt
    (mem_chart_source (Fin (Module.finrank ℂ ((ℂ ⊗[ℤ] Λ) ⧸ F)) → ℂ) (b2_torusCover Λ F v))
  have : (fun y ↦ y + a) =ᶠ[𝓝 v] (chartAt (Fin (Module.finrank ℂ ((ℂ ⊗[ℤ] Λ) ⧸ F)) → ℂ)
      (b2_torusCover Λ F v) ∘ b2_torusCover Λ F) := by
    filter_upwards [ha] with z hz
    simp only [Function.comp_apply, b2_torusCover]
    erw [hz]
    congr 1
    exact ((b2_coordHomeomorph Λ F).apply_symm_apply z).symm
  exact (contDiffAt_id.add contDiffAt_const).congr_of_eventuallyEq this.symm

end Torus

section Hom

variable {Λ Λ' : Type*} [AddCommGroup Λ] [AddCommGroup Λ']

/-- The morphism of tori induced by a lattice map is continuous. -/
theorem b2t_torusHom_continuous (F' : Submodule ℂ (ℂ ⊗[ℤ] Λ')) (F : Submodule ℂ (ℂ ⊗[ℤ] Λ))
    (g : Λ' →+ Λ) (hg : F' ≤ F.comap (b2_cplxMap g)) :
    Continuous (b2_torusHom F' F g hg) := by
  refine (QuotientAddGroup.isQuotientMap_mk _).continuous_iff.2 ?_
  exact continuous_quotient_mk'.comp
    (IsModuleTopology.continuous_of_linearMap (F'.mapQ F (b2_cplxMap g) hg))

/-- The morphism of tori induced by a lattice map is holomorphic: in charts it is affine. -/
theorem b2t_torusHom_contMDiff [Module.Finite ℤ Λ'] [Module.Finite ℤ Λ]
    (F' : Submodule ℂ (ℂ ⊗[ℤ] Λ')) (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (g : Λ' →+ Λ)
    (hg : F' ≤ F.comap (b2_cplxMap g)) [DiscreteTopology (b2_latticeMap Λ' F').range]
    [DiscreteTopology (b2_latticeMap Λ F).range] :
    ContMDiff 𝓘(ℂ, Fin (Module.finrank ℂ ((ℂ ⊗[ℤ] Λ') ⧸ F')) → ℂ)
      𝓘(ℂ, Fin (Module.finrank ℂ ((ℂ ⊗[ℤ] Λ) ⧸ F)) → ℂ) ω (b2_torusHom F' F g hg) := by
  intro t
  rw [contMDiffAt_iff]
  refine ⟨(b2t_torusHom_continuous F' F g hg).continuousAt, ?_⟩
  simp only [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, Function.id_comp, Function.comp_id, Set.range_id,
    contDiffWithinAt_univ]
  set L : (Fin (Module.finrank ℂ ((ℂ ⊗[ℤ] Λ') ⧸ F')) → ℂ) →ₗ[ℂ]
      (Fin (Module.finrank ℂ ((ℂ ⊗[ℤ] Λ) ⧸ F)) → ℂ) :=
    (b2_coord _).toLinearMap ∘ₗ (F'.mapQ F (b2_cplxMap g) hg) ∘ₗ (b2_coord _).symm.toLinearMap
  set f : (Fin (Module.finrank ℂ ((ℂ ⊗[ℤ] Λ') ⧸ F')) → ℂ) → (ℂ ⊗[ℤ] Λ) ⧸ F :=
    fun y ↦ F'.mapQ F (b2_cplxMap g) hg ((b2_coordHomeomorph Λ' F').symm y)
  have hf : Continuous f := (IsModuleTopology.continuous_of_linearMap
    (F'.mapQ F (b2_cplxMap g) hg)).comp (b2_coordHomeomorph Λ' F').symm.continuous
  set y₀ := chartAt (Fin (Module.finrank ℂ ((ℂ ⊗[ℤ] Λ') ⧸ F')) → ℂ) t t
  have hsymm : ∀ y, (chartAt (Fin (Module.finrank ℂ ((ℂ ⊗[ℤ] Λ') ⧸ F')) → ℂ) t).symm y =
      QuotientAddGroup.mk ((b2_coordHomeomorph Λ' F').symm y) :=
    b2t_torusChart_symm_apply F' t
  have hy₀ : (QuotientAddGroup.mk (f y₀) : b2_torus Λ F) =
      b2_torusHom F' F g hg t := by
    have : (chartAt (Fin (Module.finrank ℂ ((ℂ ⊗[ℤ] Λ') ⧸ F')) → ℂ) t).symm y₀ = t :=
      (chartAt _ t).left_inv (mem_chart_source _ t)
    rw [hsymm] at this
    rw [← this]
    rfl
  obtain ⟨a, ha⟩ := b2t_torusChart_eventually F (b2_torusHom F' F g hg t) hf.continuousAt
    (by rw [hy₀]; exact mem_chart_source _ _)
  have : (fun y ↦ L y + a) =ᶠ[𝓝 y₀] (chartAt (Fin (Module.finrank ℂ ((ℂ ⊗[ℤ] Λ) ⧸ F)) → ℂ)
      (b2_torusHom F' F g hg t) ∘ b2_torusHom F' F g hg ∘
        (chartAt (Fin (Module.finrank ℂ ((ℂ ⊗[ℤ] Λ') ⧸ F')) → ℂ) t).symm) := by
    filter_upwards [ha] with z hz
    simp only [Function.comp_apply, hsymm]
    erw [hz]
    rfl
  exact ((LinearMap.toContinuousLinearMap L).contDiff.contDiffAt.add
    contDiffAt_const).congr_of_eventuallyEq this.symm

end Hom

end HodgeLean.Foundations.Program
