import HodgeLean.Foundations.Program.HurwitzPrymDefs

noncomputable section

open Manifold TopologicalSpace Filter Topology
open scoped TensorProduct ContDiff

namespace HodgeLean.Foundations.Program

/-- A complex-linear endomorphism of the standard torus that preserves its lattice is
holomorphic. -/
theorem HurwitzPrymAlg_contMDiff_quotientLinear
    (A : ((ℂ ⊗[ℤ] (Fin 2 → ℤ)) ⧸ b2_stdF) →ₗ[ℂ] ((ℂ ⊗[ℤ] (Fin 2 → ℤ)) ⧸ b2_stdF))
    (hA : (b2_latticeMap (Fin 2 → ℤ) b2_stdF).range ≤
      AddSubgroup.comap A.toAddMonoidHom (b2_latticeMap (Fin 2 → ℤ) b2_stdF).range) :
    ContMDiff 𝓘(ℂ, b3_EllipticModel) 𝓘(ℂ, b3_EllipticModel) ω
      (QuotientAddGroup.map _ _ A.toAddMonoidHom hA) := by
  let f : b3_Elliptic →+ b3_Elliptic := QuotientAddGroup.map _ _ A.toAddMonoidHom hA
  have hf : Continuous f := by
    refine (QuotientAddGroup.isQuotientMap_mk _).continuous_iff.2 ?_
    exact continuous_quotient_mk'.comp (IsModuleTopology.continuous_of_linearMap A)
  intro t
  rw [contMDiffAt_iff]
  refine ⟨hf.continuousAt, ?_⟩
  simp only [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, Function.id_comp, Function.comp_id, Set.range_id,
    contDiffWithinAt_univ]
  let L : b3_EllipticModel →ₗ[ℂ] b3_EllipticModel :=
    (b2_coord _).toLinearMap ∘ₗ A ∘ₗ (b2_coord _).symm.toLinearMap
  let q : b3_EllipticModel → ((ℂ ⊗[ℤ] (Fin 2 → ℤ)) ⧸ b2_stdF) :=
    fun y ↦ A ((b2_coordHomeomorph (Fin 2 → ℤ) b2_stdF).symm y)
  have hq : Continuous q := (IsModuleTopology.continuous_of_linearMap A).comp
    (b2_coordHomeomorph (Fin 2 → ℤ) b2_stdF).symm.continuous
  let y₀ := chartAt b3_EllipticModel t t
  have hsymm : ∀ y, (chartAt b3_EllipticModel t).symm y =
      QuotientAddGroup.mk ((b2_coordHomeomorph (Fin 2 → ℤ) b2_stdF).symm y) :=
    b2t_torusChart_symm_apply b2_stdF t
  have hy₀ : (QuotientAddGroup.mk (q y₀) : b3_Elliptic) = f t := by
    have ht : (chartAt b3_EllipticModel t).symm y₀ = t :=
      (chartAt _ t).left_inv (mem_chart_source _ t)
    rw [hsymm] at ht
    rw [← ht]
    rfl
  obtain ⟨a, ha⟩ := b2t_torusChart_eventually b2_stdF (f t) hq.continuousAt
    (by rw [hy₀]; exact mem_chart_source _ _)
  have heq : (fun y ↦ L y + a) =ᶠ[𝓝 y₀]
      (chartAt b3_EllipticModel (f t) ∘ f ∘ (chartAt b3_EllipticModel t).symm) := by
    filter_upwards [ha] with z hz
    simp only [Function.comp_apply, hsymm]
    erw [hz]
    rfl
  exact ((LinearMap.toContinuousLinearMap L).contDiff.contDiffAt.add
    contDiffAt_const).congr_of_eventuallyEq heq.symm

/-- Multiplication by a power of `i` on the standard elliptic curve is holomorphic. -/
theorem HurwitzPrymAlg_ellipticScale_contMDiff (k : ℕ) :
    ContMDiff 𝓘(ℂ, b3_EllipticModel) 𝓘(ℂ, b3_EllipticModel) ω (b4_ellipticScale k) := by
  exact HurwitzPrymAlg_contMDiff_quotientLinear
    (Complex.I ^ k • (LinearMap.id :
      ((ℂ ⊗[ℤ] (Fin 2 → ℤ)) ⧸ b2_stdF) →ₗ[ℂ] ((ℂ ⊗[ℤ] (Fin 2 → ℤ)) ⧸ b2_stdF)))
    (fun _ hq ↦ b4_I_pow_smul_mem k _ hq)

lemma HurwitzPrymAlg_mfderiv_eq_chart_fderiv
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace M] [ChartedSpace E M]
    {f : M → M} {x : M} (hf : MDifferentiableAt (modelWithCornersSelf ℂ E)
      (modelWithCornersSelf ℂ E) f x) :
    mfderiv (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ E) f x =
      fderiv ℂ (chartAt E (f x) ∘ f ∘ (chartAt E x).symm) (chartAt E x x) := by
  rw [hf.mfderiv_abuse]
  simp only [writtenInExtChartAt, mfld_simps, fderivWithin_univ]
  rfl

/-- The derivative of elliptic scaling is multiplication by the same fourth root of unity. -/
theorem HurwitzPrymAlg_ellipticScale_mfderiv (k : ℕ) (t : b3_Elliptic)
    (v : b3_EllipticModel) :
    mfderiv (modelWithCornersSelf ℂ b3_EllipticModel)
      (modelWithCornersSelf ℂ b3_EllipticModel)
      (b4_ellipticScale k) t v = Complex.I ^ k • v := by
  let A : ((ℂ ⊗[ℤ] (Fin 2 → ℤ)) ⧸ b2_stdF) →ₗ[ℂ] ((ℂ ⊗[ℤ] (Fin 2 → ℤ)) ⧸ b2_stdF) :=
    Complex.I ^ k • LinearMap.id
  let f : b3_Elliptic →+ b3_Elliptic := b4_ellipticScale k
  let L : b3_EllipticModel →ₗ[ℂ] b3_EllipticModel :=
    (b2_coord _).toLinearMap ∘ₗ A ∘ₗ (b2_coord _).symm.toLinearMap
  let q : b3_EllipticModel → ((ℂ ⊗[ℤ] (Fin 2 → ℤ)) ⧸ b2_stdF) :=
    fun y ↦ A ((b2_coordHomeomorph (Fin 2 → ℤ) b2_stdF).symm y)
  have hq : Continuous q := (IsModuleTopology.continuous_of_linearMap A).comp
    (b2_coordHomeomorph (Fin 2 → ℤ) b2_stdF).symm.continuous
  let y₀ := chartAt b3_EllipticModel t t
  have hsymm : ∀ y, (chartAt b3_EllipticModel t).symm y =
      QuotientAddGroup.mk ((b2_coordHomeomorph (Fin 2 → ℤ) b2_stdF).symm y) :=
    b2t_torusChart_symm_apply b2_stdF t
  have hy₀ : (QuotientAddGroup.mk (q y₀) : b3_Elliptic) = f t := by
    have ht : (chartAt b3_EllipticModel t).symm y₀ = t :=
      (chartAt _ t).left_inv (mem_chart_source _ t)
    rw [hsymm] at ht
    rw [← ht]
    rfl
  obtain ⟨a, ha⟩ := b2t_torusChart_eventually b2_stdF (f t) hq.continuousAt
    (by rw [hy₀]; exact mem_chart_source _ _)
  have heq : (fun y ↦ L y + a) =ᶠ[nhds y₀]
      (chartAt b3_EllipticModel (f t) ∘ f ∘ (chartAt b3_EllipticModel t).symm) := by
    filter_upwards [ha] with z hz
    simp only [Function.comp_apply, hsymm]
    erw [hz]
    rfl
  rw [HurwitzPrymAlg_mfderiv_eq_chart_fderiv
    ((HurwitzPrymAlg_ellipticScale_contMDiff k).mdifferentiable (by simp)).mdifferentiableAt]
  rw [← heq.fderiv_eq]
  have hL : fderiv ℂ (fun y ↦ L y + a) y₀ = L.toContinuousLinearMap :=
    ((LinearMap.toContinuousLinearMap L).hasFDerivAt.add_const a).fderiv
  rw [hL]
  change (b2_coord _) (Complex.I ^ k • (b2_coord _).symm v) = Complex.I ^ k • v
  rw [map_smul]
  simp

/-- Scalar multiplication on a positive-dimensional complex vector space remains faithful
after quotienting by a discrete additive subgroup. -/
theorem HurwitzPrymAlg_scalar_eq_of_quotient_maps_eq
    {V : Type*} [TopologicalSpace V] [AddCommGroup V] [Module ℂ V] [Nontrivial V]
    (L : AddSubgroup V) [DiscreteTopology L]
    (hlinear : ∀ v : V, Continuous fun z : ℂ ↦ z • v) (c d : ℂ)
    (h : ∀ q : V, QuotientAddGroup.mk (c • q) =
      (QuotientAddGroup.mk (d • q) : V ⧸ L)) : c = d := by
  have hmem (q : V) : (c - d) • q ∈ L := by
    simpa [sub_smul] using (QuotientAddGroup.eq_iff_sub_mem.mp (h q))
  have hzero (q : V) : (c - d) • q = 0 := by
    let f : ℂ → L := fun z ↦ ⟨z • ((c - d) • q), by
      simpa [smul_smul, mul_comm] using hmem (z • q)⟩
    have hf : Continuous f := (hlinear ((c - d) • q)).subtype_mk _
    have himage : (f '' Set.univ).Subsingleton :=
      (isPreconnected_univ.image f hf.continuousOn).subsingleton
    have heq : f 1 = f 0 := himage ⟨1, Set.mem_univ 1, rfl⟩ ⟨0, Set.mem_univ 0, rfl⟩
    simpa [f] using congrArg Subtype.val heq
  obtain ⟨q, hq⟩ := exists_ne (0 : V)
  rcases smul_eq_zero.mp (hzero q) with hcd | hq'
  · exact sub_eq_zero.mp hcd
  · exact (hq hq').elim

/-- Equality of two elliptic scaling maps determines their fourth-root scalar. -/
theorem HurwitzPrymAlg_ellipticScale_scalar_eq {k l : ℕ}
    (h : ∀ x : b3_Elliptic, b4_ellipticScale k x = b4_ellipticScale l x) :
    Complex.I ^ k = Complex.I ^ l := by
  have hfin : Module.finrank ℂ ((ℂ ⊗[ℤ] (Fin 2 → ℤ)) ⧸ b2_stdF) = 1 := by
    simpa [b3_EllipticModel] using b3_ellipticModel_finrank
  letI : Nontrivial ((ℂ ⊗[ℤ] (Fin 2 → ℤ)) ⧸ b2_stdF) :=
    Module.nontrivial_of_finrank_pos (show 0 < Module.finrank ℂ
      ((ℂ ⊗[ℤ] (Fin 2 → ℤ)) ⧸ b2_stdF) by rw [hfin]; decide)
  apply HurwitzPrymAlg_scalar_eq_of_quotient_maps_eq
    (b2_latticeMap (Fin 2 → ℤ) b2_stdF).range
    (fun v ↦ IsModuleTopology.continuous_of_linearMap
      (LinearMap.toSpanSingleton ℂ _ v))
    (c := Complex.I ^ k) (d := Complex.I ^ l)
  intro q
  have hq := h (QuotientAddGroup.mk q)
  change QuotientAddGroup.mk (Complex.I ^ k • q) =
    QuotientAddGroup.mk (Complex.I ^ l • q) at hq
  exact hq

end HodgeLean.Foundations.Program
