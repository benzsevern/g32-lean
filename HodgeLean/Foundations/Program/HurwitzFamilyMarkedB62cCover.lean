import HodgeLean.Foundations.Program.HurwitzFamilyMarkedDefs

noncomputable section

namespace HodgeLean.Foundations.Program

open Filter Topology
open scoped Topology

theorem b6m_localHomeomorph_locallyPathConnected {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [LocallyPathConnectedSpace Y]
    {f : X → Y} (hf : IsLocalHomeomorph f) : LocallyPathConnectedSpace X := by
  constructor
  intro x
  rw [hasBasis_self]
  intro N hN
  obtain ⟨e, hx, _⟩ := hf x
  have hpre : e.symm ⁻¹' N ∈ 𝓝 (e x) := by
    have h := (e.continuousAt_symm (e.map_source hx)).preimage_mem_nhds
      (by simpa only [e.left_inv hx] using hN)
    exact h
  obtain ⟨V, ⟨hV, hVc⟩, hVN⟩ := (path_connected_basis (e x)).mem_iff.mp
    (inter_mem (e.open_target.mem_nhds (e.map_source hx)) hpre)
  refine ⟨e.symm '' V, ?_, ?_, ?_⟩
  · simpa only [e.left_inv hx] using e.symm.image_mem_nhds (e.map_source hx) hV
  · exact hVc.image' (e.continuousOn_symm.mono (fun y hy ↦ (hVN hy).1))
  · rintro z ⟨y, hy, rfl⟩
    exact (hVN hy).2

theorem b6m_based_cover_ranges_eq {X U W G : Type}
    [TopologicalSpace X] [TopologicalSpace U] [TopologicalSpace W]
    [Group G] [MulAction G U] [MulAction G W]
    {π : U → X} {ρ : W → X}
    (hπ : IsQuotientCoveringMap π G) (hρ : IsQuotientCoveringMap ρ G)
    {x : X} (u : π ⁻¹' {x}) (w : ρ ⁻¹' {x})
    (h : hπ.fundamentalGroupToMulOpposite u = hρ.fundamentalGroupToMulOpposite w) :
    (FundamentalGroup.mapOfEq ⟨π, hπ.continuous⟩ u.property).range =
      (FundamentalGroup.mapOfEq ⟨ρ, hρ.continuous⟩ w.property).range := by
  rw [← hπ.ker_monodromyPerm u, ← hρ.ker_monodromyPerm w,
    ← hπ.ker_fundamentalGroupToMulOpposite u,
    ← hρ.ker_fundamentalGroupToMulOpposite w, h]

theorem b6m_based_cover_lift {X U W G : Type}
    [TopologicalSpace X] [TopologicalSpace U] [TopologicalSpace W]
    [LocallyPathConnectedSpace X] [ConnectedSpace U]
    [Group G] [MulAction G U] [MulAction G W]
    {π : U → X} {ρ : W → X}
    (hπ : IsQuotientCoveringMap π G) (hρ : IsQuotientCoveringMap ρ G)
    {x : X} (u : π ⁻¹' {x}) (w : ρ ⁻¹' {x})
    (h : hπ.fundamentalGroupToMulOpposite u = hρ.fundamentalGroupToMulOpposite w) :
    ∃! a : C(U, W), a u.val = w.val ∧ ρ ∘ a = π := by
  haveI : LocallyPathConnectedSpace U :=
    b6m_localHomeomorph_locallyPathConnected hπ.isCoveringMap.isLocalHomeomorph
  haveI : PathConnectedSpace U := PathConnectedSpace.of_locallyPathConnectedSpace
  have hr := b6m_based_cover_ranges_eq hπ hρ u w h
  rcases u with ⟨u, hu⟩
  change π u = x at hu
  subst x
  apply hρ.isCoveringMap.existsUnique_continuousMap_lifts_of_range_le
    (f := ⟨π, hπ.continuous⟩) (a₀ := u) (e₀ := w.val) w.property
  have heq : FundamentalGroup.mapOfEq ⟨π, hπ.continuous⟩ (show π u = π u from rfl) =
      FundamentalGroup.map ⟨π, hπ.continuous⟩ u := by
    ext z
    simp [FundamentalGroup.mapOfEq, CategoryTheory.Iso.conj]
  rw [heq] at hr
  exact hr.le

theorem b6m_based_cover_homeomorph {X U W G : Type}
    [TopologicalSpace X] [TopologicalSpace U] [TopologicalSpace W]
    [LocallyPathConnectedSpace X] [ConnectedSpace U] [ConnectedSpace W]
    [Group G] [MulAction G U] [MulAction G W]
    {π : U → X} {ρ : W → X}
    (hπ : IsQuotientCoveringMap π G) (hρ : IsQuotientCoveringMap ρ G)
    {x : X} (u : π ⁻¹' {x}) (w : ρ ⁻¹' {x})
    (h : hπ.fundamentalGroupToMulOpposite u = hρ.fundamentalGroupToMulOpposite w) :
    ∃ a : U ≃ₜ W, a u.val = w.val ∧ (∀ z, ρ (a z) = π z) ∧
      ∀ a' : C(U, W), a' u.val = w.val → (∀ z, ρ (a' z) = π z) →
        ∀ z, a' z = a z := by
  obtain ⟨a, ⟨hau, ha⟩, hua⟩ := b6m_based_cover_lift hπ hρ u w h
  obtain ⟨c, ⟨hcw, hc⟩, _⟩ := b6m_based_cover_lift hρ hπ w u h.symm
  have hca : ∀ z, c (a z) = z := by
    have he := hπ.isCoveringMap.eq_of_comp_eq (c.continuous.comp a.continuous)
      continuous_id (by
        funext z
        exact (congrFun hc (a z)).trans (congrFun ha z)) u.val (by simp [hau, hcw])
    exact congrFun he
  have hac : ∀ z, a (c z) = z := by
    have he := hρ.isCoveringMap.eq_of_comp_eq (a.continuous.comp c.continuous)
      continuous_id (by
        funext z
        exact (congrFun ha (c z)).trans (congrFun hc z)) w.val (by simp [hau, hcw])
    exact congrFun he
  let e : U ≃ₜ W :=
    { toFun := a
      invFun := c
      left_inv := hca
      right_inv := hac
      continuous_toFun := a.continuous
      continuous_invFun := c.continuous }
  refine ⟨e, hau, congrFun ha, ?_⟩
  intro a' ha'u ha'p z
  exact DFunLike.congr_fun (hua a' ⟨ha'u, funext ha'p⟩) z

theorem b6m_based_cover_map_equivariant {X U W G : Type}
    [TopologicalSpace X] [TopologicalSpace U] [TopologicalSpace W]
    [LocallyPathConnectedSpace X] [ConnectedSpace U]
    [Group G] [MulAction G U] [MulAction G W]
    {π : U → X} {ρ : W → X}
    (hπ : IsQuotientCoveringMap π G) (hρ : IsQuotientCoveringMap ρ G)
    {x : X} (u : π ⁻¹' {x}) (w : ρ ⁻¹' {x})
    (h : hπ.fundamentalGroupToMulOpposite u = hρ.fundamentalGroupToMulOpposite w)
    (a : C(U, W)) (hau : a u.val = w.val) (ha : ∀ z, ρ (a z) = π z) :
    ∀ (g : G) (z : U), a (g • z) = g • a z := by
  haveI : LocallyPathConnectedSpace U :=
    b6m_localHomeomorph_locallyPathConnected hπ.isCoveringMap.isLocalHomeomorph
  haveI : PathConnectedSpace U := PathConnectedSpace.of_locallyPathConnectedSpace
  intro g
  let Γ : Path u.val (g • u.val) := PathConnectedSpace.somePath _ _
  let γ : Path x x := (Γ.map hπ.continuous).cast u.property.symm
    ((hπ.map_smul g).trans u.property).symm
  have hΓ : π ∘ Γ = γ := rfl
  have hm : hπ.fundamentalGroupToMulOpposite u (.of (.mk γ)) = MulOpposite.op g :=
    hπ.fundamentalGroupToMulOpposite_apply_mk_eq hΓ Γ.source Γ.target
  rw [h] at hm
  have hstart : (a.comp Γ.toContinuousMap) 0 = w.val := by
    change a (Γ 0) = w.val
    rw [Γ.source, hau]
  have hlift : ρ ∘ a.comp Γ.toContinuousMap = γ := by
    funext t
    exact ha (Γ t)
  have hend : g • w.val = a (g • u.val) := by
    have hh := (hρ.fundamentalGroupToMulOpposite_apply_eq_iff).mp hm
    rw [hρ.isCoveringMap.monodromy_eq_apply_one hlift hstart] at hh
    change g • w.val = a (Γ 1) at hh
    simpa only [Γ.target] using hh
  have he := hρ.isCoveringMap.eq_of_comp_eq
    (a.continuous.comp (hπ.continuous_const_smul g))
    ((hρ.continuous_const_smul g).comp a.continuous)
    (by funext z; simp only [Function.comp_apply, ha, hπ.map_smul, hρ.map_smul])
    u.val (by
      change a (g • u.val) = g • a u.val
      rw [hau]
      exact hend.symm)
  exact congrFun he

theorem b6m_based_cover_equivariant_homeomorph {X U W G : Type}
    [TopologicalSpace X] [TopologicalSpace U] [TopologicalSpace W]
    [LocallyPathConnectedSpace X] [ConnectedSpace U] [ConnectedSpace W]
    [Group G] [MulAction G U] [MulAction G W]
    {π : U → X} {ρ : W → X}
    (hπ : IsQuotientCoveringMap π G) (hρ : IsQuotientCoveringMap ρ G)
    {x : X} (u : π ⁻¹' {x}) (w : ρ ⁻¹' {x})
    (h : hπ.fundamentalGroupToMulOpposite u = hρ.fundamentalGroupToMulOpposite w) :
    ∃ a : U ≃ₜ W, a u.val = w.val ∧ (∀ z, ρ (a z) = π z) ∧
      (∀ (g : G) (z : U), a (g • z) = g • a z) ∧
      ∀ a' : C(U, W), a' u.val = w.val → (∀ z, ρ (a' z) = π z) →
        ∀ z, a' z = a z := by
  obtain ⟨a, hau, ha, huniq⟩ := b6m_based_cover_homeomorph hπ hρ u w h
  exact ⟨a, hau, ha,
    b6m_based_cover_map_equivariant hπ hρ u w h ⟨a, a.continuous⟩ hau ha, huniq⟩

attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

theorem b6m_punctured_based_comparison (b : Fin 10 → ℂ) {U W G : Type}
    [TopologicalSpace U] [TopologicalSpace W] [ConnectedSpace U] [ConnectedSpace W]
    [Group G] [MulAction G U] [MulAction G W]
    {π : U → b6t_punctured b} {ρ : W → b6t_punctured b}
    (hπ : IsQuotientCoveringMap π G) (hρ : IsQuotientCoveringMap ρ G)
    {x : b6t_punctured b} (u : π ⁻¹' {x}) (w : ρ ⁻¹' {x})
    (h : hπ.fundamentalGroupToMulOpposite u = hρ.fundamentalGroupToMulOpposite w) :
    ∃ a : U ≃ₜ W, a u.val = w.val ∧ (∀ z, ρ (a z) = π z) ∧
      (∀ (g : G) (z : U), a (g • z) = g • a z) ∧
      ∀ a' : C(U, W), a' u.val = w.val → (∀ z, ρ (a' z) = π z) →
        ∀ z, a' z = a z := by
  haveI : LocallyPathConnectedSpace (OnePoint ℂ) :=
    ChartedSpace.locallyPathConnectedSpace ℂ (OnePoint ℂ)
  haveI : LocallyPathConnectedSpace (b6t_punctured b) :=
    (Set.finite_range (b6_branch b)).isClosed.isOpen_compl.locallyPathConnectedSpace
  exact b6m_based_cover_equivariant_homeomorph hπ hρ u w h

end HodgeLean.Foundations.Program
