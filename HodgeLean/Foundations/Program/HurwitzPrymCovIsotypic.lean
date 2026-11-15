import HodgeLean.Foundations.Program.HurwitzPrymDefs

set_option maxHeartbeats 400000

/-! # Track B4, lane `b4-cov`: ranks of group-ring elements on isotypic pieces

For a representation `σ` of a finite group on a finite-dimensional complex space and a stable
subspace `W`, the rank of `a = Σ a_g σ(g)` on `W` is `Σ_i m_i(W) rk ρ_i(a)` when `a` kills every
irreducible outside the list `ρ_i`. The proof splits off an irreducible stable subspace with an
averaged (equivariant) projection and uses Schur's lemma on it.
HC no distance; AV milestone no distance.
-/

noncomputable section

namespace HodgeLean.Foundations.Program

section Isotypic

variable {G : Type} [Group G]
variable {M : Type} [AddCommGroup M] [Module ℂ M]
variable (σ : Representation ℂ G M)

/-- The restriction of `σ` to a stable subspace. -/
def b4cov_res (U : Submodule ℂ M) (hU : ∀ g, U ≤ U.comap (σ g)) : Representation ℂ G U :=
  Subrepresentation.toRepresentation (⟨U, fun g _ hv ↦ hU g hv⟩ : Subrepresentation σ)

theorem b4cov_res_apply (U : Submodule ℂ M) (hU : ∀ g, U ≤ U.comap (σ g)) (g : G) (u : U) :
    ((b4cov_res σ U hU g u : U) : M) = σ g u := rfl

/-- `G`-maps into a stable subspace are the intertwining maps into the restriction. -/
def b4cov_homGEquiv {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (U : Submodule ℂ M) (hU : ∀ g, U ≤ U.comap (σ g)) :
    b4_HomG ρ (fun g ↦ σ g) U ≃ₗ[ℂ] Representation.IntertwiningMap ρ (b4cov_res σ U hU) where
  toFun φ := ⟨(φ : V →ₗ[ℂ] M).codRestrict U φ.2.1, fun g ↦ by
    ext v; exact φ.2.2 g v⟩
  invFun ψ := ⟨U.subtype ∘ₗ ψ.toLinearMap, fun v ↦ (ψ v).2, fun g v ↦ by
    change ((ψ (ρ g v) : U) : M) = σ g (ψ v)
    rw [ψ.isIntertwining]; rfl⟩
  map_add' φ ψ := by ext; rfl
  map_smul' c φ := by ext; rfl
  left_inv φ := by ext; rfl
  right_inv ψ := by ext; rfl

theorem b4cov_mul_apply (g h : G) (m : M) : σ g (σ h m) = σ (g * h) m := by
  rw [map_mul]; rfl

/-- **An equivariant projection** onto a stable subspace (averaging a linear projection). -/
theorem b4cov_exists_equivariantProj [Fintype G] (U : Submodule ℂ M) (hU : ∀ g, U ≤ U.comap (σ g)) :
    ∃ P : M →ₗ[ℂ] M, (∀ m, P m ∈ U) ∧ (∀ u ∈ U, P u = u) ∧ ∀ g m, P (σ g m) = σ g (P m) := by
  obtain ⟨U', hU'⟩ := Submodule.exists_isCompl U
  let π := U.projection U' hU'
  have hcard : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  refine ⟨(Fintype.card G : ℂ)⁻¹ • ∑ g, σ g ∘ₗ π ∘ₗ σ g⁻¹, ?_, ?_, ?_⟩
  · intro m
    simp only [LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply]
    exact U.smul_mem _ (U.sum_mem fun g _ ↦ hU g (Submodule.projection_apply_mem hU' _))
  · intro u hu
    have : ∀ g, σ g (π (σ g⁻¹ u)) = u := fun g ↦ by
      rw [Submodule.projection_apply_of_mem_left hU' (hU g⁻¹ hu), b4cov_mul_apply,
        mul_inv_cancel, map_one, Module.End.one_apply]
    simp only [LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply,
      this, Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hcard, one_smul]
  · intro h m
    simp only [LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply,
      map_smul, map_sum]
    congr 1
    refine Fintype.sum_equiv (Equiv.mulLeft h⁻¹) _ _ fun k ↦ ?_
    simp only [Equiv.coe_mulLeft, b4cov_mul_apply, mul_inv_rev, inv_inv, mul_inv_cancel_left]

/-- `a = Σ a_g σ(g)` preserves stable subspaces. -/
theorem b4cov_groupSum_mem [Fintype G] (a : G → ℂ) (U : Submodule ℂ M)
    (hU : ∀ g, U ≤ U.comap (σ g)) (u : M) (hu : u ∈ U) : (∑ g, a g • σ g) u ∈ U := by
  rw [LinearMap.sum_apply]
  exact U.sum_mem fun g _ ↦ U.smul_mem _ (hU g hu)

section Split

variable (U W : Submodule ℂ M) (P : M →ₗ[ℂ] M) (hPU : ∀ m, P m ∈ U) (hPid : ∀ u ∈ U, P u = u)
  (hPσ : ∀ g m, P (σ g m) = σ g (P m)) (hUW : U ≤ W)

include hPU hPid hUW in
theorem b4cov_split_sup : U ⊔ (W ⊓ LinearMap.ker P) = W := by
  apply le_antisymm (sup_le hUW inf_le_left)
  intro w hw
  refine Submodule.mem_sup.2 ⟨P w, hPU w, w - P w, ⟨W.sub_mem hw (hUW (hPU w)), ?_⟩, by abel⟩
  change P (w - P w) = 0
  rw [map_sub, hPid _ (hPU w), sub_self]

include hPid in
theorem b4cov_split_inf : U ⊓ (W ⊓ LinearMap.ker P) = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun m hm ↦ ?_
  obtain ⟨h1, -, h2⟩ := hm
  rw [← hPid m h1]
  exact h2

include hPσ in
theorem b4cov_split_stable (hW : ∀ g, W ≤ W.comap (σ g)) (g : G) :
    W ⊓ LinearMap.ker P ≤ (W ⊓ LinearMap.ker P).comap (σ g) := by
  rintro m ⟨h1, h2⟩
  refine ⟨hW g h1, ?_⟩
  change P (σ g m) = 0
  rw [hPσ, LinearMap.mem_ker.1 h2, map_zero]

include hPU hPid hPσ hUW in
theorem b4cov_split_homG {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [FiniteDimensional ℂ M] (ρ : Representation ℂ G V) :
    Module.finrank ℂ (b4_HomG ρ (fun g ↦ σ g) W) =
      Module.finrank ℂ (b4_HomG ρ (fun g ↦ σ g) U) +
        Module.finrank ℂ (b4_HomG ρ (fun g ↦ σ g) (W ⊓ LinearMap.ker P)) := by
  have hsup : b4_HomG ρ (fun g ↦ σ g) U ⊔ b4_HomG ρ (fun g ↦ σ g) (W ⊓ LinearMap.ker P) =
      b4_HomG ρ (fun g ↦ σ g) W := by
    apply le_antisymm
    · refine sup_le (fun φ hφ ↦ ⟨fun v ↦ hUW (hφ.1 v), hφ.2⟩)
        (fun φ hφ ↦ ⟨fun v ↦ (hφ.1 v).1, hφ.2⟩)
    · intro φ hφ
      refine Submodule.mem_sup.2 ⟨P ∘ₗ φ, ⟨fun v ↦ hPU _, fun g v ↦ ?_⟩, φ - P ∘ₗ φ,
        ⟨fun v ↦ ⟨W.sub_mem (hφ.1 v) (hUW (hPU _)), ?_⟩, fun g v ↦ ?_⟩, by abel⟩
      · simp only [LinearMap.comp_apply, hφ.2 g v, hPσ]
      · change P (φ v - P (φ v)) = 0
        rw [map_sub, hPid _ (hPU _), sub_self]
      · simp only [LinearMap.sub_apply, LinearMap.comp_apply, hφ.2 g v, hPσ, map_sub]
  have hinf : b4_HomG ρ (fun g ↦ σ g) U ⊓ b4_HomG ρ (fun g ↦ σ g) (W ⊓ LinearMap.ker P) = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 fun φ hφ ↦ ?_
    ext v
    have := Submodule.mem_inf.2 ⟨hφ.1.1 v, hφ.2.1 v⟩
    rw [b4cov_split_inf U W P hPid] at this
    exact (Submodule.mem_bot ℂ).1 this
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (b4_HomG ρ (fun g ↦ σ g) U)
    (b4_HomG ρ (fun g ↦ σ g) (W ⊓ LinearMap.ker P))
  rw [hsup, hinf, finrank_bot] at h1
  omega

include hPU hPid hPσ hUW in
theorem b4cov_split_map [Fintype G] [FiniteDimensional ℂ M] (a : G → ℂ)
    (hU : ∀ g, U ≤ U.comap (σ g)) (hW : ∀ g, W ≤ W.comap (σ g)) :
    Module.finrank ℂ (W.map (∑ g, a g • σ g)) =
      Module.finrank ℂ (U.map (∑ g, a g • σ g)) +
        Module.finrank ℂ ((W ⊓ LinearMap.ker P).map (∑ g, a g • σ g)) := by
  have hW' := b4cov_split_stable σ W P hPσ hW
  have hsup : U.map (∑ g, a g • σ g) ⊔ (W ⊓ LinearMap.ker P).map (∑ g, a g • σ g) =
      W.map (∑ g, a g • σ g) := by
    rw [← Submodule.map_sup, b4cov_split_sup U W P hPU hPid hUW]
  have hinf : U.map (∑ g, a g • σ g) ⊓ (W ⊓ LinearMap.ker P).map (∑ g, a g • σ g) = ⊥ := by
    refine eq_bot_iff.2 fun m hm ↦ ?_
    obtain ⟨⟨x, hx, rfl⟩, ⟨y, hy, hxy⟩⟩ := hm
    have h1 := b4cov_groupSum_mem σ a U hU x hx
    have h2 := b4cov_groupSum_mem σ a _ hW' y hy
    rw [hxy] at h2
    have := Submodule.mem_inf.2 ⟨h1, h2⟩
    rwa [b4cov_split_inf U W P hPid] at this
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (U.map (∑ g, a g • σ g))
    ((W ⊓ LinearMap.ker P).map (∑ g, a g • σ g))
  rw [hsup, hinf, finrank_bot] at h1
  omega

end Split

section Schur

variable {V₁ V₂ : Type} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
  {ρ₁ : Representation ℂ G V₁} {ρ₂ : Representation ℂ G V₂}

/-- The inverse of a bijective intertwining map. -/
def b4cov_inv (φ : Representation.IntertwiningMap ρ₁ ρ₂) (hφ : Function.Bijective φ) :
    Representation.IntertwiningMap ρ₂ ρ₁ :=
  ⟨(LinearEquiv.ofBijective φ.toLinearMap hφ).symm.toLinearMap, fun g ↦ by
    ext w
    apply hφ.1
    have he : ∀ x, φ ((LinearEquiv.ofBijective φ.toLinearMap hφ).symm x) = x := fun x ↦
      (LinearEquiv.ofBijective φ.toLinearMap hφ).apply_symm_apply x
    change φ ((LinearEquiv.ofBijective φ.toLinearMap hφ).symm (ρ₂ g w)) =
      φ (ρ₁ g ((LinearEquiv.ofBijective φ.toLinearMap hφ).symm w))
    rw [φ.isIntertwining, he, he]⟩

theorem b4cov_inv_apply_apply (φ : Representation.IntertwiningMap ρ₁ ρ₂)
    (hφ : Function.Bijective φ) (v : V₁) : b4cov_inv φ hφ (φ v) = v :=
  (LinearEquiv.ofBijective φ.toLinearMap hφ).symm_apply_apply v

theorem b4cov_apply_inv_apply (φ : Representation.IntertwiningMap ρ₁ ρ₂)
    (hφ : Function.Bijective φ) (w : V₂) : φ (b4cov_inv φ hφ w) = w :=
  (LinearEquiv.ofBijective φ.toLinearMap hφ).apply_symm_apply w

/-- Composition with a bijective intertwining map identifies the spaces of intertwining maps. -/
def b4cov_compEquiv {V₃ : Type} [AddCommGroup V₃] [Module ℂ V₃] (ρ₃ : Representation ℂ G V₃)
    (φ : Representation.IntertwiningMap ρ₁ ρ₂) (hφ : Function.Bijective φ) :
    Representation.IntertwiningMap ρ₃ ρ₂ ≃ₗ[ℂ] Representation.IntertwiningMap ρ₃ ρ₁ where
  toFun ψ := (b4cov_inv φ hφ).comp ψ
  invFun χ := φ.comp χ
  map_add' ψ ψ' := by ext; simp
  map_smul' c ψ := by ext; simp
  left_inv ψ := by ext; simp [b4cov_apply_inv_apply]
  right_inv χ := by ext; simp [b4cov_inv_apply_apply]

end Schur

section Irred

variable [Fintype G] [FiniteDimensional ℂ M]
variable {k : ℕ} {V : Fin k → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  [∀ i, FiniteDimensional ℂ (V i)] (ρ : ∀ i, Representation ℂ G (V i))
  [∀ i, (ρ i).IsIrreducible]

theorem b4cov_res_sum_apply (U : Submodule ℂ M) (hU : ∀ g, U ≤ U.comap (σ g)) (a : G → ℂ)
    (u : U) : (((∑ g, a g • b4cov_res σ U hU g) u : U) : M) = (∑ g, a g • σ g) (u : M) := by
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul,
    b4cov_res_apply]

/-- **The irreducible case**: on an irreducible stable subspace `U`, either `U ≅ ρ_j` for one
`j` (and the rank of `a` on `U` is that of `ρ_j(a)`), or `a` kills `U`. -/
theorem b4cov_irred_case
    (hdist : ∀ i j, i ≠ j → ∀ φ : Representation.IntertwiningMap (ρ i) (ρ j), φ = 0)
    (a : G → ℂ)
    (hkill : ∀ (V' : Type) [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
      (ρ' : Representation ℂ G V'), ρ'.IsIrreducible →
        (∀ i, ∀ φ : Representation.IntertwiningMap ρ' (ρ i), φ = 0) → ∑ g, a g • ρ' g = 0)
    (U : Submodule ℂ M) (hU : ∀ g, U ≤ U.comap (σ g)) [hirr : (b4cov_res σ U hU).IsIrreducible] :
    Module.finrank ℂ (U.map (∑ g, a g • σ g)) =
      ∑ i, Module.finrank ℂ (b4_HomG (ρ i) (fun g ↦ σ g) U) *
        Module.finrank ℂ (LinearMap.range (∑ g, a g • ρ i g)) := by
  by_cases hex : ∃ j, ∃ φ : Representation.IntertwiningMap (ρ j) (b4cov_res σ U hU), φ ≠ 0
  · obtain ⟨j, φ, hφ0⟩ := hex
    have hφ : Function.Bijective φ :=
      (Representation.IsIrreducible.bijective_or_eq_zero φ).resolve_right hφ0
    have hzero : ∀ i, i ≠ j → Module.finrank ℂ (b4_HomG (ρ i) (fun g ↦ σ g) U) = 0 := by
      intro i hij
      rw [(b4cov_homGEquiv σ (ρ i) U hU).finrank_eq]
      have : Subsingleton (Representation.IntertwiningMap (ρ i) (b4cov_res σ U hU)) := by
        refine ⟨fun ψ ψ' ↦ ?_⟩
        have h1 := hdist i j hij ((b4cov_inv φ hφ).comp ψ)
        have h2 := hdist i j hij ((b4cov_inv φ hφ).comp ψ')
        apply (b4cov_compEquiv (ρ i) φ hφ).injective
        exact h1.trans h2.symm
      exact Module.finrank_zero_of_subsingleton
    have hone : Module.finrank ℂ (b4_HomG (ρ j) (fun g ↦ σ g) U) = 1 := by
      rw [(b4cov_homGEquiv σ (ρ j) U hU).finrank_eq,
        ← Representation.IsIrreducible.finrank_intertwiningMap_self (ρ j)]
      exact (b4cov_compEquiv (ρ j) φ hφ).finrank_eq
    let ι : V j →ₗ[ℂ] M := U.subtype ∘ₗ φ.toLinearMap
    have hι : Function.Injective ι := Subtype.val_injective.comp hφ.1
    have hιr : LinearMap.range ι = U := by
      rw [LinearMap.range_comp, LinearMap.range_eq_top.2 hφ.2, Submodule.map_top,
        Submodule.range_subtype]
    have hcomm : (∑ g, a g • σ g) ∘ₗ ι = ι ∘ₗ (∑ g, a g • ρ j g) := by
      ext v
      simp only [ι, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.sum_apply,
        LinearMap.smul_apply, Representation.IntertwiningMap.coe_toLinearMap, map_sum, map_smul,
        φ.isIntertwining, b4cov_res_apply]
    have hrank : Module.finrank ℂ (U.map (∑ g, a g • σ g)) =
        Module.finrank ℂ (LinearMap.range (∑ g, a g • ρ j g)) := by
      rw [← hιr, ← LinearMap.range_comp, hcomm, LinearMap.range_comp]
      exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hι _)).symm
    rw [Finset.sum_eq_single j (fun i _ hij ↦ by rw [hzero i hij, zero_mul])
      (fun h ↦ absurd (Finset.mem_univ j) h), hone, one_mul, hrank]
  · simp only [not_exists, not_not] at hex
    have hzero : ∀ i, Module.finrank ℂ (b4_HomG (ρ i) (fun g ↦ σ g) U) = 0 := by
      intro i
      rw [(b4cov_homGEquiv σ (ρ i) U hU).finrank_eq]
      have : Subsingleton (Representation.IntertwiningMap (ρ i) (b4cov_res σ U hU)) :=
        ⟨fun ψ ψ' ↦ (hex i ψ).trans (hex i ψ').symm⟩
      exact Module.finrank_zero_of_subsingleton
    have hk := hkill U (b4cov_res σ U hU) hirr fun i ψ ↦ by
      by_contra hψ0
      have hψ : Function.Bijective ψ :=
        (Representation.IsIrreducible.bijective_or_eq_zero ψ).resolve_right hψ0
      apply hψ0
      ext u
      have h := b4cov_inv_apply_apply ψ hψ u
      rw [hex i (b4cov_inv ψ hψ)] at h
      simp only [Representation.IntertwiningMap.coe_zero, Pi.zero_apply] at h
      simp [← h]
    have hbot : U.map (∑ g, a g • σ g) = ⊥ := by
      refine (Submodule.eq_bot_iff _).2 ?_
      rintro _ ⟨u, hu, rfl⟩
      have := b4cov_res_sum_apply σ U hU a ⟨u, hu⟩
      rw [hk] at this
      exact this.symm.trans rfl
    simp [hbot, hzero]

theorem b4cov_homG_bot {V' : Type} [AddCommGroup V'] [Module ℂ V'] (ρ' : Representation ℂ G V') :
    b4_HomG ρ' (fun g ↦ σ g) ⊥ = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun φ hφ ↦ ?_
  ext v
  exact (Submodule.mem_bot ℂ).1 (hφ.1 v)

/-- **A minimal stable subspace is irreducible.** -/
theorem b4cov_res_isIrreducible (U : Submodule ℂ M) (hU : ∀ g, U ≤ U.comap (σ g)) (hU0 : U ≠ ⊥)
    (hmin : ∀ U' : Submodule ℂ M, (∀ g, U' ≤ U'.comap (σ g)) → U' ≠ ⊥ → U' ≤ U →
      Module.finrank ℂ U ≤ Module.finrank ℂ U') :
    (b4cov_res σ U hU).IsIrreducible := by
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h ↦ hu0 ?_⟩, eq_bot_or_eq_top := fun S ↦ ?_ }
  · have : (⟨u, hu⟩ : U) ∈ (⊥ : Subrepresentation (b4cov_res σ U hU)).toSubmodule := by
      rw [h]; trivial
    exact congrArg Subtype.val ((Submodule.mem_bot ℂ).1 this)
  let T := S.toSubmodule.map U.subtype
  have hT : ∀ g, T ≤ T.comap (σ g) := by
    rintro g _ ⟨s, hs, rfl⟩
    exact ⟨b4cov_res σ U hU g s, S.apply_mem_toSubmodule g hs, rfl⟩
  have hTU : T ≤ U := Submodule.map_subtype_le _ _
  by_cases hT0 : T = ⊥
  · left
    refine Subrepresentation.ext (eq_bot_iff.2 fun x hx ↦ ?_)
    have : (x : M) ∈ T := ⟨x, hx, rfl⟩
    rw [hT0] at this
    exact (Submodule.mem_bot ℂ).2 (Subtype.ext ((Submodule.mem_bot ℂ).1 this))
  · right
    have heq : T = U := Submodule.eq_of_le_of_finrank_le hTU (hmin T hT hT0 hTU)
    refine Subrepresentation.ext (eq_top_iff.2 fun x _ ↦ ?_)
    have : (x : M) ∈ T := by rw [heq]; exact x.2
    obtain ⟨s, hs, hsx⟩ := this
    rw [← Subtype.ext hsx]
    exact hs

/-- **Ranks of group-ring elements on stable subspaces.** -/
theorem b4cov_finrank_map_isotypic
    (hdist : ∀ i j, i ≠ j → ∀ φ : Representation.IntertwiningMap (ρ i) (ρ j), φ = 0)
    (a : G → ℂ)
    (hkill : ∀ (V' : Type) [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
      (ρ' : Representation ℂ G V'), ρ'.IsIrreducible →
        (∀ i, ∀ φ : Representation.IntertwiningMap ρ' (ρ i), φ = 0) → ∑ g, a g • ρ' g = 0)
    (W : Submodule ℂ M) (hW : ∀ g, W ≤ W.comap (σ g)) :
    Module.finrank ℂ (W.map (∑ g, a g • σ g)) =
      ∑ i, Module.finrank ℂ (b4_HomG (ρ i) (fun g ↦ σ g) W) *
        Module.finrank ℂ (LinearMap.range (∑ g, a g • ρ i g)) := by
  classical
  suffices h : ∀ n, ∀ W : Submodule ℂ M, Module.finrank ℂ W ≤ n → (∀ g, W ≤ W.comap (σ g)) →
      Module.finrank ℂ (W.map (∑ g, a g • σ g)) =
        ∑ i, Module.finrank ℂ (b4_HomG (ρ i) (fun g ↦ σ g) W) *
          Module.finrank ℂ (LinearMap.range (∑ g, a g • ρ i g)) from h _ W le_rfl hW
  have hbot : Module.finrank ℂ ((⊥ : Submodule ℂ M).map (∑ g, a g • σ g)) =
      ∑ i, Module.finrank ℂ (b4_HomG (ρ i) (fun g ↦ σ g) ⊥) *
        Module.finrank ℂ (LinearMap.range (∑ g, a g • ρ i g)) := by
    rw [Submodule.map_bot, finrank_bot]
    refine (Finset.sum_eq_zero fun i _ ↦ ?_).symm
    rw [b4cov_homG_bot σ (ρ i), finrank_bot, zero_mul]
  intro n
  induction n with
  | zero =>
    intro W hn _
    rw [Submodule.finrank_eq_zero.1 (Nat.le_zero.1 hn)]
    exact hbot
  | succ n ih =>
    intro W hn hW
    by_cases hW0 : W = ⊥
    · rw [hW0]; exact hbot
    have hex : ∃ d, ∃ U : Submodule ℂ M, (∀ g, U ≤ U.comap (σ g)) ∧ U ≠ ⊥ ∧ U ≤ W ∧
        Module.finrank ℂ U = d := ⟨_, W, hW, hW0, le_rfl, rfl⟩
    obtain ⟨U, hU, hU0, hUW, hUd⟩ := Nat.find_spec hex
    have hmin : ∀ U' : Submodule ℂ M, (∀ g, U' ≤ U'.comap (σ g)) → U' ≠ ⊥ → U' ≤ U →
        Module.finrank ℂ U ≤ Module.finrank ℂ U' := fun U' h1 h2 h3 ↦
      hUd ▸ Nat.find_min' hex ⟨U', h1, h2, h3.trans hUW, rfl⟩
    have := b4cov_res_isIrreducible σ U hU hU0 hmin
    obtain ⟨P, hPU, hPid, hPσ⟩ := b4cov_exists_equivariantProj σ U hU
    have hW' := b4cov_split_stable σ W P hPσ hW
    have hdim : Module.finrank ℂ W = Module.finrank ℂ U + Module.finrank ℂ ↥(W ⊓ LinearMap.ker P) := by
      have := Submodule.finrank_sup_add_finrank_inf_eq U (W ⊓ LinearMap.ker P)
      rw [b4cov_split_sup U W P hPU hPid hUW, b4cov_split_inf U W P hPid, finrank_bot] at this
      omega
    have hUpos : 0 < Module.finrank ℂ U :=
      Nat.pos_of_ne_zero fun h ↦ hU0 (Submodule.finrank_eq_zero.1 h)
    have ih' := ih (W ⊓ LinearMap.ker P) (by omega) hW'
    rw [b4cov_split_map σ U W P hPU hPid hPσ hUW a hU hW,
      b4cov_irred_case σ ρ hdist a hkill U hU, ih', ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [b4cov_split_homG σ U W P hPU hPid hPσ hUW (ρ i), add_mul]

end Irred

end Isotypic

end HodgeLean.Foundations.Program
