import HodgeLean.Foundations.DirectSumInvariantsDefs

/-! # Proofs for the direct-sum invariants spec (stage A3a)

The agent's working file. Fill every proof hole. **Do not change the statement of any `_aux`
theorem**: `DirectSumInvariants.lean` (frozen) restates each one and must still typecheck.
Helper lemmas may be added freely, in this file or in new files; prefix them `a3a_`.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
attribute [local instance 100] LieRing.ofAssociativeRing
open scoped TensorProduct DirectSum
namespace HodgeLean.Foundations
open InvariantsExterior

variable {K : Type*} [Field K]

section Tensor

variable {𝔤₁ 𝔤₂ M₁ M₂ : Type*} [LieRing 𝔤₁] [LieAlgebra K 𝔤₁] [LieRing 𝔤₂] [LieAlgebra K 𝔤₂]
  [AddCommGroup M₁] [Module K M₁] [AddCommGroup M₂] [Module K M₂]

theorem a3a_finsuppScalarRight_rTensor {ι Q R N : Type*} [DecidableEq ι] [AddCommGroup Q] [Module K Q]
    [AddCommGroup R] [Module K R] [AddCommGroup N] [Module K N] (b : Module.Basis ι K N)
    (g : Q →ₗ[K] R) (t : Q ⊗[K] N) :
    TensorProduct.finsuppScalarRight K K R ι (TensorProduct.congr (LinearEquiv.refl K R) b.repr
        (g.rTensor N t)) =
      Finsupp.mapRange.linearMap g (TensorProduct.finsuppScalarRight K K Q ι
        (TensorProduct.congr (LinearEquiv.refl K Q) b.repr t)) := by
  induction t using TensorProduct.inductionOn with
  | tmul q n => ext i; simp
  | add x y hx hy => simp only [map_add, hx, hy]

theorem a3a_iInf_ker_rTensor {A M P N : Type*} [AddCommGroup M] [Module K M]
    [AddCommGroup P] [Module K P] [AddCommGroup N] [Module K N] (f : A → M →ₗ[K] P) :
    (⨅ a, LinearMap.ker ((f a).rTensor N)) =
      LinearMap.range ((⨅ a, LinearMap.ker (f a)).subtype.rTensor N) := by
  classical
  set W := ⨅ a, LinearMap.ker (f a)
  let b := Module.Free.chooseBasis K N
  let e : ∀ (Q : Type _) [AddCommGroup Q] [Module K Q], Q ⊗[K] N ≃ₗ[K] _ →₀ Q := fun Q _ _ =>
    (TensorProduct.congr (LinearEquiv.refl K Q) b.repr) ≪≫ₗ
      TensorProduct.finsuppScalarRight K K Q _
  apply le_antisymm
  · intro t ht
    simp only [Submodule.mem_iInf, LinearMap.mem_ker] at ht
    have hv : ∀ i, e M t i ∈ W := by
      intro i
      simp only [W, Submodule.mem_iInf, LinearMap.mem_ker]
      intro a
      have := congrArg (fun s => TensorProduct.finsuppScalarRight K K P _
        (TensorProduct.congr (LinearEquiv.refl K P) b.repr s) i) (ht a)
      rw [a3a_finsuppScalarRight_rTensor] at this
      simpa [e] using this
    let g : _ →₀ W := Finsupp.mapRange (fun m => if h : m ∈ W then ⟨m, h⟩ else 0) (by simp) (e M t)
    refine ⟨(e W).symm g, ?_⟩
    apply (e M).injective
    have := a3a_finsuppScalarRight_rTensor b W.subtype ((e W).symm g)
    change TensorProduct.finsuppScalarRight K K M _
      (TensorProduct.congr (LinearEquiv.refl K M) b.repr _) = _
    rw [this]
    change Finsupp.mapRange.linearMap W.subtype (e W ((e W).symm g)) = _
    rw [LinearEquiv.apply_symm_apply]
    ext i
    simp [g, hv i]
  · rintro _ ⟨s, rfl⟩
    simp only [Submodule.mem_iInf, LinearMap.mem_ker]
    intro a
    rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp]
    have : f a ∘ₗ W.subtype = 0 := by
      ext ⟨m, hm⟩
      simp only [W, Submodule.mem_iInf, LinearMap.mem_ker] at hm
      simp [hm a]
    simp [this]

theorem a3a_iInf_ker_lTensor {A M P N : Type*} [AddCommGroup M] [Module K M]
    [AddCommGroup P] [Module K P] [AddCommGroup N] [Module K N] (f : A → M →ₗ[K] P) :
    (⨅ a, LinearMap.ker ((f a).lTensor N)) =
      LinearMap.range ((⨅ a, LinearMap.ker (f a)).subtype.lTensor N) := by
  have key := a3a_iInf_ker_rTensor (N := N) f
  ext t
  have h1 : t ∈ (⨅ a, LinearMap.ker ((f a).lTensor N)) ↔
      TensorProduct.comm K N M t ∈ ⨅ a, LinearMap.ker ((f a).rTensor N) := by
    simp only [Submodule.mem_iInf, LinearMap.mem_ker]
    refine forall_congr' fun a => ?_
    rw [← LinearMap.comm_comp_lTensor_comp_comm_eq]
    simp
  have h2 : t ∈ LinearMap.range ((⨅ a, LinearMap.ker (f a)).subtype.lTensor N) ↔
      TensorProduct.comm K N M t ∈
        LinearMap.range ((⨅ a, LinearMap.ker (f a)).subtype.rTensor N) := by
    rw [← LinearMap.comm_comp_lTensor_comp_comm_eq]
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨TensorProduct.comm K N _ s, by simp⟩
    · rintro ⟨s, hs⟩
      refine ⟨TensorProduct.comm K _ N s, ?_⟩
      apply (TensorProduct.comm K N M).injective
      rw [← hs]
      simp
  rw [h1, h2, key]

theorem a3a_iInf_ker_rTensor_add_lTensor {A B M₁ M₂ : Type*} [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B] [AddCommGroup M₁] [Module K M₁] [AddCommGroup M₂] [Module K M₂]
    (f : A →ₗ[K] Module.End K M₁) (g : B →ₗ[K] Module.End K M₂) :
    (⨅ x : A × B, LinearMap.ker ((f x.1).rTensor M₂ + (g x.2).lTensor M₁)) =
      LinearMap.range (TensorProduct.map (⨅ x, LinearMap.ker (f x)).subtype
        (⨅ y, LinearMap.ker (g y)).subtype) := by
  set W₁ := ⨅ x, LinearMap.ker (f x)
  set W₂ := ⨅ y, LinearMap.ker (g y)
  apply le_antisymm
  · intro t ht
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, Prod.forall] at ht
    have ht2 : t ∈ ⨅ y, LinearMap.ker ((g y).lTensor M₁) := by
      simp only [Submodule.mem_iInf, LinearMap.mem_ker]
      intro y
      simpa using ht 0 y
    rw [a3a_iInf_ker_lTensor] at ht2
    obtain ⟨s, rfl⟩ := ht2
    have hs : s ∈ ⨅ x, LinearMap.ker ((f x).rTensor W₂) := by
      simp only [Submodule.mem_iInf, LinearMap.mem_ker]
      intro x
      apply Module.Flat.lTensor_preserves_injective_linearMap (M := M₁) W₂.subtype
        W₂.injective_subtype
      rw [map_zero]
      have := ht x 0
      simp only [map_zero, LinearMap.lTensor_zero, add_zero] at this
      rw [← this, ← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor,
        LinearMap.rTensor_comp_lTensor]
    rw [a3a_iInf_ker_rTensor] at hs
    obtain ⟨u, rfl⟩ := hs
    exact ⟨u, by rw [← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor]⟩
  · rintro _ ⟨u, rfl⟩
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, Prod.forall]
    intro x y
    have h1 : f x ∘ₗ W₁.subtype = 0 := by
      ext ⟨m, hm⟩
      simp only [W₁, Submodule.mem_iInf, LinearMap.mem_ker] at hm
      simp [hm x]
    have h2 : g y ∘ₗ W₂.subtype = 0 := by
      ext ⟨m, hm⟩
      simp only [W₂, Submodule.mem_iInf, LinearMap.mem_ker] at hm
      simp [hm y]
    rw [LinearMap.add_apply, LinearMap.rTensor_map, LinearMap.lTensor_map, h1, h2,
      TensorProduct.map_zero_left, TensorProduct.map_zero_right]
    simp


theorem spec_a3a_tensor_invariants_aux [FiniteDimensional K M₁] [FiniteDimensional K M₂]
    (ρ₁ : 𝔤₁ →ₗ⁅K⁆ Module.End K M₁) (ρ₂ : 𝔤₂ →ₗ⁅K⁆ Module.End K M₂) :
    (⨅ x : 𝔤₁ × 𝔤₂, LinearMap.ker ((ρ₁ x.1).rTensor M₂ + (ρ₂ x.2).lTensor M₁)) =
      LinearMap.range (TensorProduct.map (⨅ x, LinearMap.ker (ρ₁ x)).subtype
        (⨅ y, LinearMap.ker (ρ₂ y)).subtype) :=
  a3a_iInf_ker_rTensor_add_lTensor (ρ₁ : 𝔤₁ →ₗ[K] Module.End K M₁) (ρ₂ : 𝔤₂ →ₗ[K] Module.End K M₂)

theorem spec_a3a_maxTrivSubmodule_tensor_aux [FiniteDimensional K M₁] [FiniteDimensional K M₂]
    [LieRingModule (𝔤₁ × 𝔤₂) M₁] [LieModule K (𝔤₁ × 𝔤₂) M₁]
    [LieRingModule (𝔤₁ × 𝔤₂) M₂] [LieModule K (𝔤₁ × 𝔤₂) M₂]
    (h₁ : ∀ (y : 𝔤₂) (m : M₁), ⁅((0 : 𝔤₁), y), m⁆ = 0)
    (h₂ : ∀ (x : 𝔤₁) (n : M₂), ⁅(x, (0 : 𝔤₂)), n⁆ = 0) :
    (LieModule.maxTrivSubmodule K (𝔤₁ × 𝔤₂) (M₁ ⊗[K] M₂) : Submodule K (M₁ ⊗[K] M₂)) =
      LinearMap.range (TensorProduct.map
        (LieModule.maxTrivSubmodule K (𝔤₁ × 𝔤₂) M₁ : Submodule K M₁).subtype
        (LieModule.maxTrivSubmodule K (𝔤₁ × 𝔤₂) M₂ : Submodule K M₂).subtype) := by
  let f : 𝔤₁ →ₗ[K] Module.End K M₁ :=
    (LieModule.toEnd K (𝔤₁ × 𝔤₂) M₁ : (𝔤₁ × 𝔤₂) →ₗ[K] Module.End K M₁) ∘ₗ LinearMap.inl K 𝔤₁ 𝔤₂
  let g : 𝔤₂ →ₗ[K] Module.End K M₂ :=
    (LieModule.toEnd K (𝔤₁ × 𝔤₂) M₂ : (𝔤₁ × 𝔤₂) →ₗ[K] Module.End K M₂) ∘ₗ LinearMap.inr K 𝔤₁ 𝔤₂
  have hf : ∀ (x : 𝔤₁ × 𝔤₂) (m : M₁), ⁅x, m⁆ = f x.1 m := by
    rintro ⟨x, y⟩ m
    have : ((x, y) : 𝔤₁ × 𝔤₂) = (x, 0) + (0, y) := by simp
    change ⁅(x, y), m⁆ = ⁅(x, 0), m⁆
    rw [this, add_lie, h₁, add_zero]
  have hg : ∀ (x : 𝔤₁ × 𝔤₂) (n : M₂), ⁅x, n⁆ = g x.2 n := by
    rintro ⟨x, y⟩ n
    have : ((x, y) : 𝔤₁ × 𝔤₂) = (x, 0) + (0, y) := by simp
    change ⁅(x, y), n⁆ = ⁅(0, y), n⁆
    rw [this, add_lie, h₂, zero_add]
  have e₁ : (LieModule.maxTrivSubmodule K (𝔤₁ × 𝔤₂) M₁ : Submodule K M₁) =
      ⨅ x, LinearMap.ker (f x) := by
    ext m
    simp only [LieSubmodule.mem_toSubmodule, LieModule.mem_maxTrivSubmodule, Submodule.mem_iInf,
      LinearMap.mem_ker, hf]
    exact ⟨fun h x => h (x, 0), fun h x => h x.1⟩
  have e₂ : (LieModule.maxTrivSubmodule K (𝔤₁ × 𝔤₂) M₂ : Submodule K M₂) =
      ⨅ y, LinearMap.ker (g y) := by
    ext n
    simp only [LieSubmodule.mem_toSubmodule, LieModule.mem_maxTrivSubmodule, Submodule.mem_iInf,
      LinearMap.mem_ker, hg]
    exact ⟨fun h y => h (0, y), fun h x => h x.2⟩
  have e : (LieModule.maxTrivSubmodule K (𝔤₁ × 𝔤₂) (M₁ ⊗[K] M₂) : Submodule K (M₁ ⊗[K] M₂)) =
      ⨅ x : 𝔤₁ × 𝔤₂, LinearMap.ker ((f x.1).rTensor M₂ + (g x.2).lTensor M₁) := by
    ext t
    simp only [LieSubmodule.mem_toSubmodule, LieModule.mem_maxTrivSubmodule, Submodule.mem_iInf,
      LinearMap.mem_ker]
    refine forall_congr' fun x => ?_
    suffices h : ∀ t : M₁ ⊗[K] M₂, ⁅x, t⁆ = ((f x.1).rTensor M₂ + (g x.2).lTensor M₁) t by
      rw [h]
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul m n => simp [TensorProduct.LieModule.lie_tmul_right, hf, hg]
    | add a b ha hb => rw [lie_add, ha, hb, map_add]
  rw [e, e₁, e₂]
  exact a3a_iInf_ker_rTensor_add_lTensor f g

theorem spec_a3a_ker_rTensor_ne_over_int_aux :
    LinearMap.ker ((2 : Module.End ℤ ℤ).rTensor (ZMod 2)) ≠
      LinearMap.range ((LinearMap.ker (2 : Module.End ℤ ℤ)).subtype.rTensor (ZMod 2)) := by
  intro h
  have hmem : (1 : ℤ) ⊗ₜ[ℤ] (1 : ZMod 2) ∈ LinearMap.ker ((2 : Module.End ℤ ℤ).rTensor (ZMod 2)) := by
    rw [LinearMap.mem_ker]
    apply (TensorProduct.lid ℤ (ZMod 2)).injective
    simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, map_zero]
    decide
  rw [h] at hmem
  obtain ⟨s, hs⟩ := hmem
  have hbot : LinearMap.ker (2 : Module.End ℤ ℤ) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro m hm
    have : (2 : ℤ) * m = 0 := by simpa using hm
    omega
  have hs0 : s = 0 := by
    have : Subsingleton (LinearMap.ker (2 : Module.End ℤ ℤ)) := by
      rw [hbot]; infer_instance
    exact Subsingleton.elim _ _
  rw [hs0, map_zero] at hs
  have := congrArg (TensorProduct.lid ℤ (ZMod 2)) hs
  simp only [map_zero, TensorProduct.lid_tmul, one_smul] at this
  exact one_ne_zero this.symm

end Tensor

section Exterior

variable {S₁ S₂ : Type*} [AddCommGroup S₁] [Module K S₁] [AddCommGroup S₂] [Module K S₂]

theorem spec_a3a_exteriorProdMul_tmul_aux (i j : ℕ) (a : ⋀[K]^i S₁) (b : ⋀[K]^j S₂) :
    ((exteriorProdMul i j (a ⊗ₜ[K] b) : ⋀[K]^(i + j) (S₁ × S₂)) : ExteriorAlgebra K (S₁ × S₂)) =
      (ExteriorAlgebra.prodEquivTensor K S₁ S₂).symm
        ((a : ExteriorAlgebra K S₁) ᵍ⊗ₜ[K] (b : ExteriorAlgebra K S₂)) := by
  rw [ExteriorAlgebra.prodEquivTensor_symm_tmul, ← exteriorPower.coe_map, ← exteriorPower.coe_map]
  rfl

variable (K S₁ S₂) in
/-- The bigraded decomposition `⋀(S₁ × S₂) ≅ ⨁_{(i,j)} ⋀^i S₁ ⊗ ⋀^j S₂`: Mathlib's
`ExteriorAlgebra.prodEquivTensor`, followed by the decompositions of both factors and the
distributivity of `⊗` over `⨁`.
Source: Bourbaki, *Algèbre*, ch. III, §7, no. 7, Proposition 10. -/
def a3a_bigradedEquiv : ExteriorAlgebra K (S₁ × S₂) ≃ₗ[K]
    ⨁ q : ℕ × ℕ, ⋀[K]^q.1 S₁ ⊗[K] ⋀[K]^q.2 S₂ :=
  (ExteriorAlgebra.prodEquivTensor K S₁ S₂).toLinearEquiv ≪≫ₗ
    GradedTensorProduct.auxEquiv K _ _ ≪≫ₗ TensorProduct.directSum K K _ _

theorem a3a_bigradedEquiv_exteriorProdMul (i j : ℕ) (a : ⋀[K]^i S₁) (b : ⋀[K]^j S₂) :
    a3a_bigradedEquiv K S₁ S₂ (exteriorProdMul i j (a ⊗ₜ[K] b) : ExteriorAlgebra K (S₁ × S₂)) =
      DirectSum.lof K (ℕ × ℕ) (fun q => ⋀[K]^q.1 S₁ ⊗[K] ⋀[K]^q.2 S₂) (i, j) (a ⊗ₜ[K] b) := by
  simp only [a3a_bigradedEquiv, LinearEquiv.trans_apply, spec_a3a_exteriorProdMul_tmul_aux,
    AlgEquiv.toLinearEquiv_apply, AlgEquiv.apply_symm_apply, GradedTensorProduct.auxEquiv_tmul,
    DirectSum.decompose_coe, ← DirectSum.lof_eq_of K, TensorProduct.directSum_lof_tmul_lof]

example (i j : ℕ) (a : ⋀[K]^i S₁) (b : ⋀[K]^j S₂) :
    (a3a_bigradedEquiv K S₁ S₂).symm
        (DirectSum.lof K (ℕ × ℕ) (fun q => ⋀[K]^q.1 S₁ ⊗[K] ⋀[K]^q.2 S₂) (i, j) (a ⊗ₜ[K] b)) =
      (exteriorProdMul i j (a ⊗ₜ[K] b) : ExteriorAlgebra K (S₁ × S₂)) := by
  rw [LinearEquiv.symm_apply_eq, a3a_bigradedEquiv_exteriorProdMul]

variable (K S₁ S₂) in
/-- Restriction of a bigraded family to the antidiagonal `i + j = k`.
Source: Bourbaki, *Algèbre*, ch. II, §1, no. 6 (projections of a direct sum). -/
def a3a_restrict (k : ℕ) : (⨁ q : ℕ × ℕ, ⋀[K]^q.1 S₁ ⊗[K] ⋀[K]^q.2 S₂) →ₗ[K]
    ⨁ p : {p : ℕ × ℕ // p.1 + p.2 = k}, ⋀[K]^p.1.1 S₁ ⊗[K] ⋀[K]^p.1.2 S₂ :=
  DirectSum.toModule K _ _ fun q =>
    if h : q.1 + q.2 = k then
      DirectSum.lof K _ (fun p : {p : ℕ × ℕ // p.1 + p.2 = k} => ⋀[K]^p.1.1 S₁ ⊗[K] ⋀[K]^p.1.2 S₂)
        ⟨q, h⟩
    else 0

example (k : ℕ) (q : ℕ × ℕ) (h : q.1 + q.2 = k) (x : ⋀[K]^q.1 S₁ ⊗[K] ⋀[K]^q.2 S₂) :
    a3a_restrict K S₁ S₂ k (DirectSum.lof K _ _ q x) = DirectSum.lof K _
      (fun p : {p : ℕ × ℕ // p.1 + p.2 = k} => ⋀[K]^p.1.1 S₁ ⊗[K] ⋀[K]^p.1.2 S₂) ⟨q, h⟩ x := by
  simp [a3a_restrict, DirectSum.toModule_lof, h]

theorem a3a_restrict_comp_exteriorProdDegree (k : ℕ) :
    a3a_restrict K S₁ S₂ k ∘ₗ (a3a_bigradedEquiv K S₁ S₂).toLinearMap ∘ₗ
        (⋀[K]^k (S₁ × S₂)).subtype ∘ₗ exteriorProdDegree k = LinearMap.id := by
  refine DirectSum.linearMap_ext K fun p => TensorProduct.ext' fun a b => ?_
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, exteriorProdDegree,
    DirectSum.toModule_lof, LinearEquiv.coe_coe, LinearEquiv.coe_ofEq_apply,
    a3a_bigradedEquiv_exteriorProdMul, a3a_restrict, LinearMap.id_apply, p.2, ↓reduceDIte]

theorem a3a_exteriorProdDegree_comp_restrict (k : ℕ) :
    (⋀[K]^k (S₁ × S₂)).subtype ∘ₗ exteriorProdDegree k ∘ₗ a3a_restrict K S₁ S₂ k =
      GradedAlgebra.proj (fun i : ℕ => ⋀[K]^i (S₁ × S₂)) k ∘ₗ
        (a3a_bigradedEquiv K S₁ S₂).symm.toLinearMap := by
  refine DirectSum.linearMap_ext K fun q => TensorProduct.ext' fun a b => ?_
  have hsymm : (a3a_bigradedEquiv K S₁ S₂).symm
      (DirectSum.lof K (ℕ × ℕ) (fun q => ⋀[K]^q.1 S₁ ⊗[K] ⋀[K]^q.2 S₂) q (a ⊗ₜ[K] b)) =
      (exteriorProdMul q.1 q.2 (a ⊗ₜ[K] b) : ExteriorAlgebra K (S₁ × S₂)) := by
    rw [LinearEquiv.symm_apply_eq, a3a_bigradedEquiv_exteriorProdMul]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hsymm, GradedAlgebra.proj_apply,
    a3a_restrict, DirectSum.toModule_lof]
  by_cases h : q.1 + q.2 = k
  · simp only [h, ↓reduceDIte]
    rw [DirectSum.decompose_of_mem_same (fun i : ℕ => ⋀[K]^i (S₁ × S₂)) (h ▸ (exteriorProdMul q.1 q.2 (a ⊗ₜ[K] b)).2)]
    simp only [Submodule.subtype_apply, exteriorProdDegree, DirectSum.toModule_lof,
      LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_ofEq_apply]
  · simp only [h, ↓reduceDIte]
    rw [DirectSum.decompose_of_mem_ne (fun i : ℕ => ⋀[K]^i (S₁ × S₂)) (exteriorProdMul q.1 q.2 (a ⊗ₜ[K] b)).2 h]
    simp

theorem spec_a3a_exteriorProdDegree_bijective_aux (k : ℕ) :
    Function.Bijective (exteriorProdDegree (K := K) (S₁ := S₁) (S₂ := S₂) k) := by
  refine ⟨fun x y hxy => ?_, fun y => ⟨a3a_restrict K S₁ S₂ k (a3a_bigradedEquiv K S₁ S₂ y), ?_⟩⟩
  · have h := congrArg (fun z => a3a_restrict K S₁ S₂ k (a3a_bigradedEquiv K S₁ S₂
      ((⋀[K]^k (S₁ × S₂)).subtype z))) hxy
    have e := LinearMap.congr_fun (a3a_restrict_comp_exteriorProdDegree (K := K) (S₁ := S₁)
      (S₂ := S₂) k)
    simp only [LinearMap.comp_apply, LinearMap.id_apply, Submodule.subtype_apply,
      LinearEquiv.coe_coe] at e h
    rwa [e, e] at h
  · apply Subtype.ext
    have := LinearMap.congr_fun (a3a_exteriorProdDegree_comp_restrict (K := K) (S₁ := S₁)
      (S₂ := S₂) k) (a3a_bigradedEquiv K S₁ S₂ y)
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, GradedAlgebra.proj_apply] at this
    rw [this, DirectSum.decompose_of_mem_same (fun i : ℕ => ⋀[K]^i (S₁ × S₂)) y.2]

theorem a3a_prodEquivTensor_exteriorProdDegree_lof (k : ℕ) (p : {p : ℕ × ℕ // p.1 + p.2 = k}) :
    (GradedTensorProduct.of K (fun i : ℕ => ⋀[K]^i S₁) (fun i : ℕ => ⋀[K]^i S₂)).symm.toLinearMap ∘ₗ
        (ExteriorAlgebra.prodEquivTensor K S₁ S₂).toLinearMap ∘ₗ (⋀[K]^k (S₁ × S₂)).subtype ∘ₗ
          exteriorProdDegree k ∘ₗ DirectSum.lof K _
            (fun p : {p : ℕ × ℕ // p.1 + p.2 = k} => ⋀[K]^p.1.1 S₁ ⊗[K] ⋀[K]^p.1.2 S₂) p =
      TensorProduct.map (⋀[K]^p.1.1 S₁).subtype (⋀[K]^p.1.2 S₂).subtype := by
  refine TensorProduct.ext' fun a b => ?_
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, exteriorProdDegree,
    DirectSum.toModule_lof, LinearEquiv.coe_coe, LinearEquiv.coe_ofEq_apply,
    spec_a3a_exteriorProdMul_tmul_aux, AlgEquiv.toLinearMap_apply, AlgEquiv.apply_symm_apply,
    TensorProduct.map_tmul]
  rfl

theorem spec_a3a_mem_exteriorPower_iff_aux (k : ℕ) (x : ExteriorAlgebra K (S₁ × S₂)) :
    x ∈ ⋀[K]^k (S₁ × S₂) ↔
      (GradedTensorProduct.of K (fun i : ℕ => ⋀[K]^i S₁) (fun i : ℕ => ⋀[K]^i S₂)).symm
          (ExteriorAlgebra.prodEquivTensor K S₁ S₂ x) ∈
        ⨆ p : {p : ℕ × ℕ // p.1 + p.2 = k},
          LinearMap.range (TensorProduct.map (⋀[K]^p.1.1 S₁).subtype (⋀[K]^p.1.2 S₂).subtype) := by
  constructor
  · intro hx
    obtain ⟨w, hw⟩ := (spec_a3a_exteriorProdDegree_bijective_aux (K := K) (S₁ := S₁) (S₂ := S₂) k).2 ⟨x, hx⟩
    have hxw : x = ((exteriorProdDegree k w : ⋀[K]^k (S₁ × S₂)) : ExteriorAlgebra K (S₁ × S₂)) := by
      rw [hw]
    subst hxw
    clear hw hx
    induction w using DirectSum.induction_on with
    | zero => simp
    | of p y =>
      have := LinearMap.congr_fun (a3a_prodEquivTensor_exteriorProdDegree_lof
        (K := K) (S₁ := S₁) (S₂ := S₂) k p) y
      simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe,
        AlgEquiv.toLinearMap_apply, DirectSum.lof_eq_of] at this
      rw [this]
      exact Submodule.mem_iSup_of_mem p (LinearMap.mem_range_self _ _)
    | add w₁ w₂ h₁ h₂ =>
      simp only [map_add, Submodule.coe_add]
      exact Submodule.add_mem _ h₁ h₂
  · intro hx
    set L := (ExteriorAlgebra.prodEquivTensor K S₁ S₂).symm.toLinearMap ∘ₗ
      (GradedTensorProduct.of K (fun i : ℕ => ⋀[K]^i S₁) (fun i : ℕ => ⋀[K]^i S₂)).toLinearMap
    have hL : x = L ((GradedTensorProduct.of K (fun i : ℕ => ⋀[K]^i S₁)
        (fun i : ℕ => ⋀[K]^i S₂)).symm (ExteriorAlgebra.prodEquivTensor K S₁ S₂ x)) := by
      simp [L]
    rw [hL]
    refine (iSup_le fun p => ?_ : _ ≤ (⋀[K]^k (S₁ × S₂)).comap L) hx
    rintro _ ⟨y, rfl⟩
    rw [Submodule.mem_comap]
    induction y using TensorProduct.inductionOn with
    | tmul a b =>
      have hab : L (TensorProduct.map (⋀[K]^p.1.1 S₁).subtype (⋀[K]^p.1.2 S₂).subtype
          (a ⊗ₜ[K] b)) = (exteriorProdMul p.1.1 p.1.2 (a ⊗ₜ[K] b) : ExteriorAlgebra K (S₁ × S₂)) := by
        rw [spec_a3a_exteriorProdMul_tmul_aux]
        rfl
      have key : ∀ {n m : ℕ} (z : ExteriorAlgebra K (S₁ × S₂)), n = m →
          z ∈ ⋀[K]^n (S₁ × S₂) → z ∈ ⋀[K]^m (S₁ × S₂) := by
        rintro n m z rfl h
        exact h
      rw [hab]
      exact key _ p.2 (exteriorProdMul p.1.1 p.1.2 (a ⊗ₜ[K] b)).2
    | add y₁ y₂ h₁ h₂ =>
      rw [map_add, map_add]
      exact Submodule.add_mem _ h₁ h₂

theorem spec_a3a_exteriorProdMul_mul_aux (i j i' j' : ℕ) (a : ⋀[K]^i S₁) (b : ⋀[K]^j S₂)
    (a' : ⋀[K]^i' S₁) (b' : ⋀[K]^j' S₂) :
    ((exteriorProdMul i j (a ⊗ₜ[K] b) : ⋀[K]^(i + j) (S₁ × S₂)) : ExteriorAlgebra K (S₁ × S₂)) *
        (exteriorProdMul i' j' (a' ⊗ₜ[K] b') : ⋀[K]^(i' + j') (S₁ × S₂)) =
      (-1 : K) ^ (j * i') •
        ((exteriorProdMul (i + i') (j + j')
          (exteriorPower.wedge K S₁ i i' a a' ⊗ₜ[K] exteriorPower.wedge K S₂ j j' b b') :
            ⋀[K]^(i + i' + (j + j')) (S₁ × S₂)) : ExteriorAlgebra K (S₁ × S₂)) := by
  simp only [spec_a3a_exteriorProdMul_tmul_aux, ExteriorAlgebra.prodEquivTensor_symm_tmul]
  have hw₁ : ((exteriorPower.wedge K S₁ i i' a a' : ⋀[K]^(i + i') S₁) : ExteriorAlgebra K S₁) =
      (a : ExteriorAlgebra K S₁) * a' := rfl
  have hw₂ : ((exteriorPower.wedge K S₂ j j' b b' : ⋀[K]^(j + j') S₂) : ExteriorAlgebra K S₂) =
      (b : ExteriorAlgebra K S₂) * b' := rfl
  rw [hw₁, hw₂, map_mul, map_mul]
  have h := ExteriorAlgebra.map_inl_inr_anticomm K i' j a' b
  rw [← Int.cast_smul_eq_zsmul K] at h
  push_cast at h
  rw [mul_assoc, ← mul_assoc (ExteriorAlgebra.map _ (b : ExteriorAlgebra K S₂)),
    show ExteriorAlgebra.map (LinearMap.inr K S₁ S₂) (b : ExteriorAlgebra K S₂) *
      ExteriorAlgebra.map (LinearMap.inl K S₁ S₂) (a' : ExteriorAlgebra K S₁) =
      (-1 : K) ^ (j * i') • (ExteriorAlgebra.map (LinearMap.inl K S₁ S₂) (a' : ExteriorAlgebra K S₁) *
        ExteriorAlgebra.map (LinearMap.inr K S₁ S₂) (b : ExteriorAlgebra K S₂)) from ?_]
  · simp only [smul_mul_assoc, mul_smul_comm, mul_assoc]
  · rw [h, smul_smul, ← mul_pow]
    norm_num

theorem a3a_subsingleton_exteriorPower [Subsingleton S₂] {j : ℕ} (hj : j ≠ 0) :
    Subsingleton (⋀[K]^j S₂) := by
  have hzero : ∀ x ∈ ⋀[K]^j S₂, x = 0 := by
    intro x hx
    rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨v, rfl⟩ := hy
      obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
      exact (ExteriorAlgebra.ιMulti K (j' + 1)).map_coord_zero 0 (Subsingleton.elim _ _)
    | zero => rfl
    | add y z _ _ hy hz => rw [hy, hz, add_zero]
    | smul r y _ hy => rw [hy, smul_zero]
  exact ⟨fun a b => Subtype.ext ((hzero a a.2).trans (hzero b b.2).symm)⟩

theorem spec_a3a_exteriorProdMul_bijective_of_subsingleton_aux [Subsingleton S₂] (k : ℕ) :
    Function.Bijective (exteriorProdMul (K := K) (S₁ := S₁) (S₂ := S₂) k 0) := by
  set p₀ : {p : ℕ × ℕ // p.1 + p.2 = k} := ⟨(k, 0), rfl⟩
  have hcoe : ∀ x, exteriorProdMul (K := K) (S₁ := S₁) (S₂ := S₂) k 0 x =
      exteriorProdDegree k (DirectSum.lof K _
        (fun p : {p : ℕ × ℕ // p.1 + p.2 = k} => ⋀[K]^p.1.1 S₁ ⊗[K] ⋀[K]^p.1.2 S₂) p₀ x) := by
    intro x
    apply Subtype.ext
    simp [exteriorProdDegree, DirectSum.toModule_lof, p₀]
  have hbij := spec_a3a_exteriorProdDegree_bijective_aux (K := K) (S₁ := S₁) (S₂ := S₂) k
  refine ⟨fun x y hxy => ?_, fun y => ?_⟩
  · rw [hcoe, hcoe] at hxy
    exact DirectSum.of_injective p₀ (hbij.1 hxy)
  · obtain ⟨w, hw⟩ := hbij.2 y
    refine ⟨w p₀, ?_⟩
    rw [hcoe, ← hw]
    congr 1
    refine DFinsupp.ext fun p => ?_
    by_cases hp : p = p₀
    · subst hp
      rw [DirectSum.lof_eq_of, DirectSum.of_eq_same]
    · have hp2 : p.1.2 ≠ 0 := by
        intro h2
        apply hp
        apply Subtype.ext
        have := p.2
        ext <;> simp_all [p₀]
      have := a3a_subsingleton_exteriorPower (K := K) (S₂ := S₂) hp2
      exact Subsingleton.elim _ _

theorem spec_a3a_exteriorDer_zero_aux {M : Type*} [AddCommGroup M] [Module K M]
    (f : Module.End K M) : exteriorDer 0 f = 0 := by
  ext v
  simp [exteriorDer, SchurWeyl.tensorDer]

theorem spec_a3a_not_exists_ungraded_algHom_aux (h2 : (2 : K) ≠ 0) :
    ¬ ∃ φ : ExteriorAlgebra K K ⊗[K] ExteriorAlgebra K K →ₐ[K] ExteriorAlgebra K (K × K),
      φ (ExteriorAlgebra.ι K 1 ⊗ₜ[K] 1) = ExteriorAlgebra.ι K (1, 0) ∧
        φ (1 ⊗ₜ[K] ExteriorAlgebra.ι K 1) = ExteriorAlgebra.ι K (0, 1) := by
  rintro ⟨φ, h₁, h₂⟩
  set e₁ := ExteriorAlgebra.ι K ((1, 0) : K × K)
  set e₂ := ExteriorAlgebra.ι K ((0, 1) : K × K)
  have hcomm : e₁ * e₂ = e₂ * e₁ := by
    rw [← h₁, ← h₂, ← map_mul, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul,
      Algebra.TensorProduct.tmul_mul_tmul]
    simp only [one_mul, mul_one]
  have hanti : e₁ * e₂ = -(e₂ * e₁) := by
    rw [eq_neg_iff_add_eq_zero]
    exact ExteriorAlgebra.ι_add_mul_swap _ _
  have hzero : e₁ * e₂ = 0 := by
    have h : (2 : K) • (e₁ * e₂) = 0 := by
      rw [two_smul]
      nth_rewrite 2 [hcomm]
      rw [hanti, neg_add_cancel]
    exact (smul_eq_zero.mp h).resolve_left h2
  have hE : ExteriorAlgebra.prodEquivTensor K K K (e₁ * e₂) =
      ExteriorAlgebra.ι K (1 : K) ᵍ⊗ₜ[K] ExteriorAlgebra.ι K (1 : K) := by
    rw [map_mul]
    simp only [ExteriorAlgebra.prodEquivTensor, AlgEquiv.ofAlgHom_apply, e₁, e₂,
      ExteriorAlgebra.prodEquivTensorForward_ι_apply, map_zero, GradedTensorProduct.tmul,
      TensorProduct.tmul_zero, TensorProduct.zero_tmul, add_zero, zero_add]
    exact GradedTensorProduct.tmul_one_mul_one_tmul (fun i : ℕ => ⋀[K]^i K)
      (fun i : ℕ => ⋀[K]^i K) _ _
  rw [hzero, map_zero] at hE
  have := congrArg (fun x => TensorProduct.lid K K (TensorProduct.map ExteriorAlgebra.ιInv
    ExteriorAlgebra.ιInv ((GradedTensorProduct.of K (fun i : ℕ => ⋀[K]^i K)
      (fun i : ℕ => ⋀[K]^i K)).symm x))) hE
  simp only [map_zero] at this
  rw [eq_comm] at this
  simp [ExteriorAlgebra.ι_leftInverse (R := K) (1 : K)] at this

variable [CharZero K]

theorem spec_a3a_exteriorDer_comp_exteriorProdMul_aux (i j : ℕ) (f₁ : Module.End K S₁)
    (f₂ : Module.End K S₂) :
    exteriorDer (i + j) (f₁.prodMap f₂) ∘ₗ exteriorProdMul i j =
      exteriorProdMul i j ∘ₗ
        ((exteriorDer i f₁).rTensor (⋀[K]^j S₂) + (exteriorDer j f₂).lTensor (⋀[K]^i S₁)) := by
  apply TensorProduct.ext'
  intro a b
  simp only [exteriorProdMul, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.rTensor_tmul,
    LinearMap.lTensor_tmul, map_add, TensorProduct.lift.tmul, LinearMap.compl₂_apply,
    exteriorDer_wedge]
  rw [exteriorDer_map i f₁ _ _ (by ext <;> simp), exteriorDer_map j f₂ _ _ (by ext <;> simp)]

omit [CharZero K] in
theorem a3a_exteriorDer_ofEq {M : Type*} [AddCommGroup M] [Module K M] {n m : ℕ} (h : n = m)
    (f : Module.End K M) (v : ⋀[K]^n M) :
    exteriorDer m f (LinearEquiv.ofEq _ _ (congrArg (fun n => ⋀[K]^n M) h) v) =
      LinearEquiv.ofEq _ _ (congrArg (fun n => ⋀[K]^n M) h) (exteriorDer n f v) := by
  subst h
  rfl

theorem a3a_exteriorDer_exteriorProdDegree_lof (k : ℕ) (f₁ : Module.End K S₁)
    (f₂ : Module.End K S₂) (p : {p : ℕ × ℕ // p.1 + p.2 = k})
    (x : ⋀[K]^p.1.1 S₁ ⊗[K] ⋀[K]^p.1.2 S₂) :
    exteriorDer k (f₁.prodMap f₂) (exteriorProdDegree k (DirectSum.lof K _ _ p x)) =
      exteriorProdDegree k (DirectSum.lof K _ _ p
        (((exteriorDer p.1.1 f₁).rTensor (⋀[K]^p.1.2 S₂) +
          (exteriorDer p.1.2 f₂).lTensor (⋀[K]^p.1.1 S₁)) x)) := by
  simp only [exteriorProdDegree, DirectSum.toModule_lof, LinearMap.comp_apply,
    LinearEquiv.coe_coe]
  rw [a3a_exteriorDer_ofEq p.2, ← LinearMap.comp_apply (exteriorDer _ _),
    spec_a3a_exteriorDer_comp_exteriorProdMul_aux, LinearMap.comp_apply]

omit [CharZero K] in
theorem a3a_mem_iSup_range_lof {ι : Type*} [DecidableEq ι] {M N : ι → Type*}
    [∀ i, AddCommMonoid (M i)] [∀ i, Module K (M i)] [∀ i, AddCommMonoid (N i)]
    [∀ i, Module K (N i)] {P : Type*} [AddCommMonoid P] [Module K P]
    (φ : (⨁ i, M i) →ₗ[K] P) (g : ∀ i, N i →ₗ[K] M i) (y : ⨁ i, M i)
    (hy : ∀ i, y i ∈ LinearMap.range (g i)) :
    φ y ∈ ⨆ i, LinearMap.range (φ ∘ₗ DirectSum.lof K ι M i ∘ₗ g i) := by
  classical
  rw [← DirectSum.sum_support_of y, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  obtain ⟨t, ht⟩ := hy i
  exact Submodule.mem_iSup_of_mem i ⟨t, by simp only [LinearMap.comp_apply, ht]; rfl⟩

theorem a3a_tensor_invariants_exteriorDer {𝔤₁ 𝔤₂ : Type*} [LieRing 𝔤₁] [LieAlgebra K 𝔤₁]
    [LieRing 𝔤₂] [LieAlgebra K 𝔤₂] [FiniteDimensional K S₁] [FiniteDimensional K S₂]
    (ρ₁ : 𝔤₁ →ₗ⁅K⁆ Module.End K S₁) (ρ₂ : 𝔤₂ →ₗ⁅K⁆ Module.End K S₂) (n m : ℕ) :
    (⨅ x : 𝔤₁ × 𝔤₂, LinearMap.ker ((exteriorDer n (ρ₁ x.1)).rTensor (⋀[K]^m S₂) +
        (exteriorDer m (ρ₂ x.2)).lTensor (⋀[K]^n S₁))) =
      LinearMap.range (TensorProduct.map (⨅ x, LinearMap.ker (exteriorDer n (ρ₁ x))).subtype
        (⨅ y, LinearMap.ker (exteriorDer m (ρ₂ y))).subtype) :=
  spec_a3a_tensor_invariants_aux ((exteriorLie (K := K) (M := S₁) n).comp ρ₁)
    ((exteriorLie (K := K) (M := S₂) m).comp ρ₂)

theorem spec_a3a_exterior_invariants_aux {𝔤₁ 𝔤₂ : Type*} [LieRing 𝔤₁] [LieAlgebra K 𝔤₁]
    [LieRing 𝔤₂] [LieAlgebra K 𝔤₂] [FiniteDimensional K S₁] [FiniteDimensional K S₂]
    (ρ₁ : 𝔤₁ →ₗ⁅K⁆ Module.End K S₁) (ρ₂ : 𝔤₂ →ₗ⁅K⁆ Module.End K S₂) (k : ℕ) :
    (⨅ x : 𝔤₁ × 𝔤₂, LinearMap.ker (exteriorDer k ((ρ₁ x.1).prodMap (ρ₂ x.2)))) =
      ⨆ p : {p : ℕ × ℕ // p.1 + p.2 = k},
        LinearMap.range (exteriorProdDegree k ∘ₗ
          DirectSum.lof K _ (fun p : {p : ℕ × ℕ // p.1 + p.2 = k} =>
            ⋀[K]^p.1.1 S₁ ⊗[K] ⋀[K]^p.1.2 S₂) p ∘ₗ
          TensorProduct.map (⨅ x, LinearMap.ker (exteriorDer p.1.1 (ρ₁ x))).subtype
            (⨅ y, LinearMap.ker (exteriorDer p.1.2 (ρ₂ y))).subtype) := by
  classical
  -- the componentwise action on the direct sum
  let T : 𝔤₁ × 𝔤₂ → ∀ p : {p : ℕ × ℕ // p.1 + p.2 = k},
      Module.End K (⋀[K]^p.1.1 S₁ ⊗[K] ⋀[K]^p.1.2 S₂) := fun x p =>
    (exteriorDer p.1.1 (ρ₁ x.1)).rTensor (⋀[K]^p.1.2 S₂) +
      (exteriorDer p.1.2 (ρ₂ x.2)).lTensor (⋀[K]^p.1.1 S₁)
  have hT : ∀ (x : 𝔤₁ × 𝔤₂) y,
      exteriorDer k ((ρ₁ x.1).prodMap (ρ₂ x.2)) (exteriorProdDegree k y) =
        exteriorProdDegree k (DirectSum.lmap (T x) y) := by
    intro x y
    induction y using DirectSum.induction_on with
    | zero => simp
    | of p z =>
      rw [← DirectSum.lof_eq_of K, DirectSum.lmap_lof]
      exact a3a_exteriorDer_exteriorProdDegree_lof k (ρ₁ x.1) (ρ₂ x.2) p z
    | add y y' hy hy' => simp only [map_add, hy, hy']
  have hS1 : ∀ p : {p : ℕ × ℕ // p.1 + p.2 = k},
      (⨅ x : 𝔤₁ × 𝔤₂, LinearMap.ker (T x p)) =
        LinearMap.range (TensorProduct.map (⨅ x, LinearMap.ker (exteriorDer p.1.1 (ρ₁ x))).subtype
          (⨅ y, LinearMap.ker (exteriorDer p.1.2 (ρ₂ y))).subtype) := by
    intro p
    exact a3a_tensor_invariants_exteriorDer ρ₁ ρ₂ p.1.1 p.1.2
  have hT0 : ∀ (x : 𝔤₁ × 𝔤₂) (p : {p : ℕ × ℕ // p.1 + p.2 = k})
      (z : ⋀[K]^p.1.1 S₁ ⊗[K] ⋀[K]^p.1.2 S₂),
      exteriorDer k ((ρ₁ x.1).prodMap (ρ₂ x.2)) (exteriorProdDegree k (DirectSum.lof K _ _ p z)) =
        exteriorProdDegree k (DirectSum.lof K _ _ p (T x p z)) := fun x p z =>
    a3a_exteriorDer_exteriorProdDegree_lof k (ρ₁ x.1) (ρ₂ x.2) p z
  clear_value T
  apply le_antisymm
  · intro v hv
    obtain ⟨y, rfl⟩ := (spec_a3a_exteriorProdDegree_bijective_aux (K := K) (S₁ := S₁)
      (S₂ := S₂) k).2 v
    have hy : ∀ x, DirectSum.lmap (T x) y = 0 := by
      intro x
      apply (spec_a3a_exteriorProdDegree_bijective_aux (K := K) (S₁ := S₁) (S₂ := S₂) k).1
      rw [← hT, map_zero]
      exact (Submodule.mem_iInf _).mp hv x
    refine a3a_mem_iSup_range_lof (exteriorProdDegree k)
      (fun p : {p : ℕ × ℕ // p.1 + p.2 = k} =>
        TensorProduct.map (⨅ x, LinearMap.ker (exteriorDer p.1.1 (ρ₁ x))).subtype
          (⨅ y, LinearMap.ker (exteriorDer p.1.2 (ρ₂ y))).subtype) y fun p => ?_
    rw [← hS1 p]
    refine (Submodule.mem_iInf _).mpr fun x => ?_
    have := DFunLike.congr_fun (hy x) p
    rw [DirectSum.lmap_apply, DirectSum.zero_apply] at this
    exact LinearMap.mem_ker.mpr this
  · refine iSup_le fun p => ?_
    rintro _ ⟨t, rfl⟩
    refine (Submodule.mem_iInf _).mpr fun x => ?_
    have ht : TensorProduct.map (⨅ x, LinearMap.ker (exteriorDer p.1.1 (ρ₁ x))).subtype
        (⨅ y, LinearMap.ker (exteriorDer p.1.2 (ρ₂ y))).subtype t ∈
          ⨅ x : 𝔤₁ × 𝔤₂, LinearMap.ker (T x p) := by
      rw [hS1 p]; exact ⟨t, rfl⟩
    have := (Submodule.mem_iInf _).mp ht x
    rw [LinearMap.mem_ker] at this ⊢
    simp only [LinearMap.comp_apply]
    rw [hT0, this, map_zero, map_zero]

end Exterior

end HodgeLean.Foundations
