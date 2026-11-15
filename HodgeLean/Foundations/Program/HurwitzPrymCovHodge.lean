import HodgeLean.Foundations.Program.HurwitzPrymCovLoop

set_option maxHeartbeats 400000

/-! # Track B4, lane `b4-cov`: the equivariant Hodge isomorphism `F_C ≅ Ω¹(C)`

A finite group acting linearly on a finite-dimensional complex space `Ω` preserves a positive
Hermitian form (average of a coordinate form), whose Riesz map `Ω^∨ → Ω` is a conjugate-linear
`G`-bijection. Composing it with the period pairing `F̄_C ≅ Ω^∨` and complex conjugation
`F_C → F̄_C` gives a linear `G`-isomorphism `F_C ≅ Ω¹(C)`, hence equal multiplicities.
HC no distance; AV milestone no distance.
-/

noncomputable section

open Manifold Set Filter Topology
open scoped ContDiff TensorProduct ComplexConjugate

namespace HodgeLean.Foundations.Program

section Riesz

variable {Ω : Type*} [AddCommGroup Ω] [Module ℂ Ω] [FiniteDimensional ℂ Ω]
variable {G : Type*} [Group G] [Fintype G]

/-- The averaged coordinate form `h(θ, η) = Σ_g Σ_i conj ⟨τ_g θ⟩_i ⟨τ_g η⟩_i`, as a functional
in `η`. -/
def b4cov_herm (τ : G → Ω →ₗ[ℂ] Ω) (θ : Ω) : Module.Dual ℂ Ω :=
  ∑ g, ∑ i, conj ((Module.finBasis ℂ Ω).repr (τ g θ) i) •
    ((Module.finBasis ℂ Ω).coord i ∘ₗ τ g)

theorem b4cov_herm_apply (τ : G → Ω →ₗ[ℂ] Ω) (θ η : Ω) :
    b4cov_herm τ θ η = ∑ g, ∑ i, conj ((Module.finBasis ℂ Ω).repr (τ g θ) i) *
      (Module.finBasis ℂ Ω).repr (τ g η) i := by
  simp [b4cov_herm, LinearMap.sum_apply, Module.Basis.coord_apply]

theorem b4cov_herm_add (τ : G → Ω →ₗ[ℂ] Ω) (θ θ' : Ω) :
    b4cov_herm τ (θ + θ') = b4cov_herm τ θ + b4cov_herm τ θ' := by
  ext η
  simp only [b4cov_herm_apply, LinearMap.add_apply, map_add, Finsupp.add_apply, add_mul,
    Finset.sum_add_distrib]

theorem b4cov_herm_smul (τ : G → Ω →ₗ[ℂ] Ω) (a : ℂ) (θ : Ω) :
    b4cov_herm τ (a • θ) = conj a • b4cov_herm τ θ := by
  ext η
  simp only [b4cov_herm_apply, LinearMap.smul_apply, map_smul, Finsupp.smul_apply, smul_eq_mul,
    map_mul, Finset.mul_sum, mul_assoc]

theorem b4cov_herm_self_eq_zero (τ : G → Ω →ₗ[ℂ] Ω) (hτ1 : τ 1 = LinearMap.id) (θ : Ω)
    (h : b4cov_herm τ θ θ = 0) : θ = 0 := by
  rw [b4cov_herm_apply] at h
  have hre := congrArg Complex.re h
  simp only [Complex.re_sum, Complex.zero_re] at hre
  have hnn : ∀ g i, 0 ≤ (conj ((Module.finBasis ℂ Ω).repr (τ g θ) i) *
      (Module.finBasis ℂ Ω).repr (τ g θ) i).re := fun g i ↦ by
    rw [mul_comm, Complex.mul_conj]; simp [Complex.normSq_nonneg]
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun g _ ↦
    Finset.sum_nonneg fun i _ ↦ hnn g i).1 hre 1 (Finset.mem_univ _)
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ hnn 1 i).1 h1
  rw [hτ1] at h2
  apply (Module.finBasis ℂ Ω).repr.injective
  ext i
  have := h2 i (Finset.mem_univ _)
  rw [mul_comm, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_zero] at this
  simpa using this

theorem b4cov_herm_invariant (τ : G → Ω →ₗ[ℂ] Ω) (hτ1 : τ 1 = LinearMap.id)
    (hτmul : ∀ g h, τ (g * h) = τ g ∘ₗ τ h) (k : G) (θ : Ω) :
    b4cov_herm τ (τ k θ) = b4cov_herm τ θ ∘ₗ τ k⁻¹ := by
  ext η
  rw [LinearMap.comp_apply, b4cov_herm_apply, b4cov_herm_apply]
  refine (Fintype.sum_equiv (Equiv.mulRight k) _ _ fun g ↦ ?_)
  have e1 : τ (g * k) θ = τ g (τ k θ) := by rw [hτmul]; rfl
  have e2 : τ (g * k) (τ k⁻¹ η) = τ g η := by
    rw [hτmul, LinearMap.comp_apply, ← LinearMap.comp_apply (τ k) (τ k⁻¹), ← hτmul,
      mul_inv_cancel, hτ1]
    rfl
  simp only [Equiv.coe_mulRight]
  rw [e1, e2]

theorem b4cov_herm_injective (τ : G → Ω →ₗ[ℂ] Ω) (hτ1 : τ 1 = LinearMap.id) :
    Function.Injective (b4cov_herm τ) := by
  intro θ θ' h
  have hsub : b4cov_herm τ (θ - θ') = 0 := by
    rw [sub_eq_add_neg, b4cov_herm_add, ← neg_one_smul ℂ θ', b4cov_herm_smul, h, map_neg,
      map_one, neg_one_smul, add_neg_cancel]
  have := b4cov_herm_self_eq_zero τ hτ1 (θ - θ') (by rw [hsub]; rfl)
  exact sub_eq_zero.1 this

/-- The coordinate conjugation of `Ω`. -/
def b4cov_kappa (θ : Ω) : Ω :=
  (Module.finBasis ℂ Ω).equivFun.symm fun i ↦ conj ((Module.finBasis ℂ Ω).equivFun θ i)

theorem b4cov_kappa_add (θ θ' : Ω) : b4cov_kappa (θ + θ') = b4cov_kappa θ + b4cov_kappa θ' := by
  simp only [b4cov_kappa, map_add, Pi.add_apply]
  rw [← map_add]
  rfl

theorem b4cov_kappa_smul (a : ℂ) (θ : Ω) : b4cov_kappa (a • θ) = conj a • b4cov_kappa θ := by
  simp only [b4cov_kappa, map_smul, Pi.smul_apply, smul_eq_mul, map_mul]
  rw [← map_smul]
  rfl

theorem b4cov_kappa_kappa (θ : Ω) : b4cov_kappa (b4cov_kappa θ) = θ := by
  simp only [b4cov_kappa, LinearEquiv.apply_symm_apply, Complex.conj_conj]
  exact (Module.finBasis ℂ Ω).equivFun.symm_apply_apply θ

theorem b4cov_herm_surjective (τ : G → Ω →ₗ[ℂ] Ω) (hτ1 : τ 1 = LinearMap.id) :
    Function.Surjective (b4cov_herm τ) := by
  let L : Ω →ₗ[ℂ] Module.Dual ℂ Ω :=
    { toFun := fun θ ↦ b4cov_herm τ (b4cov_kappa θ)
      map_add' := fun θ θ' ↦ by rw [b4cov_kappa_add, b4cov_herm_add]
      map_smul' := fun a θ ↦ by
        rw [b4cov_kappa_smul, b4cov_herm_smul, Complex.conj_conj]; rfl }
  have hinj : Function.Injective L := fun θ θ' h ↦ by
    have := b4cov_herm_injective τ hτ1 h
    rw [← b4cov_kappa_kappa θ, ← b4cov_kappa_kappa θ']
    exact congrArg b4cov_kappa this
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (Subspace.dual_finrank_eq).symm).1 hinj
  intro u
  obtain ⟨θ, hθ⟩ := hsurj u
  exact ⟨b4cov_kappa θ, hθ⟩

/-- **The invariant Riesz map** `Ω^∨ → Ω`: conjugate-linear, bijective, `G`-equivariant. -/
theorem b4cov_exists_riesz (τ : G → Ω →ₗ[ℂ] Ω) (hτ1 : τ 1 = LinearMap.id)
    (hτmul : ∀ g h, τ (g * h) = τ g ∘ₗ τ h) :
    ∃ R : Module.Dual ℂ Ω → Ω, Function.Bijective R ∧ (∀ u u', R (u + u') = R u + R u') ∧
      (∀ (a : ℂ) u, R (a • u) = conj a • R u) ∧ ∀ g u, R (u ∘ₗ τ g⁻¹) = τ g (R u) := by
  let e := Equiv.ofBijective (b4cov_herm τ)
    ⟨b4cov_herm_injective τ hτ1, b4cov_herm_surjective τ hτ1⟩
  have he : ∀ u, b4cov_herm τ (e.symm u) = u := e.apply_symm_apply
  have hinj := b4cov_herm_injective τ hτ1
  refine ⟨e.symm, e.symm.bijective, fun u u' ↦ hinj ?_, fun a u ↦ hinj ?_, fun g u ↦ hinj ?_⟩
  · rw [he, b4cov_herm_add, he, he]
  · rw [he, b4cov_herm_smul, he, Complex.conj_conj]
  · rw [he, b4cov_herm_invariant τ hτ1 hτmul, he]

end Riesz

section Transfer

variable {G : Type*} [Group G]
variable {V M₁ M₂ : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup M₁] [Module ℂ M₁]
  [AddCommGroup M₂] [Module ℂ M₂]

/-- **`G`-maps transfer along an equivariant isomorphism of stable subspaces.** -/
theorem b4cov_finrank_homG_congr (ρ : Representation ℂ G V) (act₁ : G → M₁ →ₗ[ℂ] M₁)
    (act₂ : G → M₂ →ₗ[ℂ] M₂) (W₁ : Submodule ℂ M₁) (W₂ : Submodule ℂ M₂)
    (h₁ : ∀ g, W₁ ≤ W₁.comap (act₁ g)) (h₂ : ∀ g, W₂ ≤ W₂.comap (act₂ g)) (T : W₁ ≃ₗ[ℂ] W₂)
    (hT : ∀ g (w : W₁), (T ⟨act₁ g w, h₁ g w.2⟩ : M₂) = act₂ g (T w)) :
    Module.finrank ℂ (b4_HomG ρ act₁ W₁) = Module.finrank ℂ (b4_HomG ρ act₂ W₂) := by
  have hT' : ∀ g (w : W₂), (T.symm ⟨act₂ g w, h₂ g w.2⟩ : M₁) = act₁ g (T.symm w) := by
    intro g w
    have := hT g (T.symm w)
    rw [LinearEquiv.apply_symm_apply] at this
    have h' : T ⟨act₁ g (T.symm w), h₁ g (T.symm w).2⟩ = ⟨act₂ g w, h₂ g w.2⟩ := Subtype.ext this
    rw [← h', LinearEquiv.symm_apply_apply]
  let Φ : b4_HomG ρ act₁ W₁ →ₗ[ℂ] b4_HomG ρ act₂ W₂ :=
    { toFun := fun φ ↦ ⟨W₂.subtype ∘ₗ T.toLinearMap ∘ₗ (φ : V →ₗ[ℂ] M₁).codRestrict W₁ φ.2.1,
        fun v ↦ (T _).2, fun g v ↦ by
          simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe]
          rw [← hT g]
          congr 2
          exact Subtype.ext (φ.2.2 g v)⟩
      map_add' := fun φ ψ ↦ by
        ext v
        change ((T ((⟨(φ : V →ₗ[ℂ] _) v, φ.2.1 v⟩ : W₁) + ⟨(ψ : V →ₗ[ℂ] _) v, ψ.2.1 v⟩) : W₂) :
          M₂) = _
        rw [map_add]; rfl
      map_smul' := fun a φ ↦ by
        ext v
        change ((T (a • (⟨(φ : V →ₗ[ℂ] _) v, φ.2.1 v⟩ : W₁)) : W₂) : M₂) = _
        rw [map_smul]; rfl }
  let Ψ : b4_HomG ρ act₂ W₂ →ₗ[ℂ] b4_HomG ρ act₁ W₁ :=
    { toFun := fun φ ↦ ⟨W₁.subtype ∘ₗ T.symm.toLinearMap ∘ₗ (φ : V →ₗ[ℂ] M₂).codRestrict W₂ φ.2.1,
        fun v ↦ (T.symm _).2, fun g v ↦ by
          simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe]
          rw [← hT' g]
          congr 2
          exact Subtype.ext (φ.2.2 g v)⟩
      map_add' := fun φ ψ ↦ by
        ext v
        change ((T.symm ((⟨(φ : V →ₗ[ℂ] _) v, φ.2.1 v⟩ : W₂) + ⟨(ψ : V →ₗ[ℂ] _) v, ψ.2.1 v⟩) :
          W₁) : M₁) = _
        rw [map_add]; rfl
      map_smul' := fun a φ ↦ by
        ext v
        change ((T.symm (a • (⟨(φ : V →ₗ[ℂ] _) v, φ.2.1 v⟩ : W₂)) : W₁) : M₁) = _
        rw [map_smul]; rfl }
  refine LinearEquiv.finrank_eq
    { Φ with
      invFun := Ψ
      left_inv := fun φ ↦ by
        ext v
        change ((T.symm (T ⟨(φ : V →ₗ[ℂ] M₁) v, φ.2.1 v⟩) : W₁) : M₁) = _
        rw [LinearEquiv.symm_apply_apply]
      right_inv := fun φ ↦ by
        ext v
        change ((T (T.symm ⟨(φ : V →ₗ[ℂ] M₂) v, φ.2.1 v⟩) : W₂) : M₂) = _
        rw [LinearEquiv.apply_symm_apply] }

end Transfer

section Conj

variable {Λ : Type*} [AddCommGroup Λ]

theorem b4cov_conj_smul (a : ℂ) (v : ℂ ⊗[ℤ] Λ) : b2_conj Λ (a • v) = conj a • b2_conj Λ v := by
  induction v using TensorProduct.inductionOn with
  | tmul b l =>
    rw [TensorProduct.smul_tmul']
    change (starRingEnd ℂ (a • b)) ⊗ₜ[ℤ] l = conj a • (starRingEnd ℂ b ⊗ₜ[ℤ] l)
    rw [TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, map_mul]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

theorem b4cov_conj_conj (v : ℂ ⊗[ℤ] Λ) : b2_conj Λ (b2_conj Λ v) = v := by
  induction v using TensorProduct.inductionOn with
  | tmul b l =>
    change (starRingEnd ℂ (starRingEnd ℂ b)) ⊗ₜ[ℤ] l = b ⊗ₜ[ℤ] l
    rw [Complex.conj_conj]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- Every vector of `F̄` is the conjugate of a vector of `F`. -/
theorem b4cov_mem_conjSubmodule (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (w : ℂ ⊗[ℤ] Λ)
    (hw : w ∈ b2_conjSubmodule Λ F) : ∃ v ∈ F, b2_conj Λ v = w := by
  let S : Submodule ℂ (ℂ ⊗[ℤ] Λ) :=
    { carrier := b2_conj Λ '' F
      add_mem' := by
        rintro _ _ ⟨v, hv, rfl⟩ ⟨v', hv', rfl⟩
        exact ⟨v + v', F.add_mem hv hv', map_add _ _ _⟩
      zero_mem' := ⟨0, F.zero_mem, map_zero _⟩
      smul_mem' := by
        rintro a _ ⟨v, hv, rfl⟩
        refine ⟨conj a • v, F.smul_mem _ hv, ?_⟩
        rw [b4cov_conj_smul, Complex.conj_conj] }
  have : b2_conjSubmodule Λ F ≤ S := Submodule.span_le.2 fun x hx ↦ hx
  exact this hw

end Conj

section Surface

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
variable {G : Type} [Group G] [MulAction G C]

/-- **Pullbacks compose contravariantly.** -/
theorem b4cov_pullback_comp (f₁ f₂ : C → C) (h₁ : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω f₁)
    (h₂ : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω f₂) (θ : TangentBundle 𝓘(ℂ, E) C → ℂ) :
    b3_pullback E E f₁ (b3_pullback E E f₂ θ) = b3_pullback E E (f₂ ∘ f₁) θ := by
  funext p
  change θ ⟨f₂ (f₁ p.1), mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E) f₂ (f₁ p.1)
    (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E) f₁ p.1 p.2)⟩ =
      θ ⟨(f₂ ∘ f₁) p.1, mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E) (f₂ ∘ f₁) p.1 p.2⟩
  rw [mfderiv_comp_apply (g := f₂) (f := f₁) p.1 ((h₂ _).mdifferentiableAt (by simp))
    ((h₁ _).mdifferentiableAt (by simp))]
  rfl

theorem b4cov_formAct_one (θ : TangentBundle 𝓘(ℂ, E) C → ℂ) :
    b4_formAct E (C := C) (1 : G) θ = θ := by
  have : (fun x : C ↦ (1 : G)⁻¹ • x) = id := funext fun x ↦ by simp
  funext p
  change θ ⟨(fun x : C ↦ (1 : G)⁻¹ • x) p.1, mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E)
    (fun x : C ↦ (1 : G)⁻¹ • x) p.1 p.2⟩ = θ p
  rw [this, mfderiv_id]
  rfl

theorem b4cov_formAct_mul (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ g • x))
    (g h : G) (θ : TangentBundle 𝓘(ℂ, E) C → ℂ) :
    b4_formAct E (C := C) (g * h) θ = b4_formAct E g (b4_formAct E h θ) := by
  have hc : (fun x : C ↦ (g * h)⁻¹ • x) = (fun x : C ↦ h⁻¹ • x) ∘ (fun x : C ↦ g⁻¹ • x) :=
    funext fun x ↦ by simp [mul_smul]
  simp only [b4_formAct]
  rw [b4cov_pullback_comp _ _ (hG g⁻¹) (hG h⁻¹), hc]

/-- The action on holomorphic forms. -/
def b4cov_tau (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ g • x)) (g : G) :
    b3_HolForm E C →ₗ[ℂ] b3_HolForm E C :=
  (b4_formAct E g).restrict fun θ hθ ↦ b3_pullback_mem_holForm _ (hG g⁻¹) θ hθ

theorem b4cov_tau_one (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ g • x)) :
    b4cov_tau hG 1 = LinearMap.id := by
  ext θ
  exact congrFun (b4cov_formAct_one (G := G) (θ : TangentBundle 𝓘(ℂ, E) C → ℂ)) _

theorem b4cov_tau_mul (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ g • x))
    (g h : G) : b4cov_tau hG (g * h) = b4cov_tau hG g ∘ₗ b4cov_tau hG h := by
  ext θ
  exact congrFun (b4cov_formAct_mul hG g h (θ : TangentBundle 𝓘(ℂ, E) C → ℂ)) _

/-- **The lattice action is the transpose of the pullback**: `(g_* λ)(θ) = λ(g^* θ)`. -/
theorem b4cov_latticeAct_apply (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ g • x))
    (g : G) (hpush : b3_IsPushforward E E (fun x : C ↦ g • x) (b4_latticeAct E g))
    (l : b3_periodLattice E C) (θ : b3_HolForm E C) :
    (b4_latticeAct E g l : b3_HolForm E C → ℂ) θ = (l : b3_HolForm E C → ℂ) (b4cov_tau hG g⁻¹ θ) := by
  obtain ⟨l, hl⟩ := l
  induction hl using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨γ, rfl⟩ := hx
    have h1 := hpush γ (b4cov_mapLoop _ (hG g) γ) rfl
    change ((b4_latticeAct E g (b3_latticePeriod E C γ) : b3_periodLattice E C) :
      b3_HolForm E C → ℂ) θ = _
    rw [h1]
    change b3_pathIntegral E C ((fun x : C ↦ g • x) ∘ γ.1) θ =
      b3_pathIntegral E C γ.1 (b4_formAct E g⁻¹ θ)
    rw [b3_pathIntegral_comp _ (hG g) γ.1 γ.2.2]
    simp only [b4_formAct, inv_inv]
  | zero =>
    rw [show (⟨0, AddSubgroup.zero_mem _⟩ : b3_periodLattice E C) = 0 from rfl, map_zero]
    rfl
  | add x y hx hy ihx ihy =>
    have := map_add (b4_latticeAct E (C := C) g) ⟨x, hx⟩ ⟨y, hy⟩
    rw [show (⟨x + y, AddSubgroup.add_mem _ hx hy⟩ : b3_periodLattice E C) = ⟨x, hx⟩ + ⟨y, hy⟩
      from rfl, this]
    simp only [AddSubgroup.coe_add, Pi.add_apply, ihx, ihy]
  | neg x hx ih =>
    rw [show (⟨-x, AddSubgroup.neg_mem _ hx⟩ : b3_periodLattice E C) = -⟨x, hx⟩ from rfl, map_neg]
    simp only [AddSubgroup.coe_neg, Pi.neg_apply, ih]

theorem b4cov_cplxPeriod_cplxAct
    (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ g • x)) (g : G)
    (hpush : b3_IsPushforward E E (fun x : C ↦ g • x) (b4_latticeAct E g))
    (w : ℂ ⊗[ℤ] b3_periodLattice E C) (θ : b3_HolForm E C) :
    b3_cplxPeriod E C (b4_cplxAct E g w) θ = b3_cplxPeriod E C w (b4cov_tau hG g⁻¹ θ) := by
  induction w using TensorProduct.inductionOn with
  | tmul a l =>
    change (a • ((b4_latticeAct E g l : b3_periodLattice E C) : b3_HolForm E C → ℂ)) θ =
      (a • (l : b3_HolForm E C → ℂ)) (b4cov_tau hG g⁻¹ θ)
    simp only [Pi.smul_apply, b4cov_latticeAct_apply hG g hpush]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

/-- A functional in `b3_linearDual` as an element of the dual. -/
def b4cov_toDual (u : b3_HolForm E C → ℂ) (hu : u ∈ b3_linearDual E C) :
    Module.Dual ℂ (b3_HolForm E C) where
  toFun := u
  map_add' θ η := by
    have h0 : u 0 = 0 := by
      have := hu 1 0 0
      simp only [one_smul, add_zero, one_mul] at this
      linear_combination -this
    have := hu 1 θ η
    simpa only [one_smul, one_mul] using this
  map_smul' a θ := by
    have := hu a θ 0
    have h0 : u 0 = 0 := by
      have := hu 1 0 0
      simp only [one_smul, add_zero, one_mul] at this
      linear_combination -this
    simpa only [add_zero, h0, RingHom.id_apply, smul_eq_mul] using this

/-- **The equivariant Hodge isomorphism**: `F_C ≅ Ω¹(C)` as `G`-spaces, so multiplicities
agree. -/
theorem b4cov_hodge_eq_holo [Fintype G] [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1)
    (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ g • x))
    (hpush : ∀ g : G, b3_IsPushforward E E (fun x : C ↦ g • x) (b4_latticeAct E g))
    (hF : ∀ g : G, b3_periodF E C ≤ (b3_periodF E C).comap (b4_cplxAct E g))
    {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) :
    Module.finrank ℂ (b4_HomG ρ (fun g ↦ b4_cplxAct E (C := C) g) (b3_periodF E C)) =
      Module.finrank ℂ (b4_HomG ρ (fun g ↦ b4_formAct E (C := C) g) (b3_HolForm E C)) := by
  have := b3_holForm_finiteDimensional (C := C) hE
  have hwo := b3_isWeightOne (C := C) hE
  have hrange := b3_range_cplxPeriod (C := C) hE
  obtain ⟨R, hRbij, hRadd, hRsmul, hReq⟩ :=
    b4cov_exists_riesz (b4cov_tau hG) (b4cov_tau_one hG) (b4cov_tau_mul hG)
  have hR0 : R 0 = 0 := by
    have := hRadd 0 0
    rw [add_zero] at this
    exact left_eq_add.1 this
  have hmem : ∀ w, b3_cplxPeriod E C w ∈ b3_linearDual E C := fun w ↦
    hrange ▸ LinearMap.mem_range_self _ w
  let D : (ℂ ⊗[ℤ] b3_periodLattice E C) →ₗ[ℂ] Module.Dual ℂ (b3_HolForm E C) :=
    { toFun := fun w ↦ b4cov_toDual (b3_cplxPeriod E C w) (hmem w)
      map_add' := fun w w' ↦ by
        ext θ
        change b3_cplxPeriod E C (w + w') θ = b3_cplxPeriod E C w θ + b3_cplxPeriod E C w' θ
        rw [map_add]; rfl
      map_smul' := fun a w ↦ by
        ext θ
        change b3_cplxPeriod E C (a • w) θ = a • b3_cplxPeriod E C w θ
        rw [map_smul]; rfl }
  have hDapp : ∀ w θ, D w θ = b3_cplxPeriod E C w θ := fun _ _ ↦ rfl
  have hDσ : ∀ g w, D (b4_cplxAct E g w) = D w ∘ₗ b4cov_tau hG g⁻¹ := fun g w ↦ by
    ext θ
    exact b4cov_cplxPeriod_cplxAct hG g (hpush g) w θ
  have hDsurj : Function.Surjective D := by
    intro u
    have hu : (⇑u : b3_HolForm E C → ℂ) ∈ b3_linearDual E C := fun a θ η ↦ by
      rw [map_add, map_smul, smul_eq_mul]
    rw [← hrange] at hu
    obtain ⟨w, hw⟩ := hu
    exact ⟨w, LinearMap.ext fun θ ↦ by rw [hDapp, hw]⟩
  have hDF : ∀ w, D w = 0 ↔ w ∈ b3_periodF E C := by
    intro w
    change _ ↔ b3_cplxPeriod E C w = 0
    constructor
    · intro h
      funext θ
      exact (hDapp w θ).symm.trans (congrArg (fun L : Module.Dual ℂ _ ↦ L θ) h)
    · intro h
      ext θ
      rw [hDapp, h]; rfl
  let c := b2_conj (b3_periodLattice E C)
  let T : b3_periodF E C →ₗ[ℂ] b3_HolForm E C :=
    { toFun := fun v ↦ R (D (c v))
      map_add' := fun v v' ↦ by
        simp only [Submodule.coe_add, map_add]
        exact hRadd _ _
      map_smul' := fun a v ↦ by
        simp only [Submodule.coe_smul]
        change R (D (b2_conj _ (a • (v : ℂ ⊗[ℤ] b3_periodLattice E C)))) = _
        rw [b4cov_conj_smul, map_smul, hRsmul, Complex.conj_conj]; rfl }
  have hTinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro v hv
    have h1 : R (D (c v)) = R 0 := (LinearMap.mem_ker.1 hv).trans hR0.symm
    have h2 := (hDF _).1 (hRbij.1 h1)
    have h3 : c v ∈ b2_conjSubmodule _ (b3_periodF E C) := Submodule.subset_span ⟨v, v.2, rfl⟩
    have h4 : c v = 0 := by
      have := Submodule.mem_inf.2 ⟨h2, h3⟩
      rwa [hwo.inf_eq_bot, Submodule.mem_bot] at this
    have h5 : (v : ℂ ⊗[ℤ] b3_periodLattice E C) = 0 := by
      rw [← b4cov_conj_conj (v : ℂ ⊗[ℤ] b3_periodLattice E C)]
      change b2_conj _ (c v) = 0
      rw [h4, map_zero]
    exact (Submodule.mem_bot ℂ).2 (Subtype.ext h5)
  have hTsurj : Function.Surjective T := by
    intro θ
    obtain ⟨u, rfl⟩ := hRbij.2 θ
    obtain ⟨w, rfl⟩ := hDsurj u
    have hw : w ∈ b3_periodF E C ⊔ b2_conjSubmodule _ (b3_periodF E C) := by
      rw [hwo.sup_eq_top]; trivial
    obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := Submodule.mem_sup.1 hw
    obtain ⟨v, hv, rfl⟩ := b4cov_mem_conjSubmodule _ w₂ hw₂
    refine ⟨⟨v, hv⟩, ?_⟩
    change R (D (c v)) = R (D (w₁ + c v))
    rw [map_add, (hDF w₁).2 hw₁, zero_add]
  have hT : ∀ g (w : b3_periodF E C),
      ((T ⟨b4_cplxAct E g w, hF g w.2⟩ : b3_HolForm E C) : TangentBundle 𝓘(ℂ, E) C → ℂ) =
        b4_formAct E g ((T w : b3_HolForm E C) : TangentBundle 𝓘(ℂ, E) C → ℂ) := by
    intro g w
    change ((R (D (c (b4_cplxAct E g w))) : b3_HolForm E C) : TangentBundle 𝓘(ℂ, E) C → ℂ) =
      b4_formAct E g ((R (D (c w)) : b3_HolForm E C) : TangentBundle 𝓘(ℂ, E) C → ℂ)
    have hcσ : c (b4_cplxAct E g w) = b4_cplxAct E g (c w) :=
      (b2f_cplxMap_conj (b4_latticeAct E (C := C) g) (w : ℂ ⊗[ℤ] b3_periodLattice E C)).symm
    rw [hcσ, hDσ, hReq]
    rfl
  exact b4cov_finrank_homG_congr ρ _ _ _ _ hF
    (fun g θ hθ ↦ b3_pullback_mem_holForm _ (hG g⁻¹) θ hθ)
    (LinearEquiv.ofBijective T ⟨hTinj, hTsurj⟩) hT

end Surface

end HodgeLean.Foundations.Program
