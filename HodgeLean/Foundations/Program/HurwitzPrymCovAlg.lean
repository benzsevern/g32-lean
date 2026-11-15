import HodgeLean.Foundations.Program.HurwitzPrymDefs

set_option maxHeartbeats 400000

/-! # Track B4, lane `b4-cov`: linear algebra of complexified lattice maps

Additivity of `b2_cplxMap`, the splitting of `G`-maps along a stable decomposition
`M = F ⊕ F'`, and the dimensions of B2's image filtrations for an endomorphism preserving a
weight-one filtration.
HC no distance; AV milestone no distance.
-/

noncomputable section

open scoped TensorProduct

namespace HodgeLean.Foundations.Program

section CplxMap

variable {Λ Λ' : Type*} [AddCommGroup Λ] [AddCommGroup Λ']

theorem b4cov_cplxMap_add (f g : Λ' →+ Λ) :
    b2_cplxMap (f + g) = b2_cplxMap f + b2_cplxMap g := by
  refine LinearMap.ext fun v ↦ ?_
  induction v using TensorProduct.inductionOn with
  | tmul c x =>
    change c ⊗ₜ[ℤ] (f x + g x) = c ⊗ₜ[ℤ] f x + c ⊗ₜ[ℤ] g x
    rw [TensorProduct.tmul_add]
  | add x y hx hy => simp only [map_add, hx, hy, LinearMap.add_apply]

theorem b4cov_cplxMap_zero : b2_cplxMap (0 : Λ' →+ Λ) = 0 := by
  refine LinearMap.ext fun v ↦ ?_
  induction v using TensorProduct.inductionOn with
  | tmul c x => change c ⊗ₜ[ℤ] (0 : Λ) = 0; rw [TensorProduct.tmul_zero]
  | add x y hx hy => simp only [map_add, hx, hy, LinearMap.zero_apply, add_zero]

theorem b4cov_cplxMap_zsmul (n : ℤ) (f : Λ' →+ Λ) :
    b2_cplxMap (n • f) = (n : ℂ) • b2_cplxMap f := by
  refine LinearMap.ext fun v ↦ ?_
  induction v using TensorProduct.inductionOn with
  | tmul c x =>
    change c ⊗ₜ[ℤ] (n • f x) = (n : ℂ) • (c ⊗ₜ[ℤ] f x)
    rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', zsmul_eq_mul, smul_eq_mul,
      mul_comm]
  | add x y hx hy => simp only [map_add, hx, hy, LinearMap.smul_apply]

theorem b4cov_cplxMap_sum {ι : Type*} (s : Finset ι) (f : ι → Λ' →+ Λ) :
    b2_cplxMap (∑ i ∈ s, f i) = ∑ i ∈ s, b2_cplxMap (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [b4cov_cplxMap_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, b4cov_cplxMap_add, ih]

theorem b4cov_cplxMap_comp {Λ'' : Type*} [AddCommGroup Λ''] (f : Λ' →+ Λ) (g : Λ'' →+ Λ') :
    b2_cplxMap (f.comp g) = (b2_cplxMap f).comp (b2_cplxMap g) := by
  refine LinearMap.ext fun v ↦ ?_
  induction v using TensorProduct.inductionOn with
  | tmul c x => rfl
  | add x y hx hy => simp only [map_add, hx, hy, LinearMap.comp_apply]

end CplxMap

/-! ## `G`-maps along a stable decomposition -/

section HomG

variable {G : Type*} [Group G]
variable {V M : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup M] [Module ℂ M]

/-- The projection onto `F` along a complement `F'`, as an endomorphism of `M`. -/
abbrev b4cov_proj (F F' : Submodule ℂ M) (h : IsCompl F F') : M →ₗ[ℂ] M :=
  F.projection F' h

theorem b4cov_proj_mem (F F' : Submodule ℂ M) (h : IsCompl F F') (m : M) :
    b4cov_proj F F' h m ∈ F :=
  Submodule.projection_apply_mem h m

theorem b4cov_proj_add (F F' : Submodule ℂ M) (h : IsCompl F F') (m : M) :
    b4cov_proj F F' h m + b4cov_proj F' F h.symm m = m :=
  Submodule.projection_add_projection_eq_self h m

theorem b4cov_proj_eq_of_mem (F F' : Submodule ℂ M) (h : IsCompl F F') (m : M) (hm : m ∈ F) :
    b4cov_proj F F' h m = m :=
  Submodule.projection_apply_of_mem_left h hm

theorem b4cov_proj_eq_zero_of_mem (F F' : Submodule ℂ M) (h : IsCompl F F') (m : M)
    (hm : m ∈ F') : b4cov_proj F F' h m = 0 :=
  Submodule.projection_apply_right h ⟨m, hm⟩

/-- The projection along a stable decomposition commutes with a map preserving both pieces. -/
theorem b4cov_proj_comm (F F' : Submodule ℂ M) (h : IsCompl F F') (T : M →ₗ[ℂ] M)
    (hT : F ≤ F.comap T) (hT' : F' ≤ F'.comap T) (m : M) :
    b4cov_proj F F' h (T m) = T (b4cov_proj F F' h m) := by
  have hm := b4cov_proj_add F F' h m
  have h1 := b4cov_proj_mem F F' h m
  have h2 := b4cov_proj_mem F' F h.symm m
  conv_lhs => rw [← hm]
  rw [map_add, map_add, b4cov_proj_eq_of_mem F F' h _ (hT h1),
    b4cov_proj_eq_zero_of_mem F F' h _ (hT' h2), add_zero]

theorem b4cov_homG_sup (ρ : Representation ℂ G V) (act : G → M →ₗ[ℂ] M)
    (F F' : Submodule ℂ M) (h : IsCompl F F') (hF : ∀ g, F ≤ F.comap (act g))
    (hF' : ∀ g, F' ≤ F'.comap (act g)) :
    b4_HomG ρ act F ⊔ b4_HomG ρ act F' = b4_HomG ρ act ⊤ := by
  apply le_antisymm
  · exact sup_le (fun φ hφ ↦ ⟨fun _ ↦ trivial, hφ.2⟩) (fun φ hφ ↦ ⟨fun _ ↦ trivial, hφ.2⟩)
  · intro φ hφ
    refine Submodule.mem_sup.2 ⟨b4cov_proj F F' h ∘ₗ φ, ⟨fun v ↦ b4cov_proj_mem F F' h _,
      fun g v ↦ ?_⟩, b4cov_proj F' F h.symm ∘ₗ φ, ⟨fun v ↦ b4cov_proj_mem F' F h.symm _,
      fun g v ↦ ?_⟩, ?_⟩
    · simp only [LinearMap.comp_apply, hφ.2 g v]
      exact b4cov_proj_comm F F' h (act g) (hF g) (hF' g) _
    · simp only [LinearMap.comp_apply, hφ.2 g v]
      exact b4cov_proj_comm F' F h.symm (act g) (hF' g) (hF g) _
    · ext v
      simp only [LinearMap.add_apply, LinearMap.comp_apply]
      exact b4cov_proj_add F F' h (φ v)

theorem b4cov_homG_inf (ρ : Representation ℂ G V) (act : G → M →ₗ[ℂ] M)
    (F F' : Submodule ℂ M) (h : IsCompl F F') :
    b4_HomG ρ act F ⊓ b4_HomG ρ act F' = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun φ hφ ↦ ?_
  ext v
  have := Submodule.mem_inf.2 ⟨hφ.1.1 v, hφ.2.1 v⟩
  rw [h.inf_eq_bot] at this
  exact (Submodule.mem_bot ℂ).1 this

/-- **`G`-maps split along a stable decomposition** `M = F ⊕ F'`. -/
theorem b4cov_finrank_homG_split [FiniteDimensional ℂ V] [FiniteDimensional ℂ M]
    (ρ : Representation ℂ G V) (act : G → M →ₗ[ℂ] M)
    (F F' : Submodule ℂ M) (h : IsCompl F F') (hF : ∀ g, F ≤ F.comap (act g))
    (hF' : ∀ g, F' ≤ F'.comap (act g)) :
    Module.finrank ℂ (b4_HomG ρ act ⊤) =
      Module.finrank ℂ (b4_HomG ρ act F) + Module.finrank ℂ (b4_HomG ρ act F') := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (b4_HomG ρ act F) (b4_HomG ρ act F')
  rw [b4cov_homG_sup ρ act F F' h hF hF', b4cov_homG_inf ρ act F F' h, finrank_bot] at h1
  omega

end HomG

/-! ## Image filtrations of an endomorphism -/

section Image

variable {Λ : Type*} [AddCommGroup Λ]

/-- The complexified corestriction `ℂ ⊗ Λ → ℂ ⊗ f(Λ)`. -/
def b4cov_imageProj (f : Λ →+ Λ) : (ℂ ⊗[ℤ] Λ) →ₗ[ℂ] (ℂ ⊗[ℤ] f.range) :=
  b2_cplxMap f.rangeRestrict

theorem b4cov_imageProj_surjective (f : Λ →+ Λ) : Function.Surjective (b4cov_imageProj f) := by
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul c y =>
    obtain ⟨_, x, rfl⟩ := y
    exact ⟨c ⊗ₜ x, rfl⟩
  | add y z hy hz =>
    obtain ⟨y', rfl⟩ := hy
    obtain ⟨z', rfl⟩ := hz
    exact ⟨y' + z', map_add _ _ _⟩

theorem b4cov_subtype_comp_imageProj (f : Λ →+ Λ) :
    (b2_cplxMap f.range.subtype).comp (b4cov_imageProj f) = b2_cplxMap f := by
  rw [b4cov_imageProj, ← b4cov_cplxMap_comp]
  rfl

theorem b4cov_subtype_imageProj_apply (f : Λ →+ Λ) (y : ℂ ⊗[ℤ] Λ) :
    b2_cplxMap f.range.subtype (b4cov_imageProj f y) = b2_cplxMap f y :=
  LinearMap.congr_fun (b4cov_subtype_comp_imageProj f) y

theorem b4cov_cplxMap_subtype_injective (f : Λ →+ Λ) :
    Function.Injective (b2_cplxMap f.range.subtype) := by
  have := Module.Flat.lTensor_preserves_injective_linearMap (M := ℂ)
    f.range.subtype.toIntLinearMap Subtype.val_injective
  convert this using 1
  ext v
  induction v using TensorProduct.inductionOn with
  | tmul c x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem b4cov_imageF_eq_map (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (f : Λ →+ Λ) (hf : F ≤ F.comap (b2_cplxMap f)) :
    b2_imageF F f = F.map (b4cov_imageProj f) := by
  apply le_antisymm
  · intro z hz
    obtain ⟨y, rfl⟩ := b4cov_imageProj_surjective f z
    have hy : b2_cplxMap f y ∈ F := (b4cov_subtype_imageProj_apply f y) ▸ hz
    obtain ⟨y₁, h₁, y₂, h₂, rfl⟩ := b2f_mem_map_of_isWeightOne F hF f hf y hy
    have h₂' : b4cov_imageProj f y₂ = 0 := by
      apply b4cov_cplxMap_subtype_injective f
      exact (b4cov_subtype_imageProj_apply f y₂).trans (h₂.trans (map_zero _).symm)
    rw [map_add, h₂', add_zero]
    exact ⟨y₁, h₁, rfl⟩
  · rintro _ ⟨y, hy, rfl⟩
    show b2_cplxMap _ _ ∈ F
    exact (b4cov_subtype_imageProj_apply f y) ▸ hf hy

theorem b4cov_map_subtype_imageF (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (f : Λ →+ Λ) (hf : F ≤ F.comap (b2_cplxMap f)) :
    (b2_imageF F f).map (b2_cplxMap f.range.subtype) = F.map (b2_cplxMap f) := by
  rw [b4cov_imageF_eq_map F hF f hf, ← Submodule.map_comp, b4cov_subtype_comp_imageProj]

theorem b4cov_finrank_imageF (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (f : Λ →+ Λ) (hf : F ≤ F.comap (b2_cplxMap f)) :
    Module.finrank ℂ (b2_imageF F f) = Module.finrank ℂ (F.map (b2_cplxMap f)) := by
  rw [← b4cov_map_subtype_imageF F hF f hf]
  exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _
    (b4cov_cplxMap_subtype_injective f) _))

theorem b4cov_range_cplxMap (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (f : Λ →+ Λ) :
    LinearMap.range (b2_cplxMap f) = F.map (b2_cplxMap f) ⊔
      (b2_conjSubmodule Λ F).map (b2_cplxMap f) := by
  rw [← Submodule.map_sup, hF.sup_eq_top, Submodule.map_top]

theorem b4cov_finrank_imageQuot [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F) (f : Λ →+ Λ)
    (hf : F ≤ F.comap (b2_cplxMap f)) :
    Module.finrank ℂ ((ℂ ⊗[ℤ] f.range) ⧸ b2_imageF F f) =
      Module.finrank ℂ ((b2_conjSubmodule Λ F).map (b2_cplxMap f)) := by
  have : Module.Finite ℤ f.range :=
    Module.Finite.of_injective f.range.subtype.toIntLinearMap Subtype.val_injective
  have hq := Submodule.finrank_quotient_add_finrank (b2_imageF F f)
  rw [b4cov_finrank_imageF F hF f hf] at hq
  have hr : Module.finrank ℂ (ℂ ⊗[ℤ] f.range) =
      Module.finrank ℂ (LinearMap.range (b2_cplxMap f)) := by
    have : LinearMap.range (b2_cplxMap f) = LinearMap.range (b2_cplxMap f.range.subtype) := by
      rw [← b4cov_subtype_comp_imageProj, LinearMap.range_comp_of_range_eq_top _
        (LinearMap.range_eq_top.2 (b4cov_imageProj_surjective f))]
    rw [this]
    exact (LinearMap.finrank_range_of_inj (b4cov_cplxMap_subtype_injective f)).symm
  have hinf : F.map (b2_cplxMap f) ⊓ (b2_conjSubmodule Λ F).map (b2_cplxMap f) = ⊥ := by
    refine eq_bot_iff.2 fun z hz ↦ ?_
    obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hz
    have a1 : z ∈ F := by obtain ⟨y, hy, rfl⟩ := h1; exact hf hy
    have a2 : z ∈ b2_conjSubmodule Λ F := by
      obtain ⟨y, hy, rfl⟩ := h2; exact b2f_conjSubmodule_le_comap F f hf hy
    have := Submodule.mem_inf.2 ⟨a1, a2⟩
    rwa [hF.inf_eq_bot] at this
  have hs := Submodule.finrank_sup_add_finrank_inf_eq (F.map (b2_cplxMap f))
    ((b2_conjSubmodule Λ F).map (b2_cplxMap f))
  rw [← b4cov_range_cplxMap F hF f, hinf, finrank_bot, ← hr] at hs
  omega

end Image

end HodgeLean.Foundations.Program
