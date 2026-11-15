import HodgeLean.Foundations.Program.RelativeTorusKernelDefs
import HodgeLean.Foundations.LatticeTorus

/-!
# Track B2, lattice algebra of weight-one Hodge structures: helpers

Conjugation on `ℂ ⊗[ℤ] Λ` as a semilinear involution, the conjugate subspace as the image of a
subspace, flatness of `ℂ` over `ℤ` (so complexified injections stay injective), the
complexification of sums and compositions, and the base change of alternating forms. These are
the inputs of the fibrewise statements of `RelativeTorusKernel.lean`.
HC no distance; AV milestone no distance.
-/

noncomputable section

open scoped TensorProduct

namespace HodgeLean.Foundations.Program

section Conj

variable {Λ : Type*} [AddCommGroup Λ]

theorem b2a_conj_tmul (c : ℂ) (x : Λ) :
    b2_conj Λ (c ⊗ₜ[ℤ] x) = (starRingEnd ℂ c) ⊗ₜ[ℤ] x := rfl

theorem b2a_conj_smul (c : ℂ) (v : ℂ ⊗[ℤ] Λ) :
    b2_conj Λ (c • v) = starRingEnd ℂ c • b2_conj Λ v := by
  induction v using TensorProduct.inductionOn with
  | tmul a x =>
    show (starRingEnd ℂ (c • a)) ⊗ₜ[ℤ] x = starRingEnd ℂ c • ((starRingEnd ℂ a) ⊗ₜ[ℤ] x)
    rw [TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, map_mul]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

theorem b2a_conj_conj (v : ℂ ⊗[ℤ] Λ) : b2_conj Λ (b2_conj Λ v) = v := by
  induction v using TensorProduct.inductionOn with
  | tmul a x => rw [b2a_conj_tmul, b2a_conj_tmul, Complex.conj_conj]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem b2a_conj_incl (x : Λ) : b2_conj Λ ((1 : ℂ) ⊗ₜ[ℤ] x) = (1 : ℂ) ⊗ₜ[ℤ] x := by
  rw [b2a_conj_tmul, map_one]

/-- Conjugation as a conjugate-linear map.
Source: Birkenhake–Lange, §1.2 (the real structure of `Λ ⊗ ℂ`). -/
def b2a_conjₛₗ : (ℂ ⊗[ℤ] Λ) →ₛₗ[starRingEnd ℂ] (ℂ ⊗[ℤ] Λ) where
  toFun := b2_conj Λ
  map_add' := map_add _
  map_smul' := b2a_conj_smul

example (v : ℂ ⊗[ℤ] Λ) : b2a_conjₛₗ v = b2_conj Λ v := rfl

theorem b2a_conjSubmodule_eq_map (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) :
    b2_conjSubmodule Λ F = F.map (b2a_conjₛₗ (Λ := Λ)) := by
  change Submodule.span ℂ (b2a_conjₛₗ '' (F : Set (ℂ ⊗[ℤ] Λ))) = _
  rw [← Submodule.map_coe, Submodule.span_eq]

theorem b2a_mem_conjSubmodule {F : Submodule ℂ (ℂ ⊗[ℤ] Λ)} {v : ℂ ⊗[ℤ] Λ} :
    v ∈ b2_conjSubmodule Λ F ↔ ∃ a ∈ F, b2_conj Λ a = v := by
  rw [b2a_conjSubmodule_eq_map]
  rfl

theorem b2a_conj_mem_conjSubmodule {F : Submodule ℂ (ℂ ⊗[ℤ] Λ)} {a : ℂ ⊗[ℤ] Λ} (ha : a ∈ F) :
    b2_conj Λ a ∈ b2_conjSubmodule Λ F :=
  b2a_mem_conjSubmodule.2 ⟨a, ha, rfl⟩

theorem b2a_conj_mem_of_mem_conjSubmodule {F : Submodule ℂ (ℂ ⊗[ℤ] Λ)} {a : ℂ ⊗[ℤ] Λ}
    (ha : a ∈ b2_conjSubmodule Λ F) : b2_conj Λ a ∈ F := by
  obtain ⟨b, hb, rfl⟩ := b2a_mem_conjSubmodule.1 ha
  rwa [b2a_conj_conj]

theorem b2a_conjSubmodule_span_singleton (v : ℂ ⊗[ℤ] Λ) :
    b2_conjSubmodule Λ (ℂ ∙ v) = ℂ ∙ b2_conj Λ v := by
  rw [b2a_conjSubmodule_eq_map, Submodule.map_span, Set.image_singleton]
  rfl

/-- A real vector of a weight-one `F` is zero. -/
theorem b2a_eq_zero_of_mem_of_conj {F : Submodule ℂ (ℂ ⊗[ℤ] Λ)} (hF : b2_IsWeightOne Λ F)
    {v : ℂ ⊗[ℤ] Λ} (hv : v ∈ F) (hc : b2_conj Λ v = v) : v = 0 := by
  have h2 : v ∈ b2_conjSubmodule Λ F := hc ▸ b2a_conj_mem_conjSubmodule hv
  have := hF.inf_eq_bot ▸ (Submodule.mem_inf.2 ⟨hv, h2⟩)
  exact (Submodule.mem_bot ℂ).1 this

theorem b2a_incl_eq_zero_of_mem {F : Submodule ℂ (ℂ ⊗[ℤ] Λ)} (hF : b2_IsWeightOne Λ F)
    {x : Λ} (hx : (1 : ℂ) ⊗ₜ[ℤ] x ∈ F) : (1 : ℂ) ⊗ₜ[ℤ] x = 0 :=
  b2a_eq_zero_of_mem_of_conj hF hx (b2a_conj_incl x)

end Conj

section Cplx

variable {Λ Λ' Λ'' : Type*} [AddCommGroup Λ] [AddCommGroup Λ'] [AddCommGroup Λ'']

theorem b2a_cplxMap_tmul (g : Λ' →+ Λ) (c : ℂ) (x : Λ') :
    b2_cplxMap g (c ⊗ₜ[ℤ] x) = c ⊗ₜ[ℤ] g x := rfl

theorem b2a_conj_cplxMap (g : Λ' →+ Λ) (v : ℂ ⊗[ℤ] Λ') :
    b2_conj Λ (b2_cplxMap g v) = b2_cplxMap g (b2_conj Λ' v) := by
  induction v using TensorProduct.inductionOn with
  | tmul a x => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

theorem b2a_cplxMap_comp (g : Λ' →+ Λ) (h : Λ'' →+ Λ') :
    b2_cplxMap (g.comp h) = (b2_cplxMap g).comp (b2_cplxMap h) := by
  refine LinearMap.ext fun v ↦ ?_
  induction v using TensorProduct.inductionOn with
  | tmul c x => rfl
  | add x y hx hy => rw [map_add, hx, hy, map_add]

theorem b2a_cplxMap_comp_apply (g : Λ' →+ Λ) (h : Λ'' →+ Λ') (v : ℂ ⊗[ℤ] Λ'') :
    b2_cplxMap (g.comp h) v = b2_cplxMap g (b2_cplxMap h v) := by
  rw [b2a_cplxMap_comp]
  rfl

theorem b2a_cplxMap_sub (g h : Λ' →+ Λ) :
    b2_cplxMap (g - h) = b2_cplxMap g - b2_cplxMap h := by
  refine LinearMap.ext fun v ↦ ?_
  induction v using TensorProduct.inductionOn with
  | tmul c x =>
    simp only [LinearMap.sub_apply, b2a_cplxMap_tmul, AddMonoidHom.sub_apply,
      TensorProduct.tmul_sub]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem b2a_cplxMap_id_sub_apply (e : Λ →+ Λ) (v : ℂ ⊗[ℤ] Λ) :
    b2_cplxMap (AddMonoidHom.id Λ - e) v = v - b2_cplxMap e v := by
  rw [b2a_cplxMap_sub, b2_cplxMap_id]
  rfl

/-- `ℂ` is flat over `ℤ` (torsion-free over a Dedekind domain). -/
instance b2a_flat : Module.Flat ℤ ℂ := inferInstance

theorem b2a_cplxMap_injective (g : Λ' →+ Λ) (hg : Function.Injective g) :
    Function.Injective (b2_cplxMap g) := by
  have := Module.Flat.lTensor_preserves_injective_linearMap (M := ℂ) g.toIntLinearMap hg
  rwa [b2_cplxMap, LinearMap.baseChange_eq_lTensor]

theorem b2a_cplxMap_surjective (g : Λ' →+ Λ) (hg : Function.Surjective g) :
    Function.Surjective (b2_cplxMap g) := by
  have := LinearMap.lTensor_surjective ℂ (g := g.toIntLinearMap) hg
  rwa [b2_cplxMap, LinearMap.baseChange_eq_lTensor]

/-- The complexified inclusion of a subgroup is injective. -/
theorem b2a_cplxMap_subtype_injective (S : AddSubgroup Λ) :
    Function.Injective (b2_cplxMap S.subtype) :=
  b2a_cplxMap_injective _ Subtype.val_injective

/-- `f_ℂ` factors as the complexified inclusion of `f(Λ)` after `(f, onto its range)_ℂ`. -/
theorem b2a_cplxMap_rangeRestrict (f : Λ' →+ Λ) (v : ℂ ⊗[ℤ] Λ') :
    b2_cplxMap f.range.subtype (b2_cplxMap f.rangeRestrict v) = b2_cplxMap f v := by
  rw [← b2a_cplxMap_comp_apply]
  rfl

theorem b2a_cplxMap_rangeRestrict_surjective (f : Λ' →+ Λ) :
    Function.Surjective (b2_cplxMap f.rangeRestrict) :=
  b2a_cplxMap_surjective _ f.rangeRestrict_surjective

end Cplx

section Forms

variable {Λ Λ' : Type*} [AddCommGroup Λ] [AddCommGroup Λ']

theorem b2a_baseChange_skew (Q : LinearMap.BilinForm ℤ Λ) (hQ : ∀ x, Q x x = 0)
    (u v : ℂ ⊗[ℤ] Λ) : Q.baseChange ℂ u v = -Q.baseChange ℂ v u := by
  have hs : ∀ x y, Q x y = -Q y x := fun x y ↦ by
    have := hQ (x + y)
    simp only [map_add, LinearMap.add_apply, hQ, zero_add, add_zero] at this
    exact eq_neg_of_add_eq_zero_left ((add_comm _ _).trans this)
  induction u using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, LinearMap.add_apply, hx, hy, map_add, neg_add]
  | tmul a x =>
    induction v using TensorProduct.inductionOn with
    | add y z hy hz => rw [map_add, map_add, LinearMap.add_apply, hy, hz, neg_add]
    | tmul b y =>
      rw [LinearMap.BilinForm.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul, hs,
        neg_smul, mul_comm]

theorem b2a_baseChange_alt (Q : LinearMap.BilinForm ℤ Λ) (hQ : ∀ x, Q x x = 0)
    (u : ℂ ⊗[ℤ] Λ) : Q.baseChange ℂ u u = 0 := by
  have := b2a_baseChange_skew Q hQ u u
  have h2 : (2 : ℂ) * Q.baseChange ℂ u u = 0 := by rw [two_mul]; nth_rw 1 [this]; ring
  simpa using h2

theorem b2a_baseChange_incl_left (Q : LinearMap.BilinForm ℤ Λ) (x : Λ) (hx : ∀ y, Q x y = 0)
    (w : ℂ ⊗[ℤ] Λ) : Q.baseChange ℂ ((1 : ℂ) ⊗ₜ[ℤ] x) w = 0 := by
  induction w using TensorProduct.inductionOn with
  | tmul a y => rw [LinearMap.BilinForm.baseChange_tmul, hx, zero_smul]
  | add y z hy hz => rw [map_add, hy, hz, add_zero]

theorem b2a_baseChange_compl (Q : LinearMap.BilinForm ℤ Λ) (g : Λ' →+ Λ)
    (u v : ℂ ⊗[ℤ] Λ') :
    LinearMap.BilinForm.baseChange ℂ (Q.compl₁₂ g.toIntLinearMap g.toIntLinearMap) u v =
      Q.baseChange ℂ (b2_cplxMap g u) (b2_cplxMap g v) := by
  induction u using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, LinearMap.add_apply, hx, hy, map_add, map_add,
      LinearMap.add_apply]
  | tmul a x =>
    induction v using TensorProduct.inductionOn with
    | add y z hy hz => rw [map_add, map_add, hy, hz, map_add]
    | tmul b y => rfl

end Forms

section Free

variable {Λ : Type*} [AddCommGroup Λ]

/-- On a free lattice `x ↦ 1 ⊗ x` is injective. -/
theorem b2a_incl_injective [Module.Free ℤ Λ] :
    Function.Injective (fun x : Λ ↦ (1 : ℂ) ⊗ₜ[ℤ] x) := by
  let b := Module.Free.chooseBasis ℤ Λ
  intro x y hxy
  refine b.repr.injective (Finsupp.ext fun i ↦ ?_)
  have := congrArg (fun v ↦ (b.baseChange ℂ).repr v i) hxy
  simp only [Module.Basis.baseChange_repr_tmul, zsmul_eq_mul, mul_one] at this
  exact_mod_cast this

end Free

section Idempotent

variable {Λ : Type*} [AddCommGroup Λ]

/-- A point `[[v]]` of the torus is zero iff `v` is a lattice vector modulo `F`. -/
theorem b2a_torus_mk_eq_zero_iff (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (v : ℂ ⊗[ℤ] Λ) :
    (QuotientAddGroup.mk (Submodule.Quotient.mk v) : b2_torus Λ F) = 0 ↔
      ∃ x : Λ, v - (1 : ℂ) ⊗ₜ[ℤ] x ∈ F := by
  rw [QuotientAddGroup.eq_zero_iff]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rw [← Submodule.Quotient.eq]
    exact hx.symm
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    exact ((Submodule.Quotient.eq _).2 hx).symm

theorem b2a_cplxMap_idem_subtype (e : Λ →+ Λ) (he : e.comp e = e) (w : ℂ ⊗[ℤ] e.range) :
    b2_cplxMap e (b2_cplxMap e.range.subtype w) = b2_cplxMap e.range.subtype w := by
  rw [← b2a_cplxMap_comp_apply]
  congr 2
  ext ⟨_, y, rfl⟩
  exact DFunLike.congr_fun he y

theorem b2a_idem_one_sub (e : Λ →+ Λ) (he : e.comp e = e) :
    (AddMonoidHom.id Λ - e).comp (AddMonoidHom.id Λ - e) = AddMonoidHom.id Λ - e := by
  ext x
  have := DFunLike.congr_fun he x
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.sub_apply,
    AddMonoidHom.id_apply, map_sub] at this ⊢
  rw [this, sub_self, sub_zero]

theorem b2a_cplxMap_idem_one_sub_subtype (e : Λ →+ Λ) (he : e.comp e = e)
    (w : ℂ ⊗[ℤ] (AddMonoidHom.id Λ - e).range) :
    b2_cplxMap e (b2_cplxMap (AddMonoidHom.id Λ - e).range.subtype w) = 0 := by
  rw [← b2a_cplxMap_comp_apply]
  have : e.comp (AddMonoidHom.id Λ - e).range.subtype = 0 := by
    ext ⟨_, y, rfl⟩
    have := DFunLike.congr_fun he y
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddSubgroup.coe_subtype,
      AddMonoidHom.sub_apply, AddMonoidHom.id_apply, map_sub, AddMonoidHom.zero_apply] at this ⊢
    rw [this, sub_self]
  rw [this]
  induction w using TensorProduct.inductionOn with
  | tmul c x => simp [b2a_cplxMap_tmul]
  | add x y hx hy => rw [map_add, hx, hy, add_zero]

/-- The kernel step for an idempotent: if `ι w ≡ 1 ⊗ e λ` mod `F`, then `[w] = 0`. -/
theorem b2a_subTorus_mk_eq_zero (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (e : Λ →+ Λ)
    (w : ℂ ⊗[ℤ] e.range) (x : Λ)
    (h : b2_cplxMap e.range.subtype w - (1 : ℂ) ⊗ₜ[ℤ] e x ∈ F) :
    (QuotientAddGroup.mk (Submodule.Quotient.mk w) : b2_torus e.range (b2_imageF F e)) = 0 := by
  rw [b2a_torus_mk_eq_zero_iff]
  refine ⟨⟨e x, x, rfl⟩, ?_⟩
  change b2_cplxMap e.range.subtype _ ∈ F
  rw [map_sub]
  exact h

end Idempotent

section Dimension

variable {Λ : Type*} [AddCommGroup Λ]

theorem b2a_conjSubmodule_conjSubmodule (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) :
    b2_conjSubmodule Λ (b2_conjSubmodule Λ F) = F := by
  ext v
  constructor
  · intro hv
    obtain ⟨a, ha, rfl⟩ := b2a_mem_conjSubmodule.1 hv
    exact b2a_conj_mem_of_mem_conjSubmodule ha
  · intro hv
    rw [← b2a_conj_conj v]
    exact b2a_conj_mem_conjSubmodule (b2a_conj_mem_conjSubmodule hv)

theorem b2a_finrank_conjSubmodule_le (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) [Module.Finite ℂ F] :
    Module.finrank ℂ (b2_conjSubmodule Λ F) ≤ Module.finrank ℂ F := by
  let v := Module.finBasis ℂ F
  have hF : Submodule.span ℂ (Set.range fun i ↦ (v i : ℂ ⊗[ℤ] Λ)) = F := by
    rw [Set.range_comp' Subtype.val v]
    change Submodule.span ℂ (F.subtype '' _) = F
    rw [Submodule.span_image, v.span_eq, Submodule.map_top, Submodule.range_subtype]
  calc Module.finrank ℂ (b2_conjSubmodule Λ F)
      = Module.finrank ℂ (Submodule.map (b2a_conjₛₗ (Λ := Λ))
          (Submodule.span ℂ (Set.range fun i ↦ (v i : ℂ ⊗[ℤ] Λ)))) := by
        rw [hF, b2a_conjSubmodule_eq_map]
    _ ≤ Module.finrank ℂ F := by
        rw [Submodule.map_span, ← Set.range_comp]
        exact (finrank_range_le_card _).trans (by simp)

theorem b2a_finrank_conjSubmodule [Module.Finite ℤ Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) :
    Module.finrank ℂ (b2_conjSubmodule Λ F) = Module.finrank ℂ F := by
  refine le_antisymm (b2a_finrank_conjSubmodule_le F) ?_
  have := b2a_finrank_conjSubmodule_le (b2_conjSubmodule Λ F)
  rwa [b2a_conjSubmodule_conjSubmodule] at this

end Dimension

section Standard

/-- Coordinates on `ℂ ⊗ ℤ²`, `c ⊗ x ↦ (x₀ c, x₁ c)`.
Source: Mathlib `TensorProduct.piScalarRight`. -/
def b2a_pi : (ℂ ⊗[ℤ] (Fin 2 → ℤ)) ≃ₗ[ℂ] (Fin 2 → ℂ) :=
  TensorProduct.piScalarRight ℤ ℂ ℂ (Fin 2)

example : b2a_pi 0 = 0 := map_zero _

theorem b2a_pi_tmul (c : ℂ) (x : Fin 2 → ℤ) (i : Fin 2) :
    b2a_pi (c ⊗ₜ[ℤ] x) i = (x i : ℂ) * c := by
  simp [b2a_pi, zsmul_eq_mul]

theorem b2a_stdVec_pi :
    b2a_pi ((1 : ℂ) ⊗ₜ[ℤ] (Pi.single 0 1 : Fin 2 → ℤ) + Complex.I ⊗ₜ[ℤ] (Pi.single 1 1 : Fin 2 → ℤ))
      = ![1, Complex.I] := by
  ext i; fin_cases i <;> simp [map_add, b2a_pi_tmul]


/-- The generator `e₀ + i e₁` of `b2_stdF`.
Source: Birkenhake–Lange, §1.1. -/
abbrev b2a_stdVec : ℂ ⊗[ℤ] (Fin 2 → ℤ) :=
  (1 : ℂ) ⊗ₜ[ℤ] (Pi.single 0 1 : Fin 2 → ℤ) + Complex.I ⊗ₜ[ℤ] (Pi.single 1 1 : Fin 2 → ℤ)

example : b2a_stdVec ∈ b2_stdF := Submodule.mem_span_singleton_self _

theorem b2a_stdVec_conj : b2_conj _ b2a_stdVec =
    (1 : ℂ) ⊗ₜ[ℤ] (Pi.single 0 1 : Fin 2 → ℤ) + (-Complex.I) ⊗ₜ[ℤ] (Pi.single 1 1 : Fin 2 → ℤ) := by
  rw [map_add, b2a_conj_tmul, b2a_conj_tmul, map_one, Complex.conj_I]

theorem b2a_stdVec_conj_pi : b2a_pi (b2_conj _ b2a_stdVec) = ![1, -Complex.I] := by
  rw [b2a_stdVec_conj]
  ext i; fin_cases i <;> simp [map_add, b2a_pi_tmul]

theorem b2a_stdForm_apply (x y : Fin 2 → ℤ) : b2_stdForm x y = x 0 * y 1 - x 1 * y 0 := by
  simp [b2_stdForm, Matrix.toLinearMap₂'_apply', dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  ring

theorem b2a_skewIdem_apply (x : Fin 2 → ℤ) : b2_skewIdem x = ![x 0 + x 1, 0] := by
  ext i
  fin_cases i <;> simp [b2_skewIdem, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

section Const

open CategoryTheory

theorem b2a_const_transport {B : Type*} [TopologicalSpace B] (W : Type) [AddCommGroup W]
    [Module.Free ℤ W] [Module.Finite ℤ W] {b b' : B} (γ : Path.Homotopic.Quotient b b')
    (x : (b2_constLocalSystem B W).fiber b) : (b2_constLocalSystem B W).transport γ x = x := rfl

theorem b2a_const_flatTransport {B : Type*} [TopologicalSpace B] (W : Type) [AddCommGroup W]
    [Module.Free ℤ W] [Module.Finite ℤ W] (U : Set B) (hU : IsSimplyConnected U) (b b₀ : U)
    (v : (b2_constLocalSystem B W).cFiber b) :
    (b2_constLocalSystem B W).flatTransport U hU b b₀ v = v := by
  induction v using TensorProduct.inductionOn with
  | tmul c x => rfl
  | add x y hx hy => rw [map_add, hx, hy]; rfl

end Const

/-- The functional `z ↦ z₀ + √2 z₁` on `ℂ ⊗ ℤ²`, vanishing on `b2_irrF`.
Source: elementary; Birkenhake–Lange, §1.1 (a lattice must be discrete). -/
def b2a_irrFun : (ℂ ⊗[ℤ] (Fin 2 → ℤ)) →ₗ[ℂ] ℂ where
  toFun w := b2a_pi w 0 + ((Real.sqrt 2 : ℝ) : ℂ) * b2a_pi w 1
  map_add' v w := by simp only [map_add, Pi.add_apply]; ring
  map_smul' c v := by simp only [map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

example : b2a_irrFun 0 = 0 := map_zero _

theorem b2a_irrF_le_ker : b2_irrF ≤ LinearMap.ker b2a_irrFun := by
  rw [b2_irrF, Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker]
  simp [b2a_irrFun, b2a_pi_tmul]

/-- The induced functional on `(ℂ ⊗ ℤ²) ⧸ b2_irrF`.
Source: Mathlib `Submodule.liftQ`. -/
def b2a_irrBar : ((ℂ ⊗[ℤ] (Fin 2 → ℤ)) ⧸ b2_irrF) →ₗ[ℂ] ℂ :=
  b2_irrF.liftQ b2a_irrFun b2a_irrF_le_ker

example : b2a_irrBar 0 = 0 := map_zero _

theorem b2a_irrBar_lattice (x : Fin 2 → ℤ) :
    b2a_irrBar (b2_latticeMap _ b2_irrF x) = ((x 0 + Real.sqrt 2 * x 1 : ℝ) : ℂ) := by
  change b2a_irrFun ((1 : ℂ) ⊗ₜ[ℤ] x) = _
  simp [b2a_irrFun, b2a_pi_tmul]

theorem b2a_irr_lattice (x : Fin 2 → ℤ) :
    b2_latticeMap _ b2_irrF x = ((x 0 + Real.sqrt 2 * x 1 : ℝ) : ℂ) •
      b2_latticeMap _ b2_irrF (Pi.single 0 1) := by
  change Submodule.Quotient.mk _ = _ • Submodule.Quotient.mk _
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, b2_irrF]
  have : (1 : ℂ) ⊗ₜ[ℤ] x - ((x 0 + Real.sqrt 2 * x 1 : ℝ) : ℂ) •
      (1 : ℂ) ⊗ₜ[ℤ] (Pi.single 0 1 : Fin 2 → ℤ) =
      (-(x 1 : ℂ)) • (((Real.sqrt 2 : ℝ) : ℂ) ⊗ₜ[ℤ] (Pi.single 0 1 : Fin 2 → ℤ) -
        (1 : ℂ) ⊗ₜ[ℤ] (Pi.single 1 1 : Fin 2 → ℤ)) := by
    apply b2a_pi.injective
    ext i; fin_cases i <;> (simp [b2a_pi_tmul]; try ring)
  change (1 : ℂ) ⊗ₜ[ℤ] x - _ • (1 : ℂ) ⊗ₜ[ℤ] (Pi.single 0 1 : Fin 2 → ℤ) ∈ _
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

end Standard

end HodgeLean.Foundations.Program
