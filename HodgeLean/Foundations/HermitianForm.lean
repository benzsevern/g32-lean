import Mathlib.Algebra.QuadraticAlgebra.Discriminant
import Mathlib.Algebra.QuadraticAlgebra.NormDeterminant
import Mathlib.LinearAlgebra.SesquilinearForm.Star
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.RingTheory.Norm.Defs
import Mathlib.Tactic.LinearCombination
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.LinearAlgebra.QuadraticForm.TensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.Basic.Real.Basic

/-! # Hermitian forms over an imaginary quadratic field and their determinant class

Foundations target T3 (`docs/roadmap/foundations.md` §4 T3, §6 Rank 1).

## Setting

`K = QuadraticAlgebra ℚ a b`, that is `ℚ(ω)` with `ω² = a + b ω`. It is a field under the no-root
condition `Fact (∀ r : ℚ, r ^ 2 ≠ a + b * r)`, which Mathlib derives both from
`Fact (¬ IsSquare (discr a b))` and, for `b = 0`, from `Fact (¬ IsSquare a)`. The involution is
Mathlib's `star` on `QuadraticAlgebra`, `x + y ω ↦ (x + b y) - y ω` (the nontrivial automorphism),
and its fixed field is `ℚ` (`QuadraticAlgebraAux.star_eq_self_iff`).

The imaginary quadratic case is `discr a b < 0`, and the docstrings are restricted to it. For a
general CM field the relevant norm goes to the totally real subfield, not to `ℚ`, and nothing here
covers that.

## Main definitions

* `HermitianForm.normSubgroup K`: the image of `Kˣ` in `ℚˣ` under the field norm `Algebra.norm ℚ`.
* `HermitianForm.gramDet h e`: the determinant of the Gram matrix of a sesquilinear form `h` in a
  basis `e`; `HermitianForm.gramDetℚ h e` is its rational value.
* `HermitianForm.detClass h`: the class of the Gram determinant in `ℚˣ ⧸ normSubgroup K`, for a
  nondegenerate Hermitian `h` on a finite-dimensional `K`-space (basis-independent by
  `HermitianForm.detClass_eq`).
* `HermitianForm.diagForm d`: the diagonal Hermitian form `⟨d₁, …, dₙ⟩` on `Kⁿ`.
* `HermitianForm.hermSignature h`: half the real signature of the rational quadratic form
  `x ↦ h x x` (`HermitianForm.hermQuadForm h`) base-changed to `ℝ`.

## Main results

* `HermitianForm.gramDetℚ_basis_change`: `gramDetℚ h e' = Nm(det P) * gramDetℚ h e`.
* `HermitianForm.detClass_neg`: `detClass (-h) = [-1] ^ dim * detClass h`.
* For `K = ℚ(√-3) = QuadraticAlgebra ℚ (-3) 0`: `detClass ⟨1, 1, 1, -1, -1, -2⟩ = [-2]`
  (`detClass_diag_F1569`), `[-2/81] = [-2] = [-24]` (`classes_F1569`, `Checks: F-1569`),
  `[-2] ≠ [1]` and `[2] ≠ [1]`; `⟨1, 1, 1, -1, -1, -2⟩` has signature `(3, 3)`
  (`hermSignature_diag_F1569`).
* `HermitianForm.hermSignature_diagForm`: over `ℚ(√a)`, `a < 0`, the signature of `⟨d⟩` is
  `(#{i | 0 < d i}, #{i | d i < 0})`.

## Conventions

* Sesquilinear forms are Mathlib's `W →ₗ⋆[K] W →ₗ[K] K`: conjugate-linear in the **first**
  argument. With `P = e.toMatrix e'` the Gram matrix changes as `G ↦ Pᴴ G P`
  (`HermitianForm.toMatrix₂_basis_change`).
* `detClass` is the class of the Gram **determinant**, with no sign factor. Convention:
  determinant, matching F-1569 (1). Some sources call `(-1) ^ (n (n - 1) / 2) · det` the
  discriminant; in dimension 6 that factor is `-1` and would turn `[-2]` into `[2]`.
-/

open Module Matrix

namespace HodgeLean.Foundations

namespace QuadraticAlgebraAux

open QuadraticAlgebra

/-- The field norm `Algebra.norm R` of `QuadraticAlgebra R a b` is `QuadraticAlgebra.norm`,
`x² + b x y - a y²` at `x + y ω`. -/
theorem algebraNorm_eq_norm {R : Type*} [CommRing R] {a b : R} (z : QuadraticAlgebra R a b) :
    Algebra.norm R z = QuadraticAlgebra.norm z := by
  rw [Algebra.norm_apply, ← det_toLinearMap_eq_norm]
  rfl

variable {a b : ℚ}

/-- The fixed field of `star` on `QuadraticAlgebra ℚ a b` is `ℚ`. -/
theorem star_eq_self_iff {z : QuadraticAlgebra ℚ a b} :
    star z = z ↔ z = algebraMap ℚ _ z.re := by
  constructor
  · intro hz
    have him : z.im = 0 := by
      have := congrArg QuadraticAlgebra.im hz
      simp only [im_star] at this
      linarith
    ext <;> simp [him]
  · intro hz
    rw [hz]
    ext <;> simp

/-- In the imaginary quadratic case `discr a b < 0`, the norm of a nonzero element is positive. -/
theorem norm_pos (hd : discr a b < 0) {z : QuadraticAlgebra ℚ a b} (hz : z ≠ 0) :
    0 < QuadraticAlgebra.norm z := by
  have h4 : 4 * QuadraticAlgebra.norm z = (2 * z.re + b * z.im) ^ 2 - discr a b * z.im ^ 2 := by
    rw [norm_def, discr_def]; ring
  by_cases him : z.im = 0
  · have hre : z.re ≠ 0 := fun hre ↦ hz (QuadraticAlgebra.ext hre him)
    have : 0 < z.re ^ 2 := by positivity
    rw [norm_def, him]
    nlinarith
  · have : 0 < z.im ^ 2 := by positivity
    nlinarith [sq_nonneg (2 * z.re + b * z.im)]

end QuadraticAlgebraAux

namespace HermitianForm

open QuadraticAlgebra QuadraticAlgebraAux

section NormSubgroup

/-- The norm subgroup `Nm(Kˣ) ≤ ℚˣ`: the image of `Kˣ` under the field norm `Algebra.norm ℚ`.
For `K` imaginary quadratic its elements are positive (`pos_of_mem_normSubgroup`).

Source: the group of norms `N(k_b^×)` of a quadratic extension `k_b = k(√b)`, as in Serre,
*A Course in Arithmetic*, Ch. III, §1.1, Proposition 1. -/
noncomputable def normSubgroup (K : Type*) [Field K] [Algebra ℚ K] : Subgroup ℚˣ :=
  (Units.map (Algebra.norm ℚ : K →* ℚ)).range

variable {a b : ℚ} [Fact (∀ r : ℚ, r ^ 2 ≠ a + b * r)]

/-- A rational number lies in `Nm(Kˣ)` iff it is the norm `x² + b x y - a y²` of some `x + y ω`. -/
theorem mem_normSubgroup_iff {q : ℚˣ} :
    q ∈ normSubgroup (QuadraticAlgebra ℚ a b) ↔
      ∃ z : QuadraticAlgebra ℚ a b, QuadraticAlgebra.norm z = q := by
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨u, by simp [algebraNorm_eq_norm]⟩
  · rintro ⟨z, hz⟩
    have hz0 : z ≠ 0 := by
      rintro rfl
      exact q.ne_zero (by simpa using hz.symm)
    exact ⟨Units.mk0 z hz0, Units.ext (by simp [algebraNorm_eq_norm, hz])⟩

/-- Every nonzero rational square is a norm: `Nm(q) = q²` for `q ∈ ℚ`. -/
theorem sq_mem_normSubgroup (q : ℚˣ) : q ^ 2 ∈ normSubgroup (QuadraticAlgebra ℚ a b) :=
  mem_normSubgroup_iff.2 ⟨algebraMap ℚ _ q, by rw [norm_algebraMap]; push_cast; rfl⟩

/-- In the imaginary quadratic case `discr a b < 0`, every element of `Nm(Kˣ)` is positive. -/
theorem pos_of_mem_normSubgroup (hd : discr a b < 0) {q : ℚˣ}
    (hq : q ∈ normSubgroup (QuadraticAlgebra ℚ a b)) : 0 < (q : ℚ) := by
  obtain ⟨z, hz⟩ := mem_normSubgroup_iff.1 hq
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact q.ne_zero (by simpa using hz.symm)
  exact hz ▸ norm_pos hd hz0

/-- Two rationals whose ratio is a norm have the same class in `ℚˣ ⧸ Nm(Kˣ)`. -/
theorem mk_eq_mk_of_eq_mul {x y n : ℚˣ} (hn : n ∈ normSubgroup (QuadraticAlgebra ℚ a b))
    (h : (x : ℚ) = n * y) :
    (x : ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ a b)) = y := by
  rw [show x = n * y from Units.ext (by simpa using h), QuotientGroup.mk_mul,
    (QuotientGroup.eq_one_iff _).2 hn, one_mul]

end NormSubgroup

section Gram

variable {a b : ℚ} {W : Type*} [AddCommGroup W] [Module (QuadraticAlgebra ℚ a b) W]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Gram determinant `det (h (e i) (e j))` of a sesquilinear form `h` in a basis `e`.

Source: the determinant of the Gram matrix `(h(eᵢ, eⱼ))`, Mathlib's `LinearMap.toMatrix₂`. -/
noncomputable def gramDet (h : W →ₗ⋆[QuadraticAlgebra ℚ a b] W →ₗ[QuadraticAlgebra ℚ a b]
    QuadraticAlgebra ℚ a b) (e : Basis ι (QuadraticAlgebra ℚ a b) W) : QuadraticAlgebra ℚ a b :=
  (LinearMap.toMatrix₂ e e h).det

/-- The rational value of the Gram determinant: the `ℚ`-coordinate `re` of `gramDet h e`. For a
Hermitian `h` the Gram determinant lies in `ℚ` (`algebraMap_gramDetℚ`), so nothing is lost.

Source: as for `gramDet`. -/
noncomputable def gramDetℚ (h : W →ₗ⋆[QuadraticAlgebra ℚ a b] W →ₗ[QuadraticAlgebra ℚ a b]
    QuadraticAlgebra ℚ a b) (e : Basis ι (QuadraticAlgebra ℚ a b) W) : ℚ :=
  (gramDet h e).re

variable {h : W →ₗ⋆[QuadraticAlgebra ℚ a b] W →ₗ[QuadraticAlgebra ℚ a b] QuadraticAlgebra ℚ a b}

/-- The Gram determinant of a Hermitian form is fixed by `star`. -/
theorem star_gramDet (hh : h.IsSymm) (e : Basis ι (QuadraticAlgebra ℚ a b) W) :
    star (gramDet h e) = gramDet h e := by
  rw [gramDet, ← det_conjTranspose, ((h.isSymm_iff_isHermitian_toMatrix e).1 hh).eq]

/-- The Gram determinant of a Hermitian form is rational: it is the image of `gramDetℚ h e`. -/
theorem algebraMap_gramDetℚ (hh : h.IsSymm) (e : Basis ι (QuadraticAlgebra ℚ a b) W) :
    algebraMap ℚ _ (gramDetℚ h e) = gramDet h e :=
  (star_eq_self_iff.1 (star_gramDet hh e)).symm

/-- Change of basis for the Gram matrix of a sesquilinear form (conjugate-linear in the first
argument): with `P = e.toMatrix e'` (column `j` of `P` is `e'ⱼ` in the basis `e`), the Gram matrix
in `e'` is `Pᴴ G P`, where `G` is the Gram matrix in `e`. -/
theorem toMatrix₂_basis_change (h : W →ₗ⋆[QuadraticAlgebra ℚ a b] W →ₗ[QuadraticAlgebra ℚ a b]
    QuadraticAlgebra ℚ a b) (e e' : Basis ι (QuadraticAlgebra ℚ a b) W) :
    LinearMap.toMatrix₂ e' e' h =
      (e.toMatrix e')ᴴ * LinearMap.toMatrix₂ e e h * e.toMatrix e' := by
  refine Matrix.ext fun i j ↦ ?_
  rw [LinearMap.toMatrix₂_apply]
  conv_lhs => rw [← e.sum_repr (e' i), ← e.sum_repr (e' j)]
  simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply,
    map_smul, smul_eq_mul, Matrix.mul_apply, conjTranspose_apply, Basis.toMatrix_apply,
    LinearMap.toMatrix₂_apply, Finset.sum_mul, Finset.mul_sum, starRingEnd_apply]
  exact Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦ by ring

/-- Change of basis for the Gram determinant: `gramDet h e' = star (det P) * det P * gramDet h e`,
where `det P = e.det e'`. -/
theorem gramDet_basis_change (h : W →ₗ⋆[QuadraticAlgebra ℚ a b] W →ₗ[QuadraticAlgebra ℚ a b]
    QuadraticAlgebra ℚ a b) (e e' : Basis ι (QuadraticAlgebra ℚ a b) W) :
    gramDet h e' = star (e.det e') * e.det e' * gramDet h e := by
  rw [gramDet, gramDet, toMatrix₂_basis_change h e e', det_mul, det_mul, det_conjTranspose,
    Basis.det_apply]
  ring

/-- Change of basis for the rational Gram determinant of a Hermitian form:
`gramDetℚ h e' = Nm(det P) * gramDetℚ h e`, where `P = e.toMatrix e'`, `det P = e.det e'` and
`Nm = Algebra.norm ℚ` is the field norm. -/
theorem gramDetℚ_basis_change (hh : h.IsSymm) (e e' : Basis ι (QuadraticAlgebra ℚ a b) W) :
    gramDetℚ h e' = Algebra.norm ℚ (e.det e') * gramDetℚ h e := by
  apply QuadraticAlgebra.algebraMap_injective (a := a) (b := b)
  rw [map_mul, algebraMap_gramDetℚ hh, algebraMap_gramDetℚ hh, gramDet_basis_change,
    algebraNorm_eq_norm, algebraMap_norm_eq_mul_star]
  ring

/-- The Gram determinant does not change when the basis is reindexed. -/
theorem gramDet_reindex {ι' : Type*} [Fintype ι'] [DecidableEq ι']
    (e : Basis ι (QuadraticAlgebra ℚ a b) W) (σ : ι ≃ ι') :
    gramDet h (e.reindex σ) = gramDet h e := by
  have : LinearMap.toMatrix₂ (e.reindex σ) (e.reindex σ) h =
      (LinearMap.toMatrix₂ e e h).submatrix σ.symm σ.symm :=
    Matrix.ext fun i j ↦ by simp
  rw [gramDet, gramDet, this, det_submatrix_equiv_self]

/-- The negative of a Hermitian form is Hermitian. -/
theorem isSymm_neg (hh : h.IsSymm) : (-h).IsSymm :=
  LinearMap.isSymm_def.2 fun x y ↦ by simp [LinearMap.isSymm_def.1 hh x y]

/-- The negative of a nondegenerate form is nondegenerate. -/
theorem nondegenerate_neg (hn : h.Nondegenerate) : (-h).Nondegenerate :=
  ⟨fun x hx ↦ hn.1 x fun y ↦ by simpa using hx y, fun y hy ↦ hn.2 y fun x ↦ by simpa using hy x⟩

/-- The rational Gram determinant of `-h` is `(-1) ^ n` times that of `h`, for `n` the size of
the basis. -/
theorem gramDetℚ_neg (e : Basis ι (QuadraticAlgebra ℚ a b) W) :
    gramDetℚ (-h) e = (-1) ^ Fintype.card ι * gramDetℚ h e := by
  rw [gramDetℚ, gramDetℚ, gramDet, gramDet, map_neg (LinearMap.toMatrix₂ e e) h, det_neg,
    show ((-1 : QuadraticAlgebra ℚ a b) ^ Fintype.card ι) =
      algebraMap ℚ _ ((-1) ^ Fintype.card ι) by simp,
    ← Algebra.smul_def, re_smul, smul_eq_mul]

end Gram

section Class

variable {a b : ℚ} [Fact (∀ r : ℚ, r ^ 2 ≠ a + b * r)]
  {W : Type*} [AddCommGroup W] [Module (QuadraticAlgebra ℚ a b) W]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  {h : W →ₗ⋆[QuadraticAlgebra ℚ a b] W →ₗ[QuadraticAlgebra ℚ a b] QuadraticAlgebra ℚ a b}

/-- A Hermitian form is nondegenerate iff its Gram determinant in some (any) basis is nonzero. -/
theorem nondegenerate_iff_gramDet_ne_zero (hh : h.IsSymm)
    (e : Basis ι (QuadraticAlgebra ℚ a b) W) : h.Nondegenerate ↔ gramDet h e ≠ 0 := by
  have hR : h.SeparatingRight ↔ gramDet h e ≠ 0 := by
    rw [gramDet, ne_eq, ← exists_mulVec_eq_zero_iff]
    constructor
    · rintro hsep ⟨v, hv0, hv⟩
      refine hv0 (e.equivFun.symm.injective ?_)
      rw [map_zero]
      refine hsep _ fun x ↦ ?_
      rw [← e.equivFun.symm_apply_apply x, ← star_dotProduct_toMatrix₂_mulVec, hv,
        dotProduct_zero]
    · intro hdet y hy
      by_contra hy0
      refine hdet ⟨e.repr y, by simpa using hy0, ?_⟩
      funext i
      have := hy (e i)
      rw [apply_eq_star_dotProduct_toMatrix₂_mulVec e] at this
      simpa [Finsupp.single_apply, dotProduct, apply_ite star, ite_mul] using this
  rw [← hR]
  refine ⟨And.right, fun hsep ↦ ⟨fun x hx ↦ hsep x fun y ↦ ?_, hsep⟩⟩
  rw [← hh.eq, hx, map_zero]

/-- A nondegenerate Hermitian form has nonzero rational Gram determinant. -/
theorem gramDetℚ_ne_zero (hh : h.IsSymm) (hn : h.Nondegenerate)
    (e : Basis ι (QuadraticAlgebra ℚ a b) W) : gramDetℚ h e ≠ 0 := by
  intro h0
  apply (nondegenerate_iff_gramDet_ne_zero hh e).1 hn
  rw [← algebraMap_gramDetℚ hh, h0, map_zero]

variable [Module.Finite (QuadraticAlgebra ℚ a b) W]

/-- The determinant class `[det h] ∈ ℚˣ ⧸ Nm(Kˣ)` of a nondegenerate Hermitian form `h` on a
finite-dimensional `K`-space, for `K = QuadraticAlgebra ℚ a b` imaginary quadratic. It is the class
of the rational Gram determinant in any basis (`detClass_eq`); the basis used to define it is
`Module.finBasis`.

Convention: determinant, matching F-1569 (1). There is no sign factor. Some sources call
`(-1) ^ (n (n - 1) / 2) · det` the discriminant; in dimension 6 that factor is `-1` and would
turn `[-2]` into `[2]`.

Source: the target group `ℚ^× / N(K^×)` is the quotient by the group of norms of Serre,
*A Course in Arithmetic*, GTM 7, Ch. III §1.1, Prop. 1. That the class of the Gram determinant
does not depend on the basis is proved here (`gramDetℚ_basis_change`, `detClass_eq`). -/
noncomputable def detClass (h : W →ₗ⋆[QuadraticAlgebra ℚ a b] W →ₗ[QuadraticAlgebra ℚ a b]
    QuadraticAlgebra ℚ a b) (hh : h.IsSymm) (hn : h.Nondegenerate) :
    ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ a b) :=
  (Units.mk0 (gramDetℚ h (Module.finBasis _ W)) (gramDetℚ_ne_zero hh hn _) : ℚˣ)

/-- Basis independence: `detClass h` is the class of the rational Gram determinant of `h` in any
basis `e`. -/
theorem detClass_eq (hh : h.IsSymm) (hn : h.Nondegenerate)
    (e : Basis ι (QuadraticAlgebra ℚ a b) W) :
    detClass h hh hn = ((Units.mk0 (gramDetℚ h e) (gramDetℚ_ne_zero hh hn e) : ℚˣ) :
      ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ a b)) := by
  set f := Module.finBasis (QuadraticAlgebra ℚ a b) W
  let σ : ι ≃ Fin (finrank (QuadraticAlgebra ℚ a b) W) :=
    Fintype.equivOfCardEq (by rw [← finrank_eq_card_basis e, Fintype.card_fin])
  have hre : gramDetℚ h (e.reindex σ) = gramDetℚ h e := by
    rw [gramDetℚ, gramDetℚ, gramDet_reindex]
  have hu : IsUnit ((e.reindex σ).det f) := Basis.isUnit_det _ _
  refine mk_eq_mk_of_eq_mul (n := Units.map (Algebra.norm ℚ : QuadraticAlgebra ℚ a b →* ℚ)
    hu.unit) ⟨_, rfl⟩ ?_
  simpa [hre] using gramDetℚ_basis_change hh (e.reindex σ) f

/-- `detClass (-h) = [-1] ^ n * detClass h` for `n = dim_K W`. -/
theorem detClass_neg (hh : h.IsSymm) (hn : h.Nondegenerate) :
    detClass (-h) (isSymm_neg hh) (nondegenerate_neg hn) =
      (((-1 : ℚˣ) ^ finrank (QuadraticAlgebra ℚ a b) W : ℚˣ) :
        ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ a b)) * detClass h hh hn := by
  rw [detClass, detClass, ← QuotientGroup.mk_mul]
  congr 1
  ext
  simp [gramDetℚ_neg]

/-- In the imaginary quadratic case `discr a b < 0` and odd dimension, `h` and `-h` have different
determinant classes, because `-1` is not a norm. -/
theorem detClass_neg_ne (hd : discr a b < 0) (hodd : Odd (finrank (QuadraticAlgebra ℚ a b) W))
    (hh : h.IsSymm) (hn : h.Nondegenerate) :
    detClass (-h) (isSymm_neg hh) (nondegenerate_neg hn) ≠ detClass h hh hn := by
  rw [detClass_neg hh hn, hodd.neg_one_pow, ne_eq, mul_eq_right, QuotientGroup.eq_one_iff]
  intro hmem
  have := pos_of_mem_normSubgroup hd hmem
  norm_num at this

end Class

section Diagonal

variable {a b : ℚ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The diagonal Hermitian form `⟨d₁, …, dₙ⟩` on `Kⁿ`, `h x y = ∑ i, star (x i) * d i * y i`,
for rational `d i`.

Source: the diagonal Hermitian form whose Gram matrix in the standard basis is
`diag(d₁, …, dₙ)`, computed here (`toMatrix₂_diagForm`). -/
noncomputable def diagForm (d : ι → ℚ) :
    (ι → QuadraticAlgebra ℚ a b) →ₗ⋆[QuadraticAlgebra ℚ a b] (ι → QuadraticAlgebra ℚ a b)
      →ₗ[QuadraticAlgebra ℚ a b] QuadraticAlgebra ℚ a b :=
  Matrix.toLinearMapₛₗ₂ (starRingEnd _) (Pi.basisFun _ ι) (Pi.basisFun _ ι)
    (diagonal fun i ↦ algebraMap ℚ _ (d i))

/-- `⟨d⟩(x, y) = ∑ i, star (x i) * d i * y i`. -/
theorem diagForm_apply (d : ι → ℚ) (x y : ι → QuadraticAlgebra ℚ a b) :
    diagForm d x y = ∑ i, star (x i) * algebraMap ℚ _ (d i) * y i := by
  simp only [diagForm, Matrix.toLinearMapₛₗ₂_apply, diagonal_apply, Pi.basisFun_repr,
    smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [starRingEnd_apply]
  ring

/-- The Gram matrix of `diagForm d` in the standard basis is `diag(d)`. -/
theorem toMatrix₂_diagForm (d : ι → ℚ) :
    LinearMap.toMatrix₂ (Pi.basisFun _ ι) (Pi.basisFun _ ι) (diagForm (a := a) (b := b) d) =
      diagonal fun i ↦ algebraMap ℚ _ (d i) :=
  LinearMap.toMatrix₂_toLinearMapₛₗ₂ _ _ _

/-- `diagForm d` is Hermitian (its entries are rational, hence `star`-fixed). -/
theorem diagForm_isSymm (d : ι → ℚ) : (diagForm (a := a) (b := b) d).IsSymm := by
  rw [LinearMap.isSymm_iff_isHermitian_toMatrix (Pi.basisFun _ ι), toMatrix₂_diagForm]
  exact isHermitian_diagonal_of_self_adjoint _ <| funext fun i ↦
    QuadraticAlgebra.ext (by simp) (by simp)

/-- The rational Gram determinant of `diagForm d` in the standard basis is `∏ i, d i`. -/
theorem gramDetℚ_diagForm (d : ι → ℚ) :
    gramDetℚ (diagForm (a := a) (b := b) d) (Pi.basisFun _ ι) = ∏ i, d i := by
  rw [gramDetℚ, gramDet, toMatrix₂_diagForm, det_diagonal, ← map_prod]
  rfl

variable [Fact (∀ r : ℚ, r ^ 2 ≠ a + b * r)]

/-- `diagForm d` is nondegenerate when every `d i` is nonzero. -/
theorem diagForm_nondegenerate {d : ι → ℚ} (hd : ∀ i, d i ≠ 0) :
    (diagForm (a := a) (b := b) d).Nondegenerate := by
  rw [nondegenerate_iff_gramDet_ne_zero (diagForm_isSymm d) (Pi.basisFun _ ι),
    ← algebraMap_gramDetℚ (diagForm_isSymm d), gramDetℚ_diagForm, ne_eq,
    FaithfulSMul.algebraMap_eq_zero_iff]
  exact Finset.prod_ne_zero_iff.2 fun i _ ↦ hd i

/-- `detClass ⟨d₁, …, dₙ⟩ = [d₁ ⋯ dₙ]`. -/
theorem detClass_diagForm {d : ι → ℚ} (hd : ∀ i, d i ≠ 0) :
    detClass (diagForm (a := a) (b := b) d) (diagForm_isSymm d) (diagForm_nondegenerate hd) =
      ((Units.mk0 (∏ i, d i) (Finset.prod_ne_zero_iff.2 fun i _ ↦ hd i) : ℚˣ) :
        ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ a b)) := by
  rw [detClass_eq _ _ (Pi.basisFun _ ι)]
  congr 1
  ext
  simp [gramDetℚ_diagForm]

end Diagonal

section Descent

/-- `p² + 3 q² = 2 n²` has no integer solution with `n ≠ 0`: reduce mod 3, then descend. -/
theorem eq_zero_of_sq_add_three_mul_sq_eq_two_mul_sq :
    ∀ (n : ℕ) (p q : ℤ), p ^ 2 + 3 * q ^ 2 = 2 * (n : ℤ) ^ 2 → n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro p q hpq
  by_contra hn
  have key : ∀ x y z : ZMod 3, x ^ 2 + 3 * z ^ 2 = 2 * y ^ 2 → x = 0 ∧ y = 0 := by decide
  have hmod := congrArg (Int.cast : ℤ → ZMod 3) hpq
  push_cast at hmod
  obtain ⟨hp3, hn3⟩ := key _ _ _ hmod
  obtain ⟨p', rfl⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd p 3).1 hp3
  obtain ⟨n', rfl⟩ := (ZMod.natCast_eq_zero_iff n 3).1 hn3
  have hq : (3 : ℤ) ∣ q ^ 2 := ⟨2 * (n' : ℤ) ^ 2 - p' ^ 2, by push_cast at hpq; linarith⟩
  obtain ⟨q', rfl⟩ := Int.prime_three.dvd_of_dvd_pow hq
  have h' : p' ^ 2 + 3 * q' ^ 2 = 2 * (n' : ℤ) ^ 2 := by push_cast at hpq; linarith
  have := ih n' (by omega) p' q' h'
  omega

/-- `x² + 3 y² = 2` has no rational solution. -/
theorem sq_add_three_mul_sq_ne_two (x y : ℚ) : x ^ 2 + 3 * y ^ 2 ≠ 2 := by
  intro hxy
  have hx : (x.num : ℚ) = x * x.den := (Rat.mul_den_eq_num x).symm
  have hy : (y.num : ℚ) = y * y.den := (Rat.mul_den_eq_num y).symm
  have hint : (x.num * y.den) ^ 2 + 3 * (y.num * x.den) ^ 2 =
      2 * ((x.den * y.den : ℕ) : ℤ) ^ 2 := by
    have : ((x.num * y.den : ℤ) : ℚ) ^ 2 + 3 * ((y.num * x.den : ℤ) : ℚ) ^ 2 =
        2 * ((x.den * y.den : ℕ) : ℚ) ^ 2 := by
      push_cast
      rw [hx, hy]
      linear_combination ((x.den : ℚ) * y.den) ^ 2 * hxy
    exact_mod_cast this
  have := eq_zero_of_sq_add_three_mul_sq_eq_two_mul_sq _ _ _ hint
  simp [x.den_nz, y.den_nz] at this

end Descent

section Signature

variable {a b : ℚ} {W : Type*} [AddCommGroup W] [Module (QuadraticAlgebra ℚ a b) W]
  [Module ℚ W] [IsScalarTower ℚ (QuadraticAlgebra ℚ a b) W]

/-- `re (r * z) = r * re z` for rational `r`. -/
theorem re_algebraMap_mul (r : ℚ) (z : QuadraticAlgebra ℚ a b) :
    (algebraMap ℚ _ r * z).re = r * z.re := by
  rw [← Algebra.smul_def, re_smul, smul_eq_mul]

/-- The `ℚ`-bilinear form `(x, y) ↦ re (h x y)` on the underlying `ℚ`-space of `W`.

Source: restriction of scalars of a sesquilinear form from `K` to the fixed field `ℚ` of the
involution, followed by the `ℚ`-linear coordinate `re : K → ℚ`. -/
noncomputable def reBilin
    (h : W →ₗ⋆[QuadraticAlgebra ℚ a b] W →ₗ[QuadraticAlgebra ℚ a b] QuadraticAlgebra ℚ a b) :
    LinearMap.BilinForm ℚ W :=
  LinearMap.mk₂ ℚ (fun x y ↦ (h x y).re)
    (fun x x' y ↦ by simp)
    (fun r x y ↦ by
      rw [← algebraMap_smul (QuadraticAlgebra ℚ a b) r x, LinearMap.map_smulₛₗ,
        LinearMap.smul_apply, starRingEnd_apply,
        show star (algebraMap ℚ (QuadraticAlgebra ℚ a b) r) = algebraMap ℚ _ r from
          QuadraticAlgebra.ext (by simp) (by simp),
        smul_eq_mul, re_algebraMap_mul, smul_eq_mul])
    (fun x y y' ↦ by simp)
    (fun r x y ↦ by
      rw [← algebraMap_smul (QuadraticAlgebra ℚ a b) r y, LinearMap.map_smul, smul_eq_mul,
        re_algebraMap_mul, smul_eq_mul])

/-- The rational quadratic form `x ↦ h x x` on the underlying `ℚ`-space of `W` (for Hermitian `h`,
`h x x` is rational, and this is its value).

Source: restriction of scalars of `x ↦ h(x, x)` to the fixed field `ℚ` of the involution; its
value on `x` is `re (h x x)` by definition (`hermQuadForm_apply`). -/
noncomputable def hermQuadForm
    (h : W →ₗ⋆[QuadraticAlgebra ℚ a b] W →ₗ[QuadraticAlgebra ℚ a b] QuadraticAlgebra ℚ a b) :
    QuadraticForm ℚ W :=
  (reBilin h).toQuadraticMap

/-- `hermQuadForm h x = re (h x x)`. -/
theorem hermQuadForm_apply
    (h : W →ₗ⋆[QuadraticAlgebra ℚ a b] W →ₗ[QuadraticAlgebra ℚ a b] QuadraticAlgebra ℚ a b)
    (x : W) : hermQuadForm h x = (h x x).re :=
  rfl

/-- The signature `(r, s)` of a Hermitian form `h` over an imaginary quadratic field: half the
real signature `(sigPos, sigNeg)` of the rational quadratic form `x ↦ h x x` on the underlying
`ℚ`-space, base-changed to `ℝ`.

The underlying `ℚ`-space has twice the `K`-dimension, and a Hermitian form of signature `(r, s)`
has real part of signature `(2r, 2s)`, hence the division by `2`.

Source: Sylvester's law of inertia for the real quadratic form `x ↦ h(x, x)` on the underlying
real space (Mathlib's `QuadraticForm.sigPos` and `sigNeg`). That its signature is twice the
Hermitian one is proved here for diagonal forms (`hermSignature_diagForm`). -/
noncomputable def hermSignature
    (h : W →ₗ⋆[QuadraticAlgebra ℚ a b] W →ₗ[QuadraticAlgebra ℚ a b] QuadraticAlgebra ℚ a b) :
    ℕ × ℕ :=
  (sigPos ((hermQuadForm h).baseChange ℝ) / 2,
    sigNeg ((hermQuadForm h).baseChange ℝ) / 2)

end Signature

section DiagSignature

open QuadraticMap

variable {a : ℚ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Over `ℚ(√a)`, `⟨d⟩(x, x) = ∑ i, d i ((x i).re² - a (x i).im²)`. -/
theorem hermQuadForm_diagForm (d : ι → ℚ) (x : ι → QuadraticAlgebra ℚ a 0) :
    hermQuadForm (diagForm (a := a) (b := 0) d) x =
      ∑ i, d i * ((x i).re ^ 2 - a * (x i).im ^ 2) := by
  rw [hermQuadForm_apply, diagForm_apply, ← reₗ_apply (R := ℚ) a 0, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [reₗ_apply, re_mul, im_mul, re_star, im_star, algebraMap_re, algebraMap_im]
  ring

/-- The `ℚ`-linear identification `(ι → ℚ(√a)) ≃ (ι × Fin 2 → ℚ)`, `x ↦ ((x i).re, (x i).im)`.

Source: the coordinates of `ℚ(√a)ⁿ` in the `ℚ`-basis `(1, √a)` of each factor
(`QuadraticAlgebra.linearEquivTuple`). -/
noncomputable def tupleEquiv : (ι → QuadraticAlgebra ℚ a 0) ≃ₗ[ℚ] (ι × Fin 2 → ℚ) :=
  (LinearEquiv.piCongrRight fun _ ↦ linearEquivTuple a 0).trans
    (LinearEquiv.curry ℚ ℚ ι (Fin 2)).symm

/-- The weights `(d i, -a · d i)` of `x ↦ ∑ d i (re² - a im²)` as a sum of squares over `ℝ`.

Source: `Nm(x + y√a) = x² - a y²`, so `⟨d⟩(x, x) = ∑ i, d i ((x i).re² - a (x i).im²)`
(`hermQuadForm_diagForm`). -/
noncomputable def diagWeights (a : ℚ) (d : ι → ℚ) : ι × Fin 2 → ℝ :=
  fun k ↦ (d k.1 * ![1, -a] k.2 : ℚ)

/-- Over `ℝ`, the base change of the rational form of `⟨d⟩` is the weighted sum of squares
`diagWeights a d` in the coordinates given by `tupleEquiv`. -/
theorem baseChange_hermQuadForm_diagForm (d : ι → ℚ) :
    (weightedSumSquares ℝ (diagWeights a d)).comp
        ((tupleEquiv.baseChange ℚ ℝ _ _).trans
          (TensorProduct.piScalarRight ℚ ℝ ℝ (ι × Fin 2))).toLinearMap =
      (hermQuadForm (diagForm (a := a) (b := 0) d)).baseChange ℝ := by
  ext m
  simp [weightedSumSquares_apply, Fintype.sum_prod_type, Fin.sum_univ_two, diagWeights,
    hermQuadForm_diagForm, tupleEquiv, LinearEquiv.baseChange_tmul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  norm_cast
  ring

/-- Over `ℝ`, the rational form of `⟨d⟩` is the weighted sum of squares with weights
`(d i, -a · d i)`. -/
theorem equivalent_diagWeights (d : ι → ℚ) :
    Equivalent ((hermQuadForm (diagForm (a := a) (b := 0) d)).baseChange ℝ)
      (weightedSumSquares ℝ (diagWeights a d)) :=
  ⟨{ toLinearEquiv := (tupleEquiv.baseChange ℚ ℝ _ _).trans
        (TensorProduct.piScalarRight ℚ ℝ ℝ (ι × Fin 2))
     map_app' := fun m ↦ by
       rw [← baseChange_hermQuadForm_diagForm d]
       rfl }⟩

/-- For `K = ℚ(√a)` with `a < 0`, the diagonal form `⟨d₁, …, dₙ⟩` has signature
`(#{i | 0 < d i}, #{i | d i < 0})`. -/
theorem hermSignature_diagForm (ha : a < 0) (d : ι → ℚ) :
    hermSignature (diagForm (a := a) (b := 0) d) =
      ({i | 0 < d i}.ncard, {i | d i < 0}.ncard) := by
  have hc : ∀ j : Fin 2, (0 : ℝ) < ((![1, -a] j : ℚ) : ℝ) := by
    intro j; fin_cases j <;> simp [ha]
  have hpos : {k : ι × Fin 2 | 0 < diagWeights a d k} = {i | 0 < d i} ×ˢ Set.univ := by
    ext ⟨i, j⟩
    simp only [diagWeights, Rat.cast_mul, Set.mem_ofPred_eq, Set.mem_prod, Set.mem_univ,
      and_true]
    exact (mul_pos_iff_of_pos_right (hc j)).trans Rat.cast_pos
  have hneg : {k : ι × Fin 2 | diagWeights a d k < 0} = {i | d i < 0} ×ˢ Set.univ := by
    ext ⟨i, j⟩
    simp only [diagWeights, Rat.cast_mul, Set.mem_ofPred_eq, Set.mem_prod, Set.mem_univ,
      and_true]
    exact ⟨fun h ↦ Rat.cast_lt_zero.1 (lt_of_not_ge fun hd ↦
      (not_lt.2 (mul_nonneg hd (hc j).le)) h),
      fun h ↦ mul_neg_of_neg_of_pos (Rat.cast_lt_zero.2 h) (hc j)⟩
  rw [hermSignature, QuadraticForm.sigPos_of_equiv_weightedSumSquares (equivalent_diagWeights d),
    QuadraticForm.sigNeg_of_equiv_weightedSumSquares (equivalent_diagWeights d), hpos, hneg,
    Set.ncard_prod, Set.ncard_prod, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
  simp

end DiagSignature

section SqrtNegThree

/-! ### `K = ℚ(√-3)`, presented as `QuadraticAlgebra ℚ (-3) 0` (`ω = √-3`, `ω² = -3`) -/

/-- `-3` is not a square in `ℚ`. -/
theorem not_isSquare_neg_three : ¬ IsSquare (-3 : ℚ) := by
  exact not_isSquare_of_neg (by norm_num)

instance : Fact (¬ IsSquare (-3 : ℚ)) := ⟨not_isSquare_neg_three⟩

/-- `ℚ(√-3)` is imaginary quadratic: its discriminant is `-12`. -/
theorem discr_neg_three : discr (-3 : ℚ) 0 = -12 := by
  norm_num [discr_def]

example : Field (QuadraticAlgebra ℚ (-3) 0) := inferInstance

/-- `12 = Nm(2√-3)` lies in `Nm(ℚ(√-3)ˣ)`. -/
example : Units.mk0 (12 : ℚ) (by norm_num) ∈ normSubgroup (QuadraticAlgebra ℚ (-3) 0) :=
  mem_normSubgroup_iff.2 ⟨⟨0, 2⟩, by norm_num [norm_def]⟩

/-- `81 = Nm(9)` lies in `Nm(ℚ(√-3)ˣ)`. -/
example : Units.mk0 (81 : ℚ) (by norm_num) ∈ normSubgroup (QuadraticAlgebra ℚ (-3) 0) :=
  mem_normSubgroup_iff.2 ⟨9, by norm_num [norm_def]⟩

/-- The Gram determinant of `⟨1, 1, 1, -1, -1, -2⟩` in the standard basis of `ℚ(√-3)⁶` is `-2`. -/
example : gramDet (diagForm (a := -3) (b := 0) ![1, 1, 1, -1, -1, -2])
    (Pi.basisFun _ (Fin 6)) = -2 := by
  rw [← algebraMap_gramDetℚ (diagForm_isSymm _), gramDetℚ_diagForm]
  norm_num [Fin.prod_univ_succ]

/-- The rational Gram determinant of `⟨1, 1, 1, -1, -1, -2⟩` is `-2`. -/
example : gramDetℚ (diagForm (a := -3) (b := 0) ![1, 1, 1, -1, -1, -2])
    (Pi.basisFun _ (Fin 6)) = -2 := by
  rw [gramDetℚ_diagForm]
  norm_num [Fin.prod_univ_succ]

/-- The entries of `⟨1, 1, 1, -1, -1, -2⟩` are nonzero. -/
theorem diag_F1569_ne_zero : ∀ i, (![1, 1, 1, -1, -1, -2] : Fin 6 → ℚ) i ≠ 0 := by
  intro i
  fin_cases i <;> norm_num

/-- The Hermitian form `⟨1, 1, 1, -1, -1, -2⟩` on `ℚ(√-3)⁶` (signature (3,3), determinant `-2`)
has determinant class `[-2]`. This is the form `diag(1, 1, 1, -1, -1, -2)`; the form
`diag(1, 1, 1, -1, -1, 2)` would have determinant `+2` and signature (4,2). -/
theorem detClass_diag_F1569 :
    detClass (diagForm (a := -3) (b := 0) ![1, 1, 1, -1, -1, -2]) (diagForm_isSymm _)
        (diagForm_nondegenerate diag_F1569_ne_zero) =
      ((Units.mk0 (-2 : ℚ) (by norm_num) : ℚˣ) :
        ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0)) := by
  rw [detClass_diagForm diag_F1569_ne_zero]
  congr 1
  ext
  norm_num [Fin.prod_univ_succ]

/-- `diagForm` evaluated: `⟨1, -2⟩(x, y) = x̄₀ y₀ - 2 x̄₁ y₁`, here at `x = y = (√-3, 1)`. -/
example : diagForm (a := -3) (b := 0) ![1, -2] ![ω, 1] ![ω, 1] = 1 := by
  rw [diagForm_apply]
  ext <;> norm_num [Fin.sum_univ_succ]

/-- The entries of `⟨1, 1, 1, -1, -1, 2⟩` are nonzero. -/
theorem diag_two_ne_zero : ∀ i, (![1, 1, 1, -1, -1, 2] : Fin 6 → ℚ) i ≠ 0 := by
  intro i
  fin_cases i <;> norm_num

/-- `reBilin` and `hermQuadForm` of `⟨1, -2⟩` at `x = (√-3, 1)`: `h x x = 3 - 2 = 1`. -/
example : reBilin (diagForm (a := -3) (b := 0) ![1, -2]) ![ω, 1] ![ω, 1] = 1 ∧
    hermQuadForm (diagForm (a := -3) (b := 0) ![1, -2]) ![ω, 1] = 1 := by
  have : (diagForm (a := -3) (b := 0) ![1, -2] ![ω, 1] ![ω, 1]).re = 1 := by
    rw [diagForm_apply]
    norm_num [Fin.sum_univ_succ]
  exact ⟨this, (hermQuadForm_apply _ _).trans this⟩

/-- `tupleEquiv` sends `(1 + 2√-3)` to its coordinates `(1, 2)`. -/
example : tupleEquiv (a := -3) (ι := Fin 1) ![⟨1, 2⟩] = fun k ↦ ![1, 2] k.2 := by
  funext ⟨i, j⟩
  fin_cases i; fin_cases j <;> rfl

/-- `diagWeights` of `⟨1, -2⟩` over `ℚ(√-3)`: the weights are `(1, 3, -2, -6)`. -/
example : diagWeights (-3) ![(1 : ℚ), -2] (1, 1) = -6 := by
  norm_num [diagWeights]

/-- The Hermitian form `⟨1, 1, 1, -1, -1, -2⟩` on `ℚ(√-3)⁶` has signature `(3, 3)`. -/
theorem hermSignature_diag_F1569 :
    hermSignature (diagForm (a := -3) (b := 0) ![1, 1, 1, -1, -1, -2]) = (3, 3) := by
  rw [hermSignature_diagForm (by norm_num)]
  have hp : {i : Fin 6 | 0 < (![1, 1, 1, -1, -1, -2] : Fin 6 → ℚ) i} =
      ↑({0, 1, 2} : Finset (Fin 6)) := by
    ext i; fin_cases i <;> norm_num
  have hn : {i : Fin 6 | (![1, 1, 1, -1, -1, -2] : Fin 6 → ℚ) i < 0} =
      ↑({3, 4, 5} : Finset (Fin 6)) := by
    ext i; fin_cases i <;> norm_num
  rw [hp, hn, Set.ncard_coe_finset, Set.ncard_coe_finset]
  rfl

/-- Falsification check: `diag(1, 1, 1, -1, -1, 2)` has signature `(4, 2)`, not `(3, 3)`. -/
example : hermSignature (diagForm (a := -3) (b := 0) ![1, 1, 1, -1, -1, 2]) = (4, 2) := by
  rw [hermSignature_diagForm (by norm_num)]
  have hp : {i : Fin 6 | 0 < (![1, 1, 1, -1, -1, 2] : Fin 6 → ℚ) i} =
      ↑({0, 1, 2, 5} : Finset (Fin 6)) := by
    ext i; fin_cases i <;> norm_num
  have hn : {i : Fin 6 | (![1, 1, 1, -1, -1, 2] : Fin 6 → ℚ) i < 0} =
      ↑({3, 4} : Finset (Fin 6)) := by
    ext i; fin_cases i <;> norm_num
  rw [hp, hn, Set.ncard_coe_finset, Set.ncard_coe_finset]
  rfl

/-- Falsification check: the survey's `diag(1, 1, 1, -1, -1, 2)` (determinant `+2`) has a
different class from `diag(1, 1, 1, -1, -1, -2)`, since `[2] = [-1] · [-2]` and `-1` is not a
norm. -/
theorem detClass_diag_two_ne :
    detClass (diagForm (a := -3) (b := 0) ![1, 1, 1, -1, -1, 2]) (diagForm_isSymm _)
        (diagForm_nondegenerate diag_two_ne_zero) ≠
      detClass (diagForm (a := -3) (b := 0) ![1, 1, 1, -1, -1, -2]) (diagForm_isSymm _)
        (diagForm_nondegenerate diag_F1569_ne_zero) := by
  rw [detClass_diagForm diag_two_ne_zero, detClass_diagForm diag_F1569_ne_zero, ne_eq,
    QuotientGroup.eq]
  intro hmem
  have := pos_of_mem_normSubgroup (by norm_num [discr_def]) hmem
  norm_num [Fin.prod_univ_succ] at this

/-- In `ℚˣ ⧸ Nm(ℚ(√-3)ˣ)`, `[-2/81] = [-2] = [-24]`, with witnesses `81 = Nm(9)` and
`12 = Nm(2√-3)`.

Checks: F-1569 -/
theorem classes_F1569 :
    ((Units.mk0 (-2 / 81 : ℚ) (by norm_num) : ℚˣ) :
        ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0)) =
      ((Units.mk0 (-2 : ℚ) (by norm_num) : ℚˣ) :
        ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0)) ∧
    ((Units.mk0 (-2 : ℚ) (by norm_num) : ℚˣ) :
        ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0)) =
      ((Units.mk0 (-24 : ℚ) (by norm_num) : ℚˣ) :
        ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0)) := by
  constructor
  · -- `-2 = Nm(9) · (-2/81)`
    refine (mk_eq_mk_of_eq_mul (n := Units.mk0 81 (by norm_num))
      (mem_normSubgroup_iff.2 ⟨9, by norm_num [norm_def]⟩) ?_).symm
    norm_num
  · -- `-24 = Nm(2√-3) · (-2)`
    refine (mk_eq_mk_of_eq_mul (n := Units.mk0 12 (by norm_num))
      (mem_normSubgroup_iff.2 ⟨⟨0, 2⟩, by norm_num [norm_def]⟩) ?_).symm
    norm_num

/-- `[-2] ≠ [1]` in `ℚˣ ⧸ Nm(ℚ(√-3)ˣ)`: norms from an imaginary quadratic field are positive. -/
theorem class_neg_two_ne_one :
    ((Units.mk0 (-2 : ℚ) (by norm_num) : ℚˣ) :
      ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0)) ≠ 1 := by
  rw [ne_eq, QuotientGroup.eq_one_iff]
  intro hmem
  have := pos_of_mem_normSubgroup (by norm_num [discr_def]) hmem
  norm_num at this

/-- `[2] ≠ [1]` in `ℚˣ ⧸ Nm(ℚ(√-3)ˣ)`: `x² + 3 y² = 2` has no rational solution. -/
theorem class_two_ne_one :
    ((Units.mk0 (2 : ℚ) (by norm_num) : ℚˣ) :
      ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0)) ≠ 1 := by
  rw [ne_eq, QuotientGroup.eq_one_iff]
  intro hmem
  obtain ⟨z, hz⟩ := mem_normSubgroup_iff.1 hmem
  apply sq_add_three_mul_sq_ne_two z.re z.im
  rw [norm_def] at hz
  simp only [Units.val_mk0] at hz
  linear_combination hz

/-- In odd dimension, `h` and `-h` have different classes: for `⟨1⟩` on `ℚ(√-3)¹`,
`detClass (-⟨1⟩) ≠ detClass ⟨1⟩`. -/
example : detClass (-diagForm (a := -3) (b := 0) ![(1 : ℚ)]) (isSymm_neg (diagForm_isSymm _))
      (nondegenerate_neg (diagForm_nondegenerate (by simp))) ≠
    detClass (diagForm (a := -3) (b := 0) ![(1 : ℚ)]) (diagForm_isSymm _)
      (diagForm_nondegenerate (by simp)) :=
  detClass_neg_ne (by norm_num [discr_def]) (by simp) _ _

end SqrtNegThree

end HermitianForm

end HodgeLean.Foundations
