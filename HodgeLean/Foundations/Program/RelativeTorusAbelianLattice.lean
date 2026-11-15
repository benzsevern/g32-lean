import HodgeLean.Foundations.Program.RelativeTorusAbelianDefs
import HodgeLean.Adapters.AbelianCMData
import HodgeLean.Adapters.AbelianEndomorphisms2
import HodgeLean.Adapters.DegreeOneLattice
import HodgeLean.Adapters.ExpHolomorphic
import HodgeLean.Adapters.LatticeClassHQ

/-!
# Track B2, comparison with abelian varieties: lattice algebra

Helpers for `RelativeTorusAbelianProofs.lean`. For a lattice `Λ`, conjugation on `ℂ ⊗[ℤ] Λ` is
conjugate-linear and involutive, and the base change of a form commutes with it. For the S12
period lattice `Λ_X ⊂ ℂ^g`, the real lift `r : ℂ^g → ℂ ⊗[ℤ] Λ_X` (coordinates in a real basis
of `Λ_X`) is a section of the evaluation fixed by conjugation; every vector is `r x + i r y`, and
the period filtration is the image of `f v = r (i v) - i r v`.
HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open scoped TensorProduct CategoryTheory.MonObj
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Adapters

namespace HodgeLean.Foundations.Program

section Conj

variable {Λ : Type*} [AddCommGroup Λ]

theorem b2v_conj_tmul (c : ℂ) (x : Λ) : b2_conj Λ (c ⊗ₜ[ℤ] x) = (starRingEnd ℂ c) ⊗ₜ[ℤ] x :=
  rfl

theorem b2v_conj_smul (c : ℂ) (u : ℂ ⊗[ℤ] Λ) :
    b2_conj Λ (c • u) = starRingEnd ℂ c • b2_conj Λ u := by
  induction u using TensorProduct.inductionOn with
  | tmul d x =>
    rw [TensorProduct.smul_tmul', b2v_conj_tmul, b2v_conj_tmul, TensorProduct.smul_tmul',
      smul_eq_mul, smul_eq_mul, map_mul]
  | add u w hu hw => rw [smul_add, map_add, hu, hw, map_add, smul_add]

theorem b2v_conj_conj (u : ℂ ⊗[ℤ] Λ) : b2_conj Λ (b2_conj Λ u) = u := by
  induction u using TensorProduct.inductionOn with
  | tmul d x => rw [b2v_conj_tmul, b2v_conj_tmul, Complex.conj_conj]
  | add u w hu hw => rw [map_add, map_add, hu, hw]

/-- Conjugation as a conjugate-linear map.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.2 (the real structure of
`Λ ⊗ ℂ`); Mathlib `LinearMap` over `starRingEnd ℂ`. -/
def b2a_conjSL : (ℂ ⊗[ℤ] Λ) →ₛₗ[starRingEnd ℂ] (ℂ ⊗[ℤ] Λ) where
  toFun := b2_conj Λ
  map_add' := map_add _
  map_smul' := b2v_conj_smul

example (c : ℂ) (x : Λ) : b2a_conjSL (c ⊗ₜ[ℤ] x) = starRingEnd ℂ c ⊗ₜ[ℤ] x := rfl

theorem b2a_conjSubmodule_eq (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) :
    b2_conjSubmodule Λ F = F.map b2a_conjSL := by
  rw [b2_conjSubmodule]
  exact Submodule.span_eq (F.map b2a_conjSL)

theorem b2a_baseChange_conj (Q : LinearMap.BilinForm ℤ Λ) (u w : ℂ ⊗[ℤ] Λ) :
    Q.baseChange ℂ (b2_conj Λ u) (b2_conj Λ w) = starRingEnd ℂ (Q.baseChange ℂ u w) := by
  induction u using TensorProduct.inductionOn with
  | add u u' hu hu' => simp only [map_add, LinearMap.add_apply, hu, hu']
  | tmul c x =>
    induction w using TensorProduct.inductionOn with
    | add w w' hw hw' => simp only [map_add, hw, hw']
    | tmul d y =>
      simp only [b2v_conj_tmul, LinearMap.BilinForm.baseChange_tmul, zsmul_eq_mul, map_mul,
        map_intCast]

theorem b2a_baseChange_antisymm (Q : LinearMap.BilinForm ℤ Λ) (hQ : ∀ x, Q x x = 0)
    (u w : ℂ ⊗[ℤ] Λ) : Q.baseChange ℂ u w = - Q.baseChange ℂ w u := by
  have hanti : ∀ x y, Q x y = - Q y x := fun x y ↦ by
    have h := hQ (x + y)
    simp only [map_add, LinearMap.add_apply, hQ x, hQ y, zero_add, add_zero] at h
    exact eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact h)
  induction u using TensorProduct.inductionOn with
  | add u u' hu hu' => simp only [map_add, LinearMap.add_apply, hu, hu', neg_add]
  | tmul c x =>
    induction w using TensorProduct.inductionOn with
    | add w w' hw hw' => simp only [map_add, LinearMap.add_apply, hw, hw', neg_add]
    | tmul d y =>
      simp only [LinearMap.BilinForm.baseChange_tmul, hanti x y, zsmul_eq_mul, Int.cast_neg]
      ring

end Conj

section Abelian

variable (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

/-- The period lattice is a full lattice of `ℂ^g`. -/
instance b2a_isZLattice : IsZLattice ℝ (abelianPeriodLattice X) := by
  let : IsCommMonObj X := isCommMonObj_of_complexSelfProductIntegral X
    (complexSelfProductIntegral_of_isIntegral X)
  exact isZLattice_complexExponentialLattice X (dim X.left)

/-- The period lattice is discrete. -/
instance b2a_discrete : DiscreteTopology (abelianPeriodLattice X) := by
  let : IsCommMonObj X := isCommMonObj_of_complexSelfProductIntegral X
    (complexSelfProductIntegral_of_isIntegral X)
  exact discrete_complexExponentialLattice X (dim X.left)

/-- The real basis of `ℂ^g` given by the S12 basis of the period lattice.
Source: Birkenhake–Lange, §1.1 (`Λ ⊗ ℝ = ℂ^g`); Mathlib `Module.Basis.ofZLatticeBasis`. -/
def b2a_basisR : Module.Basis (Fin (2 * dim X.left)) ℝ (Fin (dim X.left) → ℂ) :=
  (abelianLatticeBasis X).ofZLatticeBasis ℝ (abelianPeriodLattice X)

example (k : Fin (2 * dim X.left)) :
    b2a_basisR X k = (abelianLatticeBasis X k : Fin (dim X.left) → ℂ) :=
  Module.Basis.ofZLatticeBasis_apply ℝ _ _ k

theorem b2a_basisR_apply (k : Fin (2 * dim X.left)) :
    b2a_basisR X k = (abelianLatticeBasis X k : Fin (dim X.left) → ℂ) :=
  Module.Basis.ofZLatticeBasis_apply ℝ _ _ k

theorem b2a_basisR_repr_coe (l : b2_abelianLattice X) (k : Fin (2 * dim X.left)) :
    (b2a_basisR X).repr (l : Fin (dim X.left) → ℂ) k = ((abelianLatticeBasis X).repr l k : ℝ) :=
  Module.Basis.ofZLatticeBasis_repr_apply ℝ _ _ l k

/-- **The real lift** `ℂ^g → ℂ ⊗[ℤ] Λ_X`, `∑ tₖ bₖ ↦ ∑ tₖ ⊗ bₖ` for the real coordinates `tₖ` in
the basis `bₖ` of `Λ_X`.
Source: Birkenhake–Lange, §1.1 (`Λ ⊗ ℝ = ℂ^g`) and §1.2 (`Λ ⊗ ℂ = V ⊕ V̄`). -/
def b2a_lift : (Fin (dim X.left) → ℂ) →+ ℂ ⊗[ℤ] b2_abelianLattice X where
  toFun v := ∑ k, (((b2a_basisR X).repr v k : ℝ) : ℂ) ⊗ₜ[ℤ] abelianLatticeBasis X k
  map_zero' := by simp
  map_add' v w := by
    simp only [map_add, Finsupp.add_apply, Complex.ofReal_add, TensorProduct.add_tmul,
      Finset.sum_add_distrib]

example : b2a_lift X 0 = 0 := map_zero _

theorem b2a_lift_apply (v : Fin (dim X.left) → ℂ) :
    b2a_lift X v = ∑ k, (((b2a_basisR X).repr v k : ℝ) : ℂ) ⊗ₜ[ℤ] abelianLatticeBasis X k :=
  rfl

theorem b2a_lift_real_smul (t : ℝ) (v : Fin (dim X.left) → ℂ) :
    b2a_lift X (t • v) = (t : ℂ) • b2a_lift X v := by
  simp only [b2a_lift_apply, LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul, Complex.ofReal_mul,
    Finset.smul_sum, TensorProduct.smul_tmul']

theorem b2a_lift_coe (l : b2_abelianLattice X) :
    b2a_lift X (l : Fin (dim X.left) → ℂ) = (1 : ℂ) ⊗ₜ[ℤ] l := by
  have h : ∀ (n : ℤ) (x : b2_abelianLattice X),
      (((n : ℝ) : ℂ)) ⊗ₜ[ℤ] x = (1 : ℂ) ⊗ₜ[ℤ] (n • x) := fun n x ↦ by
    rw [← TensorProduct.smul_tmul, zsmul_eq_mul, mul_one]
    norm_cast
  simp only [b2a_lift_apply, b2a_basisR_repr_coe, h, ← TensorProduct.tmul_sum,
    (abelianLatticeBasis X).sum_repr]

theorem b2a_eval_tmul (c : ℂ) (l : b2_abelianLattice X) :
    b2_abelianEval X (c ⊗ₜ[ℤ] l) = c • (l : Fin (dim X.left) → ℂ) := by
  simp [b2_abelianEval]

theorem b2a_eval_lift (v : Fin (dim X.left) → ℂ) : b2_abelianEval X (b2a_lift X v) = v := by
  simp only [b2a_lift_apply, map_sum, b2a_eval_tmul, Complex.coe_smul, ← b2a_basisR_apply]
  exact (b2a_basisR X).sum_repr v

theorem b2a_eval_surjective : Function.Surjective (b2_abelianEval X) :=
  fun v ↦ ⟨b2a_lift X v, b2a_eval_lift X v⟩

theorem b2a_conj_lift (v : Fin (dim X.left) → ℂ) :
    b2_conj _ (b2a_lift X v) = b2a_lift X v := by
  simp only [b2a_lift_apply, map_sum, b2v_conj_tmul, Complex.conj_ofReal]

/-- Every vector of `ℂ ⊗[ℤ] Λ_X` is `r x + i r y`. -/
theorem b2a_decomp (u : ℂ ⊗[ℤ] b2_abelianLattice X) :
    ∃ x y, u = b2a_lift X x + Complex.I • b2a_lift X y := by
  induction u using TensorProduct.inductionOn with
  | tmul c l =>
    refine ⟨c.re • (l : Fin (dim X.left) → ℂ), c.im • (l : Fin (dim X.left) → ℂ), ?_⟩
    rw [b2a_lift_real_smul, b2a_lift_real_smul, b2a_lift_coe, TensorProduct.smul_tmul',
      TensorProduct.smul_tmul', TensorProduct.smul_tmul', ← TensorProduct.add_tmul]
    congr 1
    simp only [smul_eq_mul, mul_one]
    rw [mul_comm]
    exact (Complex.re_add_im c).symm
  | add u w hu hw =>
    obtain ⟨x, y, rfl⟩ := hu
    obtain ⟨x', y', rfl⟩ := hw
    refine ⟨x + x', y + y', ?_⟩
    rw [map_add, map_add, smul_add]
    abel

/-- The vector `f v = r (i v) - i r v` of the period filtration (the `-i`-eigenvector of the
complex structure attached to `v`).
Source: Birkenhake–Lange, §1.2 (`Λ ⊗ ℂ = V ⊕ V̄`). -/
def b2a_f (v : Fin (dim X.left) → ℂ) : ℂ ⊗[ℤ] b2_abelianLattice X :=
  b2a_lift X (Complex.I • v) - Complex.I • b2a_lift X v

example (v : Fin (dim X.left) → ℂ) :
    b2a_f X v = b2a_lift X (Complex.I • v) - Complex.I • b2a_lift X v := rfl

theorem b2a_f_zero : b2a_f X 0 = 0 := by
  rw [b2a_f, smul_zero, map_zero, smul_zero, sub_zero]

theorem b2a_eval_f (v : Fin (dim X.left) → ℂ) : b2_abelianEval X (b2a_f X v) = 0 := by
  rw [b2a_f, map_sub, LinearMap.map_smul, b2a_eval_lift, b2a_eval_lift, sub_self]

theorem b2a_f_mem (v : Fin (dim X.left) → ℂ) : b2a_f X v ∈ b2_abelianF X :=
  b2a_eval_f X v

theorem b2a_conj_f (v : Fin (dim X.left) → ℂ) :
    b2_conj _ (b2a_f X v) = b2a_lift X (Complex.I • v) + Complex.I • b2a_lift X v := by
  rw [b2a_f, map_sub, b2v_conj_smul, b2a_conj_lift, b2a_conj_lift, Complex.conj_I, neg_smul,
    sub_neg_eq_add]

theorem b2a_mem_F_iff (u : ℂ ⊗[ℤ] b2_abelianLattice X) :
    u ∈ b2_abelianF X ↔ ∃ v, u = b2a_f X v := by
  refine ⟨fun hu ↦ ?_, ?_⟩
  · obtain ⟨x, y, rfl⟩ := b2a_decomp X u
    have hxy : x + Complex.I • y = 0 := by
      have : b2_abelianEval X (b2a_lift X x + Complex.I • b2a_lift X y) = 0 := hu
      rwa [map_add, LinearMap.map_smul, b2a_eval_lift, b2a_eval_lift] at this
    have hx : x = -(Complex.I • y) := eq_neg_of_add_eq_zero_left hxy
    refine ⟨-y, ?_⟩
    rw [b2a_f, hx, smul_neg, map_neg, map_neg, smul_neg]
    abel
  · rintro ⟨v, rfl⟩
    exact b2a_f_mem X v

theorem b2a_lift_eq_zero {v : Fin (dim X.left) → ℂ} (h : b2a_lift X v = 0) : v = 0 := by
  rw [← b2a_eval_lift X v, h, map_zero]

theorem b2a_f_eq_zero {v : Fin (dim X.left) → ℂ} (h : b2a_f X v = 0) : v = 0 := by
  have h' := b2a_conj_f X v
  rw [h, map_zero] at h'
  have h2 : (2 * Complex.I) • b2a_lift X v = 0 := by
    have : b2a_lift X (Complex.I • v) - Complex.I • b2a_lift X v = 0 := h
    rw [two_mul, add_smul]
    calc Complex.I • b2a_lift X v + Complex.I • b2a_lift X v
        = (b2a_lift X (Complex.I • v) + Complex.I • b2a_lift X v) -
          (b2a_lift X (Complex.I • v) - Complex.I • b2a_lift X v) := by abel
      _ = 0 := by rw [← h', this, sub_zero]
  exact b2a_lift_eq_zero X ((smul_eq_zero.1 h2).resolve_left (by simp))

end Abelian

section Riemann

open HodgeLean.Foundations.AppellHumbert

variable (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

theorem b2a_baseChange_one_tmul (Q : LinearMap.BilinForm ℤ (b2_abelianLattice X))
    (l m : b2_abelianLattice X) :
    Q.baseChange ℂ ((1 : ℂ) ⊗ₜ[ℤ] l) ((1 : ℂ) ⊗ₜ[ℤ] m) = (Q l m : ℂ) := by
  rw [LinearMap.BilinForm.baseChange_tmul, mul_one, zsmul_eq_mul, mul_one]

theorem b2a_f_add (a b : Fin (dim X.left) → ℂ) : b2a_f X (a + b) = b2a_f X a + b2a_f X b := by
  simp only [b2a_f, smul_add, map_add]
  abel

theorem b2a_f_I (a : Fin (dim X.left) → ℂ) :
    b2a_f X (Complex.I • a) = -Complex.I • b2a_f X a := by
  rw [b2a_f, b2a_f, smul_smul, Complex.I_mul_I, neg_one_smul, map_neg, smul_sub, smul_smul,
    neg_mul, Complex.I_mul_I, neg_neg, one_smul, neg_smul]
  abel

theorem b2a_f_real_smul (t : ℝ) (a : Fin (dim X.left) → ℂ) :
    b2a_f X (t • a) = (t : ℂ) • b2a_f X a := by
  simp only [b2a_f, smul_sub, smul_comm Complex.I t a, b2a_lift_real_smul, smul_comm Complex.I
    (t : ℂ)]

theorem b2a_f_smul (c : ℂ) (a : Fin (dim X.left) → ℂ) :
    b2a_f X (c • a) = starRingEnd ℂ c • b2a_f X a := by
  have hc : c • a = c.re • a + c.im • (Complex.I • a) := by
    rw [← Complex.coe_smul, ← Complex.coe_smul, smul_smul, ← add_smul, Complex.re_add_im]
  rw [hc, b2a_f_add, b2a_f_real_smul, b2a_f_real_smul, b2a_f_I, smul_smul, ← add_smul]
  congr 1
  apply Complex.ext <;> simp

theorem b2a_conj_f_smul (c : ℂ) (a : Fin (dim X.left) → ℂ) :
    b2_conj _ (b2a_f X (c • a)) = c • b2_conj _ (b2a_f X a) := by
  rw [b2a_f_smul, b2v_conj_smul, Complex.conj_conj]

theorem b2a_conj_f_add (a b : Fin (dim X.left) → ℂ) :
    b2_conj _ (b2a_f X (a + b)) = b2_conj _ (b2a_f X a) + b2_conj _ (b2a_f X b) := by
  rw [b2a_f_add, map_add]

/-- The real lift in terms of `f` and its conjugate: `r v = (i / 2) (f v - conj (f v))`. -/
theorem b2a_lift_eq_f (v : Fin (dim X.left) → ℂ) :
    b2a_lift X v = (Complex.I / 2) • (b2a_f X v - b2_conj _ (b2a_f X v)) := by
  rw [b2a_conj_f, b2a_f]
  have : b2a_lift X (Complex.I • v) - Complex.I • b2a_lift X v -
      (b2a_lift X (Complex.I • v) + Complex.I • b2a_lift X v) =
      (-2 * Complex.I) • b2a_lift X v := by
    rw [neg_mul, neg_smul, two_mul, add_smul]
    abel
  rw [this, smul_smul]
  have h2 : Complex.I / 2 * (-2 * Complex.I) = 1 := by
    field_simp
    linear_combination -Complex.I_sq
  rw [h2, one_smul]

/-- **The Hermitian form of a Riemann form**: `H(v, w) = (-i / 2) Q_ℂ(conj (f w), f v)`, which is
`Q_ℝ(v, i w) + i Q_ℝ(v, w)` when `F` is isotropic.
Source: Birkenhake–Lange, §2.1 (Hermitian and alternating forms, `E = Im H`) and §4.2. -/
def b2a_hermitian (Q : LinearMap.BilinForm ℤ (b2_abelianLattice X)) (hQ : ∀ x, Q x x = 0) :
    HermitianForm (V := Fin (dim X.left) → ℂ) where
  toFun v w := (-Complex.I / 2) * Q.baseChange ℂ (b2_conj _ (b2a_f X w)) (b2a_f X v)
  add_left x y z := by rw [b2a_f_add, map_add, mul_add]
  smul_left c x y := by
    rw [b2a_f_smul, map_smul, smul_eq_mul]
    simp only [Complex.star_def]
    ring
  add_right x y z := by rw [b2a_conj_f_add, map_add, LinearMap.add_apply, mul_add]
  smul_right c x y := by
    rw [b2a_conj_f_smul, map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  conj_symm x y := by
    rw [Complex.star_def, map_mul, ← b2a_baseChange_conj, b2v_conj_conj,
      b2a_baseChange_antisymm Q hQ]
    simp only [map_div₀, map_neg, Complex.conj_I, map_ofNat]
    ring

theorem b2a_hermitian_apply (Q : LinearMap.BilinForm ℤ (b2_abelianLattice X))
    (hQ : ∀ x, Q x x = 0) (v w : Fin (dim X.left) → ℂ) :
    (b2a_hermitian X Q hQ).toFun v w =
      (-Complex.I / 2) * Q.baseChange ℂ (b2_conj _ (b2a_f X w)) (b2a_f X v) := rfl

example (Q : LinearMap.BilinForm ℤ (b2_abelianLattice X)) (hQ : ∀ x, Q x x = 0) :
    (b2a_hermitian X Q hQ).toFun 0 0 = 0 := by
  simp [b2a_hermitian_apply, b2a_f_zero]

theorem b2a_hermitian_pos (Q : LinearMap.BilinForm ℤ (b2_abelianLattice X))
    (hQ : b2_IsRiemannForm (b2_abelianLattice X) (b2_abelianF X) Q) :
    (b2a_hermitian X Q hQ.alt).IsPositiveDefinite := by
  intro v hv
  have hp := hQ.positive (b2a_f X v) (b2a_f_mem X v) (fun h ↦ hv (b2a_f_eq_zero X h))
  rw [b2a_hermitian_apply, b2a_baseChange_antisymm Q hQ.alt (b2_conj _ _) (b2a_f X v)]
  have : (-Complex.I / 2) * -Q.baseChange ℂ (b2a_f X v) (b2_conj _ (b2a_f X v)) =
      ((1 / 2 : ℝ) : ℂ) * (Complex.I * Q.baseChange ℂ (b2a_f X v) (b2_conj _ (b2a_f X v))) := by
    push_cast
    ring
  rw [this, Complex.re_ofReal_mul]
  exact mul_pos (by norm_num) hp

theorem b2a_hermitian_im (Q : LinearMap.BilinForm ℤ (b2_abelianLattice X))
    (hQ : b2_IsRiemannForm (b2_abelianLattice X) (b2_abelianF X) Q)
    (l m : b2_abelianLattice X) :
    (Q l m : ℝ) = (b2a_hermitian X Q hQ.alt).imaginary l m := by
  set H := b2a_hermitian X Q hQ.alt
  have e1 : (Q l m : ℂ) = Q.baseChange ℂ (b2a_lift X l) (b2a_lift X m) := by
    rw [b2a_lift_coe, b2a_lift_coe, b2a_baseChange_one_tmul]
  rw [b2a_lift_eq_f X (l : Fin (dim X.left) → ℂ), b2a_lift_eq_f X (m : Fin (dim X.left) → ℂ)]
    at e1
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul] at e1
  have hA : Q.baseChange ℂ (b2a_f X l) (b2a_f X m) = 0 :=
    hQ.isotropic _ (b2a_f_mem X _) _ (b2a_f_mem X _)
  have hD : Q.baseChange ℂ (b2_conj _ (b2a_f X l)) (b2_conj _ (b2a_f X m)) = 0 := by
    rw [b2a_baseChange_conj, hA, map_zero]
  have hB := b2a_baseChange_antisymm Q hQ.alt (b2a_f X l) (b2_conj _ (b2a_f X m))
  have hz : H.toFun l m = (-Complex.I / 2) *
      Q.baseChange ℂ (b2_conj _ (b2a_f X m)) (b2a_f X l) := rfl
  have hz' : starRingEnd ℂ (H.toFun l m) = (-Complex.I / 2) *
      Q.baseChange ℂ (b2_conj _ (b2a_f X l)) (b2a_f X m) := by
    rw [← Complex.star_def, H.conj_symm]
    rfl
  apply Complex.ofReal_injective
  rw [HermitianForm.imaginary, Complex.im_eq_sub_conj, hz', hz]
  push_cast
  rw [e1, hA, hD, hB]
  field_simp
  linear_combination (Q.baseChange ℂ (b2_conj _ (b2a_f X m)) (b2a_f X l) -
    Q.baseChange ℂ (b2_conj _ (b2a_f X l)) (b2a_f X m)) * Complex.I_sq

theorem b2a_lift_im (Q : LinearMap.BilinForm ℤ (b2_abelianLattice X))
    (H : HermitianForm (V := Fin (dim X.left) → ℂ))
    (hE : ∀ l m : b2_abelianLattice X, (Q l m : ℝ) = H.imaginary l m)
    (a b : Fin (dim X.left) → ℂ) :
    Q.baseChange ℂ (b2a_lift X a) (b2a_lift X b) = (H.imaginary a b : ℂ) := by
  let L₁ : (Fin (dim X.left) → ℂ) →ₗ[ℝ] (Fin (dim X.left) → ℂ) →ₗ[ℝ] ℂ :=
    LinearMap.mk₂ ℝ (fun a b ↦ Q.baseChange ℂ (b2a_lift X a) (b2a_lift X b))
      (fun x y z ↦ by rw [map_add, map_add, LinearMap.add_apply])
      (fun t x y ↦ by
        rw [b2a_lift_real_smul, map_smul, LinearMap.smul_apply, Complex.coe_smul])
      (fun x y z ↦ by rw [map_add, map_add])
      (fun t x y ↦ by rw [b2a_lift_real_smul, map_smul, Complex.coe_smul])
  let L₂ : (Fin (dim X.left) → ℂ) →ₗ[ℝ] (Fin (dim X.left) → ℂ) →ₗ[ℝ] ℂ :=
    LinearMap.mk₂ ℝ (fun a b ↦ ((H.imaginary a b : ℝ) : ℂ))
      (fun x y z ↦ by
        change ((H.toFun (x + y) z).im : ℂ) = ((H.toFun x z).im : ℂ) + ((H.toFun y z).im : ℂ)
        rw [H.add_left, Complex.add_im, Complex.ofReal_add])
      (fun t x y ↦ by
        change ((H.toFun (t • x) y).im : ℂ) = t • ((H.toFun x y).im : ℂ)
        rw [hermitian_real_smul_left, Complex.im_ofReal_mul, Complex.ofReal_mul,
          Complex.real_smul])
      (fun x y z ↦ by
        change ((H.toFun x (y + z)).im : ℂ) = ((H.toFun x y).im : ℂ) + ((H.toFun x z).im : ℂ)
        rw [H.add_right, Complex.add_im, Complex.ofReal_add])
      (fun t x y ↦ by
        change ((H.toFun x (t • y)).im : ℂ) = t • ((H.toFun x y).im : ℂ)
        rw [hermitian_real_smul_right, Complex.im_ofReal_mul, Complex.ofReal_mul,
          Complex.real_smul])
  have hL : L₁ = L₂ := LinearMap.ext_basis (b2a_basisR X) (b2a_basisR X) fun i j ↦ by
    change Q.baseChange ℂ (b2a_lift X (b2a_basisR X i)) (b2a_lift X (b2a_basisR X j)) =
      ((H.imaginary (b2a_basisR X i) (b2a_basisR X j) : ℝ) : ℂ)
    rw [b2a_basisR_apply, b2a_basisR_apply, b2a_lift_coe, b2a_lift_coe, b2a_baseChange_one_tmul,
      ← hE]
    norm_cast
  exact LinearMap.congr_fun₂ hL a b

theorem b2a_isRiemannForm_of_hermitian (Q : LinearMap.BilinForm ℤ (b2_abelianLattice X))
    (H : HermitianForm (V := Fin (dim X.left) → ℂ)) (hH : H.IsPositiveDefinite)
    (hE : ∀ l m : b2_abelianLattice X, (Q l m : ℝ) = H.imaginary l m) :
    b2_IsRiemannForm (b2_abelianLattice X) (b2_abelianF X) Q := by
  have hIl : ∀ a b, H.toFun (Complex.I • a) b = -Complex.I * H.toFun a b := fun a b ↦ by
    rw [H.smul_left, Complex.star_def, Complex.conj_I]
  have hIr : ∀ a b, H.toFun a (Complex.I • b) = Complex.I * H.toFun a b := fun a b ↦
    H.smul_right _ a b
  refine ⟨fun x ↦ latticeClassHQ_form_self (abelianPeriodLattice X) H (b2_bilinToAddHom Q) hE x,
    ?_, ?_⟩
  · intro x hx y hy
    obtain ⟨a, rfl⟩ := (b2a_mem_F_iff X x).1 hx
    obtain ⟨b, rfl⟩ := (b2a_mem_F_iff X y).1 hy
    simp only [b2a_f, map_sub, LinearMap.map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      smul_eq_mul, b2a_lift_im X Q H hE, HermitianForm.imaginary, hIl, hIr]
    apply Complex.ext <;> simp
  · intro x hx hx0
    obtain ⟨a, rfl⟩ := (b2a_mem_F_iff X x).1 hx
    have ha : a ≠ 0 := by
      rintro rfl
      exact hx0 (by rw [b2a_f, smul_zero, map_zero, smul_zero, sub_zero])
    have hpos := hH a ha
    have hre : (H.toFun a a).im = 0 := by
      have := H.conj_symm a a
      rw [Complex.star_def] at this
      exact Complex.conj_eq_iff_im.1 this
    rw [b2a_conj_f]
    simp only [b2a_f, map_sub, map_add, LinearMap.map_smul, LinearMap.sub_apply,
      LinearMap.smul_apply, smul_eq_mul, b2a_lift_im X Q H hE,
      HermitianForm.imaginary, hIl, hIr]
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.sub_re,
      Complex.add_re, Complex.sub_im, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.neg_re, Complex.neg_im, hre]
    nlinarith

end Riemann

section Contract

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- Contraction commutes with linear maps: `contract (⋀²e ω) φ = e (contract ω (φ ∘ e))`. -/
theorem b2a_contract_map (e : V →ₗ[K] W) (ω : ⋀[K]^2 V) (φ : Module.Dual K W) :
    Symplectic.contract (exteriorPower.map 2 e ω) φ = e (Symplectic.contract ω (φ ∘ₗ e)) := by
  have hω : ω ∈ Submodule.span K (Set.range (exteriorPower.ιMulti K 2 (M := V))) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hω using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    rw [exteriorPower.map_apply_ιMulti, Symplectic.contract_ιMulti, Symplectic.contract_ιMulti]
    simp
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, LinearMap.add_apply, hx, hy, map_add,
      LinearMap.add_apply, map_add]
  | smul c x _ hx => rw [map_smul, map_smul, LinearMap.smul_apply, hx, map_smul,
      LinearMap.smul_apply, map_smul]

/-- The exterior square of a linear equivalence preserves nondegenerate 2-vectors. -/
theorem b2a_isNondegenerate_map (e : V ≃ₗ[K] W) {ω : ⋀[K]^2 V}
    (hω : Symplectic.IsNondegenerate ω) :
    Symplectic.IsNondegenerate (exteriorPower.map 2 e.toLinearMap ω) := by
  have h : (Symplectic.contract (exteriorPower.map 2 e.toLinearMap ω) : Module.Dual K W → W) =
      e ∘ Symplectic.contract ω ∘ e.dualMap := by
    funext φ
    rw [b2a_contract_map]
    rfl
  rw [Symplectic.IsNondegenerate, h]
  exact e.bijective.comp (hω.comp e.dualMap.bijective)

end Contract

end HodgeLean.Foundations.Program
