import HodgeLean.Foundations.MatrixAlgGroupLieElem

/-! # Matrix algebraic groups: the bracket on the tangent space at `1`

Left-invariant derivations `D_X` of `k[x_ij]` (with `D_X x = x X`) commute with left
translations, so for a set `S` stable under products, `D_X` preserves the vanishing ideal of `S`
whenever `X` is tangent to `S` at `1`. Since `⁅D_X, D_Y⁆ = D_{XY - YX}` and `D_Z` evaluated at
`1` is the differential along `Z`, the tangent space at `1` is stable under `XY - YX`.
-/

noncomputable section

namespace HodgeLean.Foundations

open MvPolynomial HodgeLean.Foundations.Program

variable {k : Type*} [Field k] {n : ℕ}

/-- Polynomials in the matrix entries. -/
local notation "𝓟" => MvPolynomial (Fin n × Fin n) k
/-- Matrices of polynomials in the matrix entries. -/
local notation "𝓜" => Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) k)

/-- The left-invariant derivation of `k[x_ij]` attached to a matrix `X`: it sends the coordinate
matrix `x` to `x X`, so `D_X f = Σ_ij (x X)_ij ∂f/∂x_ij`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §3.4 and §3.9 (left-invariant derivations of
`k[GL_n]`); Humphreys, *Linear Algebraic Groups*, §9.1 and §9.2. -/
def g1_leftDer (X : Matrix (Fin n) (Fin n) k) : Derivation k 𝓟 𝓟 :=
  mkDerivation k fun ij ↦ (g1_varMatrix k n * X.map C : 𝓜) ij.1 ij.2

example (X : Matrix (Fin n) (Fin n) k) (c : k) : g1_leftDer X (C c) = 0 :=
  MvPolynomial.derivation_C _ c

/-- The left-invariant derivation on a coordinate. -/
theorem g1_leftDer_X (X : Matrix (Fin n) (Fin n) k) (ij : Fin n × Fin n) :
    g1_leftDer X (MvPolynomial.X ij) = (g1_varMatrix k n * X.map C : 𝓜) ij.1 ij.2 :=
  mkDerivation_X k _ ij

/-- A derivation on the entries of `A c` for a constant matrix `c`. -/
theorem g1_der_mul_const (D : Derivation k 𝓟 𝓟)
    (A : 𝓜) (c : Matrix (Fin n) (Fin n) k) (i j : Fin n) :
    D ((A * c.map C : 𝓜) i j) = (A.map D * c.map C : 𝓜) i j := by
  simp [Matrix.mul_apply, Derivation.leibniz, MvPolynomial.derivation_C, mul_comm]

/-- A derivation on the entries of `c A` for a constant matrix `c`. -/
theorem g1_der_const_mul (D : Derivation k 𝓟 𝓟)
    (A : 𝓜) (c : Matrix (Fin n) (Fin n) k) (i j : Fin n) :
    D ((c.map C * A : 𝓜) i j) = (c.map C * A.map D : 𝓜) i j := by
  simp [Matrix.mul_apply, Derivation.leibniz, MvPolynomial.derivation_C, mul_comm]

/-- The left-invariant derivation sends the coordinate matrix `x` to `x X`. -/
theorem g1_leftDer_map_varMatrix (X : Matrix (Fin n) (Fin n) k) :
    (g1_varMatrix k n).map (g1_leftDer X) = (g1_varMatrix k n * X.map C : 𝓜) := by
  ext i j
  simp [g1_varMatrix, g1_leftDer_X]

/-- The commutator of left-invariant derivations is the derivation of the commutator. -/
theorem g1_leftDer_bracket (X Y : Matrix (Fin n) (Fin n) k) :
    ⁅g1_leftDer X, g1_leftDer Y⁆ = g1_leftDer (X * Y - Y * X) := by
  apply MvPolynomial.derivation_ext
  rintro ⟨i, j⟩
  rw [Derivation.commutator_apply, g1_leftDer_X, g1_leftDer_X, g1_leftDer_X, g1_der_mul_const,
    g1_der_mul_const, g1_leftDer_map_varMatrix, g1_leftDer_map_varMatrix, ← Matrix.sub_apply,
    Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_sub, Matrix.map_sub, Matrix.map_mul,
    Matrix.map_mul]
  exact fun a b ↦ map_sub C a b

/-- A finite sum of derivations, applied to a polynomial. -/
theorem g1_der_sum_apply {ι : Type*} (t : Finset ι) (F : ι → Derivation k 𝓟 𝓟) (f : 𝓟) :
    (∑ i ∈ t, F i) f = ∑ i ∈ t, F i f := by
  rw [← Derivation.coeFnAddMonoidHom_apply, map_sum, Finset.sum_apply]
  rfl

/-- At `1`, the left-invariant derivation is the differential. -/
theorem g1_eval_leftDer (X : Matrix (Fin n) (Fin n) k) (f : 𝓟) :
    eval (g1_coords (1 : Matrix.GeneralLinearGroup (Fin n) k)) (g1_leftDer X f) =
      g1_differential f X := by
  have hD : g1_leftDer X = ∑ ij : Fin n × Fin n,
      (g1_varMatrix k n * X.map C : 𝓜) ij.1 ij.2 • pderiv ij := by
    apply MvPolynomial.derivation_ext
    intro ij
    rw [g1_leftDer_X, g1_der_sum_apply]
    simp [pderiv_X, Pi.single_apply]
  rw [hD, g1_der_sum_apply, map_sum, g1_differential_apply]
  refine Finset.sum_congr rfl fun ij _ ↦ ?_
  rw [Derivation.smul_apply, smul_eq_mul, map_mul, mul_comm]
  congr 1
  have h := congrArg (fun M : Matrix (Fin n) (Fin n) k ↦ M ij.1 ij.2)
    (show (eval (g1_coords (1 : Matrix.GeneralLinearGroup (Fin n) k))).mapMatrix
      (g1_varMatrix k n * X.map C) = X by
      rw [map_mul, g1_mapMatrix_eval_varMatrix]
      ext a b
      simp)
  exact h

/-- Left translation sends the coordinate matrix `x` to `g x`. -/
theorem g1_leftTranslate_map_varMatrix (g : Matrix.GeneralLinearGroup (Fin n) k) :
    (g1_varMatrix k n).map (g1_leftTranslate g) =
      ((g : Matrix (Fin n) (Fin n) k).map C * g1_varMatrix k n : 𝓜) := by
  ext i j
  simp [g1_varMatrix, g1_leftTranslate]

/-- An algebra map on the entries of `A c` for a constant matrix `c`. -/
theorem g1_algHom_mul_const (φ : 𝓟 →ₐ[k] 𝓟)
    (A : 𝓜) (c : Matrix (Fin n) (Fin n) k) (i j : Fin n) :
    φ ((A * c.map C : 𝓜) i j) = (A.map φ * c.map C : 𝓜) i j := by
  simp only [Matrix.mul_apply, map_sum, map_mul, Matrix.map_apply]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  congr 1
  exact φ.commutes (c l j)

/-- Left-invariant derivations commute with left translations. -/
theorem g1_leftDer_leftTranslate (X : Matrix (Fin n) (Fin n) k)
    (g : Matrix.GeneralLinearGroup (Fin n) k) (f : 𝓟) :
    g1_leftDer X (g1_leftTranslate g f) = g1_leftTranslate g (g1_leftDer X f) := by
  have key : ∀ ij : Fin n × Fin n, g1_leftDer X (g1_leftTranslate g (MvPolynomial.X ij)) =
      g1_leftTranslate g (g1_leftDer X (MvPolynomial.X ij)) := by
    rintro ⟨i, j⟩
    have h1 : g1_leftTranslate g (MvPolynomial.X (i, j)) =
        ((g : Matrix (Fin n) (Fin n) k).map C * g1_varMatrix k n : 𝓜) i j := by
      simp [g1_leftTranslate]
    rw [h1, g1_der_const_mul, g1_leftDer_map_varMatrix, g1_leftDer_X, g1_algHom_mul_const,
      g1_leftTranslate_map_varMatrix, Matrix.mul_assoc]
  induction f using MvPolynomial.induction_on with
  | C a =>
    rw [show g1_leftTranslate g (C a) = C a from (g1_leftTranslate g).commutes a,
      MvPolynomial.derivation_C, map_zero]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p ij hp =>
    rw [map_mul, Derivation.leibniz, Derivation.leibniz, map_add, smul_eq_mul, smul_eq_mul,
      smul_eq_mul, smul_eq_mul, map_mul, map_mul, hp, key]

/-- For a set stable under products, `D_X` preserves the vanishing ideal when `X` is tangent. -/
theorem g1_leftDer_mem (S : Set (Matrix.GeneralLinearGroup (Fin n) k))
    (hS : ∀ g ∈ S, ∀ h ∈ S, g * h ∈ S) (X : Matrix (Fin n) (Fin n) k)
    (hX : X ∈ g1_lieOfSet S) {f : 𝓟} (hf : f ∈ g1_vanishingIdealSet S) :
    g1_leftDer X f ∈ g1_vanishingIdealSet S := by
  simp only [g1_lieOfSet, Submodule.mem_iInf, LinearMap.mem_ker] at hX
  refine mem_vanishingIdeal_iff.mpr ?_
  rintro _ ⟨g, hg, rfl⟩
  change eval (g1_coords g) _ = 0
  have htr : g1_leftTranslate g f ∈ g1_vanishingIdealSet S := by
    refine mem_vanishingIdeal_iff.mpr ?_
    rintro _ ⟨h, hh, rfl⟩
    change eval (g1_coords h) _ = 0
    rw [g1_eval_leftTranslate]
    exact (mem_vanishingIdeal_iff.mp hf) _ ⟨g * h, hS g hg h hh, rfl⟩
  have := hX _ htr
  rw [← g1_eval_leftDer, g1_leftDer_leftTranslate, g1_eval_leftTranslate, mul_one] at this
  exact this

/-- For a set stable under products, the tangent space at `1` is stable under brackets. -/
theorem g1_lieOfSet_bracket_mem (S : Set (Matrix.GeneralLinearGroup (Fin n) k))
    (hS : ∀ g ∈ S, ∀ h ∈ S, g * h ∈ S) (X Y : Matrix (Fin n) (Fin n) k)
    (hX : X ∈ g1_lieOfSet S) (hY : Y ∈ g1_lieOfSet S) : X * Y - Y * X ∈ g1_lieOfSet S := by
  have hX' := hX
  have hY' := hY
  simp only [g1_lieOfSet, Submodule.mem_iInf, LinearMap.mem_ker] at hX hY ⊢
  intro f hf
  rw [← g1_eval_leftDer, ← g1_leftDer_bracket, Derivation.commutator_apply, map_sub,
    g1_eval_leftDer, g1_eval_leftDer, hX _ (g1_leftDer_mem S hS Y hY' hf),
    hY _ (g1_leftDer_mem S hS X hX' hf), sub_self]

end HodgeLean.Foundations
