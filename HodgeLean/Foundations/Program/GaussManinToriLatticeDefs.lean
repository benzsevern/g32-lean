module

public import Mathlib

/-!
# Period matrices, their lattices and `H^{1,0}`: definitions (Mathlib only)

The elementary linear algebra of Track D2, stated with Mathlib alone. A `g × 2g` complex matrix
`P` is a period matrix when its `2g` columns are `ℝ`-linearly independent in `ℂ^g`; its columns
span the lattice `Λ` (`d2_lattice`), the marking `ℤ^{2g} → Λ` sends the `k`-th basis vector to the
`k`-th column, and `F¹ = H^{1,0}` of the torus `ℂ^g / Λ` is the row space of `P` inside
`ℂ ⊗ ℚ^{2g}` (`d2_hodgeOne`). A Riemann form is an integral alternating matrix on the marked
lattice whose real extension is invariant under the complex structure and positive in the
repository's convention, and the polarization of `H¹` is the dual form `(A^{-1})ᵀ`.

The weight-one variation built from marked period data is in `GaussManinToriDefs.lean`.

HC no distance; AV milestone no distance.
-/

@[expose] public noncomputable section

open scoped TensorProduct Matrix

namespace HodgeLean.Foundations.Program

section PeriodMatrix

variable {g : ℕ}

/-- The `k`-th column of a `g × 2g` matrix, the image in `ℂ^g` of the `k`-th marked generator of
the lattice.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §1.1 (period matrices). -/
def d2_column (P : Fin g → Fin (2 * g) → ℂ) (k : Fin (2 * g)) : Fin g → ℂ :=
  fun i ↦ P i k

example (P : Fin g → Fin (2 * g) → ℂ) (i : Fin g) (k : Fin (2 * g)) :
    d2_column P k i = P i k := rfl

/-- A period matrix: the `2g` columns are linearly independent over `ℝ`, hence an `ℝ`-basis of
`ℂ^g`, so their `ℤ`-span is a lattice.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §1.1. -/
def d2_IsPeriodMatrix (P : Fin g → Fin (2 * g) → ℂ) : Prop :=
  LinearIndependent ℝ (d2_column P)

example (P : Fin 0 → Fin (2 * 0) → ℂ) : d2_IsPeriodMatrix P :=
  haveI : IsEmpty (Fin (2 * 0)) := ⟨fun k ↦ Fin.elim0 k⟩
  linearIndependent_empty_type

/-- The lattice `Λ` spanned over `ℤ` by the columns of `P`; the fibre torus is `ℂ^g / Λ`.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §1.1. -/
def d2_lattice (P : Fin g → Fin (2 * g) → ℂ) : Submodule ℤ (Fin g → ℂ) :=
  Submodule.span ℤ (Set.range (d2_column P))

example (P : Fin g → Fin (2 * g) → ℂ) (k : Fin (2 * g)) : d2_column P k ∈ d2_lattice P :=
  Submodule.subset_span ⟨k, rfl⟩

/-- The marking `ℤ^{2g} → Λ`, `n ↦ ∑ n_k P e_k`.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §1.1. -/
def d2_markingMap (P : Fin g → Fin (2 * g) → ℂ) : (Fin (2 * g) → ℤ) →ₗ[ℤ] (Fin g → ℂ) :=
  Fintype.linearCombination ℤ (d2_column P)

example (P : Fin g → Fin (2 * g) → ℂ) (n : Fin (2 * g) → ℤ) :
    d2_markingMap P n = ∑ k, n k • d2_column P k :=
  Fintype.linearCombination_apply ℤ _ n

/-- The real-linear map `ℝ^{2g} → ℂ^g`, `s ↦ ∑ s_k P e_k`, identifying `Λ ⊗ ℝ` with `ℂ^g`.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §1.1. -/
def d2_realMap (P : Fin g → Fin (2 * g) → ℂ) : (Fin (2 * g) → ℝ) →ₗ[ℝ] (Fin g → ℂ) :=
  Fintype.linearCombination ℝ (d2_column P)

example (P : Fin g → Fin (2 * g) → ℂ) (s : Fin (2 * g) → ℝ) :
    d2_realMap P s = ∑ k, s k • d2_column P k :=
  Fintype.linearCombination_apply ℝ _ s

/-- The real extension `E(s, t) = sᵀ A t` of an integral form given by its matrix in the marked
basis of the lattice.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §2.1 (alternating forms on
`Λ`). -/
def d2_riemannReal {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (s t : Fin n → ℝ) : ℝ :=
  s ⬝ᵥ (A.map (Int.cast : ℤ → ℝ) *ᵥ t)

example {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (t : Fin n → ℝ) : d2_riemannReal A 0 t = 0 :=
  zero_dotProduct _

/-- A Riemann form for the period matrix `P`: an integral matrix `A` on the marked lattice,
alternating, whose real extension `E` is invariant under the complex structure of `ℂ^g`
transported to `ℝ^{2g}`, with `E(v, i v) > 0` for `v ≠ 0`. The complex structure enters through
pairs `(s, s')` with `P s' = i · P s`, so no inverse of the real map is taken. This is the
repository's sign convention (`Re H(v, v) = Im H(v, i v)` for `HermitianForm`).
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §4.1 (polarizations) and
Lemma 1.3.1; Griffiths--Harris, *Principles of Algebraic Geometry*, ch. 2, §6 (Riemann
conditions). -/
structure d2_IsRiemannForm (P : Fin g → Fin (2 * g) → ℂ)
    (A : Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) : Prop where
  alternating : Aᵀ = -A
  typeOneOne : ∀ s t s' t' : Fin (2 * g) → ℝ, d2_realMap P s' = Complex.I • d2_realMap P s →
    d2_realMap P t' = Complex.I • d2_realMap P t → d2_riemannReal A s' t' = d2_riemannReal A s t
  positive : ∀ s s' : Fin (2 * g) → ℝ, s ≠ 0 → d2_realMap P s' = Complex.I • d2_realMap P s →
    0 < d2_riemannReal A s s'

example (P : Fin 0 → Fin (2 * 0) → ℂ) : d2_IsRiemannForm P 0 :=
  ⟨by simp, fun _ _ _ _ _ _ ↦ by simp [d2_riemannReal],
    fun _ _ hs ↦ absurd (funext fun k ↦ Fin.elim0 k) hs⟩

/-- The polarization of `H¹ = Hom(Λ, ℚ) = ℚ^{2g}` dual to the Riemann form: the matrix
`(A^{-1})ᵀ`, so that `Q(E(x, ·), E(y, ·)) = E(x, y)`.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §4.1 and §14.1 (the dual
polarization); Griffiths--Harris, ch. 2, §6. -/
def d2_dualForm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : LinearMap.BilinForm ℚ (Fin n → ℚ) :=
  Matrix.toBilin' (A.map (Int.cast : ℤ → ℚ))⁻¹ᵀ

example {n : ℕ} : d2_dualForm (0 : Matrix (Fin n) (Fin n) ℤ) = 0 := by
  simp [d2_dualForm]

end PeriodMatrix

section Hodge

variable {g : ℕ}

/-- The coordinate isomorphism `ℂ^n ≅ ℂ ⊗ ℚ^n`, `c ↦ ∑ c_k ⊗ e_k`.
Source: Bourbaki, *Algèbre*, ch. II, §5 (extension of scalars of a free module);
`Module.Basis.baseChange`. -/
def d2_vec (n : ℕ) : (Fin n → ℂ) ≃ₗ[ℂ] ℂ ⊗[ℚ] (Fin n → ℚ) :=
  ((Pi.basisFun ℚ (Fin n)).baseChange ℂ).equivFun.symm

example (n : ℕ) : d2_vec n 0 = 0 := map_zero _

/-- Restriction of `ℂ`-linear forms to the marked lattice: `(P, φ) ↦ (φ(P e_k))_k ∈ ℂ ⊗ ℚ^{2g}`,
the class in `H¹(ℂ^g/Λ, ℂ)` of the holomorphic `1`-form with constant coefficients `φ`. It is
linear in both the matrix and the form.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §1.4 (`H¹(X, ℂ)` and
`H^{1,0}(X)` of a complex torus). -/
def d2_evalBilin {n : ℕ} :
    (Fin g → Fin n → ℂ) →ₗ[ℂ] Module.Dual ℂ (Fin g → ℂ) →ₗ[ℂ] ℂ ⊗[ℚ] (Fin n → ℚ) :=
  LinearMap.mk₂ ℂ (fun P φ ↦ d2_vec n (fun k ↦ φ (fun i ↦ P i k)))
    (fun P P' φ ↦ by
      rw [← map_add]; congr 1; funext k; rw [Pi.add_apply, ← map_add]; rfl)
    (fun c P φ ↦ by
      rw [← map_smul]; congr 1; funext k; rw [Pi.smul_apply, smul_eq_mul, ← smul_eq_mul,
        ← map_smul]; rfl)
    (fun P φ ψ ↦ by rw [← map_add]; rfl)
    (fun c P φ ↦ by rw [← map_smul]; rfl)

example {n : ℕ} (P : Fin g → Fin n → ℂ) (φ : Module.Dual ℂ (Fin g → ℂ)) :
    d2_evalBilin P φ = d2_vec n (fun k ↦ φ (fun i ↦ P i k)) := rfl

/-- `F¹ = H^{1,0}`: the restrictions of the `ℂ`-linear forms on `ℂ^g` to the lattice, i.e. the
row space of `P` inside `ℂ ⊗ ℚ^{2g}`.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §1.4; Griffiths--Harris,
ch. 2, §6. -/
def d2_hodgeOne (P : Fin g → Fin (2 * g) → ℂ) : Submodule ℂ (ℂ ⊗[ℚ] (Fin (2 * g) → ℚ)) :=
  LinearMap.range (d2_evalBilin P)

example (P : Fin g → Fin (2 * g) → ℂ) (φ : Module.Dual ℂ (Fin g → ℂ)) :
    d2_evalBilin P φ ∈ d2_hodgeOne P :=
  LinearMap.mem_range_self _ φ

end Hodge

section Witnesses

/-- The period matrix `(1, τ)` of the elliptic curve `ℂ / (ℤ + ℤ τ)`.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §1.1 and §8.1 (`Λ = ℤ + τ ℤ`). -/
def d2_ellipticPeriod (τ : ℂ) : Fin 1 → Fin (2 * 1) → ℂ :=
  fun _ k ↦ if (k : ℕ) = 0 then 1 else τ

example (τ : ℂ) : d2_ellipticPeriod τ 0 1 = τ := by simp [d2_ellipticPeriod]

/-- The standard Riemann form `E(λ₁, λ₂) = 1` on `ℤ + ℤ τ`, the matrix `[[0, 1], [-1, 0]]`.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §3.1 and §8.1. -/
def d2_stdRiemann : Matrix (Fin (2 * 1)) (Fin (2 * 1)) ℤ :=
  !![0, 1; -1, 0]

example : d2_stdRiemann 0 1 = 1 := rfl

end Witnesses

end HodgeLean.Foundations.Program
