import HodgeLean.Papers.G32Moduli
import HodgeLean.Foundations.Program.RelativeTorusKernelDefs
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Explicit lattice and graph coordinates for B6-0a

The implication from bounded-domain membership to the Riemann relations uses the integral
order ℤ[√−3]. Here ω means √−3, as in `WeilHermitian`, rather than a cubic root of unity.
No algebraic fibre or Landherr coverage is selected. HC no distance; AV milestone no distance.
-/

noncomputable section
open scoped TensorProduct Matrix ComplexOrder
open HodgeLean.Papers HodgeLean.Foundations.HermitianForm
namespace HodgeLean.Foundations.Program

/-- Coordinates `a + bω` for the lattice ℤ[ω]⁶, ω² = −3.
Source: G32 v0.16, §2.1; van Geemen, LNM 1594, §5.10 (choice of a lattice). -/
abbrev b60_Lattice := (Fin 6 × Fin 2) → ℤ
example : Module.Free ℤ b60_Lattice := inferInstance

/-- Integral diagonal coefficients of the Hermitian form.
Source: `HermitianForm.detClass_diag_F1569` and `hermSignature_diag_F1569`. -/
def b60_diag : Fin 6 → ℤ := ![1, 1, 1, -1, -1, -2]
example : b60_diag 5 = -2 := rfl

/-- The rational Hermitian form, conjugate-linear in its first variable.
Source: `HermitianForm.diagForm`, G32 v0.16, §2.1. -/
def b60_H := diagForm (a := -3) (b := 0) ![1, 1, 1, -1, -1, -2]
example : hermSignature b60_H = (3, 3) := hermSignature_diag_F1569
example : gramDetℚ b60_H (Pi.basisFun _ (Fin 6)) = -2 := by
  rw [b60_H, gramDetℚ_diagForm]
  norm_num [Fin.prod_univ_succ]
example : detClass b60_H (diagForm_isSymm _)
    (diagForm_nondegenerate diag_F1569_ne_zero) =
    ((Units.mk0 (-2 : ℚ) (by norm_num) : ℚˣ) :
      ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0)) := detClass_diag_F1569

/-- Inclusion in the rational Hermitian space in the basis `1, ω`.
Source: G32 v0.16, §2.1; `QuadraticAlgebra`. -/
def b60_rat (x : b60_Lattice) : Fin 6 → QuadraticAlgebra ℚ (-3) 0 :=
  fun i => ⟨x (i, 0), x (i, 1)⟩
example (x : b60_Lattice) (i : Fin 6) : (b60_rat x i).re = x (i, 0) := rfl

/-- Multiplication by ω on the integral lattice.
Source: `WeilHermitian.WithJ`, ω² = −3. -/
def b60_omega : b60_Lattice →ₗ[ℤ] b60_Lattice where
  toFun x := fun p => if p.2 = 0 then -3 * x (p.1, 1) else x (p.1, 0)
  map_add' x y := by ext p; split <;> simp_all [mul_add]
  map_smul' c x := by ext p; split <;> simp_all <;> ring
example (x : b60_Lattice) (i : Fin 6) : b60_omega x (i, 0) = -3 * x (i, 1) := by
  simp [b60_omega]

/-- The integral trace pairing: the ω coefficient of H, hence Tr(H/(2ω)).
Source: G32 v0.16, §2.1; `WeilHermitian.im_weilHermitian`. -/
def b60_E : LinearMap.BilinForm ℤ b60_Lattice where
  toFun x :=
    { toFun := fun y => ∑ i, b60_diag i * (x (i, 0) * y (i, 1) - x (i, 1) * y (i, 0))
      map_add' := by
        intro y z
        simp only [Pi.add_apply]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      map_smul' := by
        intro c y
        change (∑ i, b60_diag i * (x (i, 0) * (c * y (i, 1)) -
          x (i, 1) * (c * y (i, 0)))) = c * _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring }
  map_add' := by
    intro x y
    apply LinearMap.ext
    intro z
    change (∑ i, b60_diag i * ((x (i, 0) + y (i, 0)) * z (i, 1) -
      (x (i, 1) + y (i, 1)) * z (i, 0))) = _ + _
    dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  map_smul' := by
    intro c x
    apply LinearMap.ext
    intro y
    change (∑ i, b60_diag i * ((c * x (i, 0)) * y (i, 1) -
      (c * x (i, 1)) * y (i, 0))) = c * _
    dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

example (x y : b60_Lattice) : b60_E x y =
    ∑ i, b60_diag i * (x (i, 0) * y (i, 1) - x (i, 1) * y (i, 0)) := rfl

/-- Complexified integral basis.
Source: Mathlib `Module.Basis.baseChange`. -/
def b60_basis := (Pi.basisFun ℤ (Fin 6 × Fin 2)).baseChange ℂ
example (p : Fin 6 × Fin 2) : b60_basis p =
    (1 : ℂ) ⊗ₜ[ℤ] (Pi.basisFun ℤ (Fin 6 × Fin 2) p) := by
  exact Module.Basis.baseChange_apply ℂ (Pi.basisFun ℤ (Fin 6 × Fin 2)) p

/-- For `s = ±1`, eigenvectors for ω with eigenvalue `s i √3`, normalized to diagonal signs.
Source: van Geemen, LNM 1594, §§5.7–5.10; diagonal real isometry for G32 §2.1. -/
def b60_eigen (s : ℂ) (i : Fin 6) : ℂ ⊗[ℤ] b60_Lattice :=
  (if i = 5 then ((Real.sqrt 2 : ℂ)⁻¹) else 1) •
    (b60_basis (i, 0) + (s / (Complex.I * (Real.sqrt 3 : ℂ))) • b60_basis (i, 1))
example : b60_eigen 1 0 = b60_basis (0, 0) +
    (1 / (Complex.I * (Real.sqrt 3 : ℂ))) • b60_basis (0, 1) := by
  simp [b60_eigen]

/-- Six holomorphic frame vectors: the negative graph in the + eigenspace and the
positive graph in the − eigenspace. Transpose, without conjugation, enforces isotropy.
Source: van Geemen, LNM 1594, §§5.7–5.10; G32 v0.16, §2.1. -/
def b60_frame (z : Fin 9 → ℂ) : Fin 2 × Fin 3 → ℂ ⊗[ℤ] b60_Lattice := fun p =>
  if p.1 = 0 then
    b60_eigen (-1) (Fin.castAdd 3 p.2) +
      ∑ j : Fin 3, g32m_toMat z j p.2 • b60_eigen (-1) (Fin.natAdd 3 j)
  else
    b60_eigen 1 (Fin.natAdd 3 p.2) +
      ∑ j : Fin 3, g32m_toMat z p.2 j • b60_eigen 1 (Fin.castAdd 3 j)
example : b60_frame 0 (0, 0) = b60_eigen (-1) 0 := by
  simp [b60_frame, g32m_toMat]

/-- The filtration generated by this explicit frame, defined on all matrix coordinates.
Source: van Geemen, LNM 1594, §5.10. -/
def b60_F (z : Fin 9 → ℂ) : Submodule ℂ (ℂ ⊗[ℤ] b60_Lattice) :=
  Submodule.span ℂ (Set.range (b60_frame z))
example (z : Fin 9 → ℂ) (p : Fin 2 × Fin 3) : b60_frame z p ∈ b60_F z :=
  Submodule.subset_span ⟨p, rfl⟩

/-- Complexified ω action.
Source: Mathlib `LinearMap.baseChange`; G32 v0.16, §2.1. -/
def b60_omegaC := b60_omega.baseChange ℂ
example (c : ℂ) (x : b60_Lattice) :
    b60_omegaC (c ⊗ₜ[ℤ] x) = c ⊗ₜ[ℤ] b60_omega x := rfl

/-- Frame coordinates in the fixed complexified integral basis.
Source: Mathlib `Module.Basis.repr`; van Geemen, LNM 1594, §5.10. -/
def b60_frameCoord (z : Fin 9 → ℂ) (p : Fin 2 × Fin 3) (q : Fin 6 × Fin 2) : ℂ :=
  b60_basis.repr (b60_frame z p) q
example (z : Fin 9 → ℂ) (p : Fin 2 × Fin 3) (q : Fin 6 × Fin 2) :
    b60_frameCoord z p q = b60_basis.repr (b60_frame z p) q := rfl

end HodgeLean.Foundations.Program
