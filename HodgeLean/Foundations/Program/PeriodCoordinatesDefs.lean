import HodgeLean.Foundations.Program.UniversalFamilyB60cFiltration

/-! # B6-4a: graph coordinates of the fixed bounded chart (definitions)

Explicit coordinates for filtrations of the fixed complexified Weil lattice
`ℂ ⊗ ℤ[ω]⁶` of B6-0a, in the normalized eigenbasis `b60c_eigenBasis`. A three-frame in
the `-i√3` eigenspace has a head block (the first three eigen-coordinates) and a tail
block (the last three); when the head block is invertible, the frame spans the graph of
`tail · head⁻¹`. The coordinate of a filtration is the matrix entry of the explicit
graph chart `b60_F`, read off when the filtration lies in that chart and `0` otherwise.
No family, marking or geometric input is introduced. HC no distance; AV milestone no
distance.
-/

noncomputable section
open scoped TensorProduct Matrix
open HodgeLean.Papers
namespace HodgeLean.Foundations.Program

/-- **The negative eigenspace** of the complexified quadratic action, eigenvalue `-i√3`.
It contains the negative half `b60c_eigenBasis (0, ·)` of the normalized eigenbasis.
Source: van Geemen, LNM 1594, §5.1; `b60c_omega_eigenBasis`. -/
def b64_Eminus : Submodule ℂ (ℂ ⊗[ℤ] b60_Lattice) :=
  Module.End.eigenspace b60_omegaC (-Complex.I * (Real.sqrt 3 : ℂ))

example (i : Fin 6) : b60c_eigenBasis (0, i) ∈ b64_Eminus := by
  rw [b64_Eminus, Module.End.mem_eigenspace_iff, b60c_omega_eigenBasis]
  simp

/-- **The negative graph frame** at a matrix point: the three vectors
`e⁻ⱼ + ∑ₖ Zₖⱼ e⁻₃₊ₖ` of `b60_frame z (0, ·)`.
Source: van Geemen, LNM 1594, §5.10; `b60_frame`. -/
def b64_negFrame (z : Fin 9 → ℂ) (j : Fin 3) : ℂ ⊗[ℤ] b60_Lattice :=
  b60_frame z (0, j)

example (z : Fin 9 → ℂ) (j : Fin 3) : b64_negFrame z j =
    b60_eigen (-1) (Fin.castAdd 3 j) +
      ∑ k : Fin 3, g32m_toMat z k j • b60_eigen (-1) (Fin.natAdd 3 k) := by
  simp [b64_negFrame, b60_frame]

/-- The eigen-coordinates of the negative graph frame: `1` at its own head slot and the
matrix entries `Zₖⱼ` at the tail slots. A direct computation, used by the instance checks.
Source: `b60_frame`, `b60c_eigenBasis_apply`, Mathlib `Module.Basis.repr_self`. -/
theorem b64_negFrame_repr (z : Fin 9 → ℂ) (j : Fin 3) (p : Fin 2 × Fin 6) :
    b60c_eigenBasis.repr (b64_negFrame z j) p =
      (if (0, Fin.castAdd 3 j) = p then 1 else 0) +
        ∑ k : Fin 3, g32m_toMat z k j * (if (0, Fin.natAdd 3 k) = p then 1 else 0) := by
  have h : b64_negFrame z j = b60c_eigenBasis (0, Fin.castAdd 3 j) +
      ∑ k : Fin 3, g32m_toMat z k j • b60c_eigenBasis (0, Fin.natAdd 3 k) := by
    simp [b64_negFrame, b60_frame, b60c_eigenBasis_apply]
  rw [h]
  simp only [map_add, map_sum, map_smul, Module.Basis.repr_self, Finsupp.add_apply,
    Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, Finsupp.single_apply,
    smul_eq_mul]

example (z : Fin 9 → ℂ) (k : Fin 6) :
    b60c_eigenBasis.repr (b64_negFrame z 0) ((1 : Fin 2), k) =
      (if ((0 : Fin 2), Fin.castAdd 3 (0 : Fin 3)) = ((1 : Fin 2), k) then 1 else 0) +
        ∑ k' : Fin 3, g32m_toMat z k' 0 *
          (if ((0 : Fin 2), Fin.natAdd 3 k') = ((1 : Fin 2), k) then 1 else 0) :=
  b64_negFrame_repr z 0 ((1 : Fin 2), k)

/-- **The head block** of a three-frame: entry `(i, j)` is the eigen-coordinate
`(0, i)` of the vector `v j`.
Source: Mathlib `Module.Basis.repr`; `b60c_eigenBasis`. -/
def b64_headBlock (v : Fin 3 → ℂ ⊗[ℤ] b60_Lattice) : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.of fun i j => b60c_eigenBasis.repr (v j) (0, Fin.castAdd 3 i)

example : b64_headBlock 0 = 0 := by
  ext i j
  simp [b64_headBlock]

/-- **The tail block** of a three-frame: entry `(k, j)` is the eigen-coordinate
`(0, 3 + k)` of the vector `v j`.
Source: Mathlib `Module.Basis.repr`; `b60c_eigenBasis`. -/
def b64_tailBlock (v : Fin 3 → ℂ ⊗[ℤ] b60_Lattice) : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.of fun k j => b60c_eigenBasis.repr (v j) (0, Fin.natAdd 3 k)

example : b64_tailBlock 0 = 0 := by
  ext i j
  simp [b64_tailBlock]

/-- **The graph coordinate of a three-frame**: the nine entries of `tail · head⁻¹`, in
the coordinate convention `g32m_toMat` of the period domain. Mathlib's matrix inverse is
zero on singular matrices, so the function is total; it is meaningful when the head
block is invertible.
Source: the graph chart of the Grassmannian, Griffiths–Harris, *Principles of
Algebraic Geometry*, Ch. 1, §5; `b60c_matrixCoordinates`. -/
def b64_graphCoord (v : Fin 3 → ℂ ⊗[ℤ] b60_Lattice) : Fin 9 → ℂ :=
  b60c_matrixCoordinates (b64_tailBlock v * (b64_headBlock v)⁻¹)

example (v : Fin 3 → ℂ ⊗[ℤ] b60_Lattice) :
    g32m_toMat (b64_graphCoord v) = b64_tailBlock v * (b64_headBlock v)⁻¹ :=
  b60c_toMat_matrixCoordinates _

/-- **The negative part** of a vector: its component along the negative half of the
normalized eigenbasis.
Source: Mathlib `Module.Basis.repr`; `b60c_eigenBasis`. -/
def b64_negPart (x : ℂ ⊗[ℤ] b60_Lattice) : ℂ ⊗[ℤ] b60_Lattice :=
  ∑ i : Fin 6, b60c_eigenBasis.repr x (0, i) • b60c_eigenBasis (0, i)

example : b64_negPart 0 = 0 := by
  simp [b64_negPart]

open Classical in
/-- **The period coordinate of a filtration**: a matrix point `z` with `F = b60_F z`
when one exists, and `0` otherwise. The frozen statement `b64_coordOf_eq` identifies
the value on the chart.
Source: van Geemen, LNM 1594, §5.10; G32 v0.16, §2.1; `b60_F`. -/
def b64_coordOf (F : Submodule ℂ (ℂ ⊗[ℤ] b60_Lattice)) : Fin 9 → ℂ :=
  if h : ∃ z : Fin 9 → ℂ, F = b60_F z then h.choose else 0

/-- On the chart, the chosen coordinate reproduces the filtration. -/
example (z : Fin 9 → ℂ) : b60_F (b64_coordOf (b60_F z)) = b60_F z := by
  have h : ∃ w : Fin 9 → ℂ, b60_F z = b60_F w := ⟨z, rfl⟩
  unfold b64_coordOf
  split_ifs with h'
  · exact h'.choose_spec.symm
  · exact absurd h h'

end HodgeLean.Foundations.Program
