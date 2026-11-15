import HodgeLean.Foundations.Program.UniversalFamilyCover

/-! # Hecke spreading S1–S6: definitions

The Cayley map of a sesquilinear Gram matrix; the unitary group of the fixed Weil lattice
`b60_Lattice`, as `12 × 12` matrices commuting with `b60_omega` and preserving `b60_E`, over a
ring with trivial involution (`ℚ` or `ℝ`); its complexified action on `ℂ ⊗ b60_Lattice`; and the
relation "the filtration at `σ` is the image of the filtration at `τ`".
HC no distance; AV milestone no distance.
-/

noncomputable section
open scoped Matrix TensorProduct
open HodgeLean.Papers
namespace HodgeLean.Foundations.Program

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The unitary group of a Gram matrix `H` with respect to the involution of the entries:
`gᴴ H g = H`. No nondegeneracy is imposed.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §23.9 (unitary groups);
G32 v0.16, §2.1 (the group `U(V, H)`). -/
def hk_unitary {K : Type*} [CommRing K] [StarRing K] (H : Matrix n n K) :
    Set (Matrix n n K) :=
  {g | gᴴ * H * g = H}

example {K : Type*} [CommRing K] [StarRing K] (H : Matrix n n K) :
    (1 : Matrix n n K) ∈ hk_unitary H := by
  simp [hk_unitary]

/-- The Lie algebra of `hk_unitary H`: `Xᴴ H + H X = 0`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §3.9 and §23.9. -/
def hk_lie {K : Type*} [CommRing K] [StarRing K] (H : Matrix n n K) :
    Set (Matrix n n K) :=
  {X | Xᴴ * H + H * X = 0}

example {K : Type*} [CommRing K] [StarRing K] (H : Matrix n n K) :
    (0 : Matrix n n K) ∈ hk_lie H := by
  simp [hk_lie]

/-- The Cayley map `X ↦ (1 - X)(1 + X)⁻¹`, with Mathlib's matrix inverse (zero on singular
matrices).
Source: Weyl, *The Classical Groups*, Princeton 1939, Chapter II, §10 (Cayley's
parametrization); plan `G32RemainingPremises.md`, §2.3, stage S1. -/
def hk_cayley {K : Type*} [CommRing K] (X : Matrix n n K) : Matrix n n K :=
  (1 - X) * (1 + X)⁻¹

example {K : Type*} [Field K] : hk_cayley (0 : Matrix n n K) = 1 := by
  simp [hk_cayley]

/-- The index set of the integral coordinates `a + bω` of `b60_Lattice`.
Source: `b60_Lattice`, G32 v0.16, §2.1. -/
abbrev hk_ι := Fin 6 × Fin 2

example : Fintype.card hk_ι = 12 := rfl

/-- The integral matrix of multiplication by `ω` (`ω² = -3`) on `b60_Lattice`.
Source: `b60_omega`; G32 v0.16, §2.1. -/
def hk_Omega : Matrix hk_ι hk_ι ℤ :=
  LinearMap.toMatrix' b60_omega

example : hk_Omega (0, 0) (0, 1) = -3 := by
  simp [hk_Omega, LinearMap.toMatrix'_apply, b60_omega]

/-- The integral Gram matrix of the trace pairing `b60_E`.
Source: `b60_E`; G32 v0.16, §2.1. -/
def hk_E : Matrix hk_ι hk_ι ℤ :=
  LinearMap.toMatrix₂' ℤ b60_E

example : hk_E (0, 0) (0, 1) = 1 := by
  simp [hk_E, LinearMap.toMatrix₂'_apply, b60_E, b60_diag, Pi.single_apply]

/-- The unitary group `U(b60_H)` as a `ℚ`-group, at points in a ring `R` with trivial
involution: `12 × 12` matrices commuting with `ω` and preserving the trace pairing `E`. At
`R = ℚ` these are the `K`-linear isometries of `(K⁶, b60_H)`; at `R = ℝ` this is `U(3,3)`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §23.9 (restriction of scalars of a unitary
group); G32 v0.16, §2.1; plan `G32RemainingPremises.md`, §2.3. -/
def hk_group (R : Type*) [CommRing R] [StarRing R] [TrivialStar R] :
    Set (Matrix hk_ι hk_ι R) :=
  {g | g ∈ hk_unitary (hk_E.map (Int.cast : ℤ → R)) ∧
    g * hk_Omega.map (Int.cast : ℤ → R) = hk_Omega.map (Int.cast : ℤ → R) * g}

example : (1 : Matrix hk_ι hk_ι ℚ) ∈ hk_group ℚ := by
  simp [hk_group, hk_unitary]

example : (-1 : Matrix hk_ι hk_ι ℝ) ∈ hk_group ℝ := by
  simp [hk_group, hk_unitary]

/-- The Lie algebra of `hk_group`: `Xᵀ E + E X = 0` and `X ω = ω X`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §3.9; plan `G32RemainingPremises.md`,
§2.3, stage S2. -/
def hk_lieAlg (R : Type*) [CommRing R] [StarRing R] [TrivialStar R] :
    Set (Matrix hk_ι hk_ι R) :=
  {X | X ∈ hk_lie (hk_E.map (Int.cast : ℤ → R)) ∧
    X * hk_Omega.map (Int.cast : ℤ → R) = hk_Omega.map (Int.cast : ℤ → R) * X}

example : (0 : Matrix hk_ι hk_ι ℚ) ∈ hk_lieAlg ℚ := by
  simp [hk_lieAlg, hk_lie]

/-- Rational matrices as real matrices.
Source: Mathlib `Matrix.map`, `Rat.cast`. -/
def hk_ratCast (q : Matrix hk_ι hk_ι ℚ) : Matrix hk_ι hk_ι ℝ :=
  q.map (Rat.cast : ℚ → ℝ)

example : hk_ratCast 1 = 1 := by
  simp [hk_ratCast]

/-- A real matrix acting `ℂ`-linearly on `ℂ ⊗ b60_Lattice`, in the complexified integral basis
`b60_basis`. The columns follow `LinearMap.toMatrix'`, as for `hk_Omega`.
Source: Mathlib `Matrix.toLin`; `b60_basis`. -/
def hk_toC (g : Matrix hk_ι hk_ι ℝ) : (ℂ ⊗[ℤ] b60_Lattice) →ₗ[ℂ] (ℂ ⊗[ℤ] b60_Lattice) :=
  Matrix.toLin b60_basis b60_basis (g.map (Complex.ofReal : ℝ → ℂ))

example : hk_toC 1 = LinearMap.id := by
  simp [hk_toC, Matrix.toLin_one]

/-- The real matrix `g` carries the filtration at `τ` onto the filtration at `σ`:
`b60_F σ = g · b60_F τ`. By `b60_F_injective` there is at most one such `σ`.
Source: G32 v0.16, §2.1 (the action of `U(V, H)(ℝ)` on `𝓗₃`); van Geemen, LNM 1594, §5.10. -/
def hk_moves (g : Matrix hk_ι hk_ι ℝ) (τ σ : g32m_Domain) : Prop :=
  b60_F σ = (b60_F τ).map (hk_toC g)

example (τ : g32m_Domain) : hk_moves 1 τ τ := by
  simp [hk_moves, hk_toC, Matrix.toLin_one]

end HodgeLean.Foundations.Program
