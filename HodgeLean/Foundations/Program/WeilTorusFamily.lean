import HodgeLean.Foundations.Program.WeilTorusFamilyProofs

/-! # B6-0a: lattice and Weil-type filtration

The implication from membership in the fixed G32 bounded domain to B2's weight-one and
Riemann relations concerns the explicit integral lattice and graph frame. The converse
positivity statement is also included. Algebraic fibres, membership in the algebraic moduli
problem, Landherr coverage and uniformization comparisons belong to later stages.
HC no distance; AV milestone no distance.
-/

noncomputable section
open scoped TensorProduct Matrix ComplexOrder
open HodgeLean.Papers HodgeLean.Foundations.HermitianForm
namespace HodgeLean.Foundations.Program

/-- The integral action satisfies the quadratic relation.
Source: G32 v0.16, §2.1; multiplication in ℤ[√−3]. -/
theorem b60_omega_square  :
    b60_omega.comp b60_omega = (-3 : ℤ) • LinearMap.id :=
  b60_omega_square_aux 

example (x : b60_Lattice) : b60_omega (b60_omega x) = (-3 : ℤ) • x :=
  LinearMap.congr_fun b60_omega_square x

/-- The integral pairing has exactly the G32 trace normalization.
Source: G32 v0.16, §2.1; WeilHermitian.im_weilHermitian. -/
theorem b60_trace_pairing (x y : b60_Lattice) :
    (b60_E x y : ℚ) = QuadraticAlgebra.trace
      (b60_H (b60_rat x) (b60_rat y) / (2 * QuadraticAlgebra.omega)) :=
  b60_trace_pairing_aux x y

example : (b60_E 0 0 : ℚ) = QuadraticAlgebra.trace
    (b60_H (b60_rat 0) (b60_rat 0) / (2 * QuadraticAlgebra.omega)) :=
  b60_trace_pairing 0 0

/-- The six graph vectors form an independent frame at every matrix.
Source: van Geemen, LNM 1594, §§5.7–5.10; graph coordinates. -/
theorem b60_frame_independent (z : Fin 9 → ℂ) :
    LinearIndependent ℂ (b60_frame z) :=
  b60_frame_independent_aux z

example : LinearIndependent ℂ (b60_frame 0) := b60_frame_independent 0

/-- Bounded-domain membership gives the weight-one decomposition.
Source: van Geemen, LNM 1594, §§5.7–5.10; G32 v0.16, §2.1. -/
theorem b60_weight_one (τ : g32m_Domain) :
    b2_IsWeightOne b60_Lattice (b60_F τ) :=
  b60_weight_one_aux τ

example : b2_IsWeightOne b60_Lattice (b60_F 0) :=
  b60_weight_one ⟨0, g32m_zero_mem⟩

/-- The Riemann relations hold exactly on the frozen bounded domain.
Source: van Geemen, LNM 1594, §§5.7–5.11; B2 Riemann relations. -/
theorem b60_riemann_iff (z : Fin 9 → ℂ) :
    b2_IsRiemannForm b60_Lattice (b60_F z) b60_E ↔ z ∈ g32m_Domain :=
  b60_riemann_iff_aux z

example : b2_IsRiemannForm b60_Lattice (b60_F 0) b60_E :=
  (b60_riemann_iff 0).2 g32m_zero_mem

/-- The integral quadratic action preserves the filtration.
Source: van Geemen, LNM 1594, §§5.1, 5.7; G32 v0.16, Definition 2.1. -/
theorem b60_omega_preserves (z : Fin 9 → ℂ) :
    Submodule.map b60_omegaC (b60_F z) ≤ b60_F z :=
  b60_omega_preserves_aux z

example : Submodule.map b60_omegaC (b60_F 0) ≤ b60_F 0 :=
  b60_omega_preserves 0

/-- The two quadratic eigenspaces each contribute dimension three.
Source: van Geemen, LNM 1594, §5.1; G32 v0.16, Definition 2.1. -/
theorem b60_weil_dimensions (z : Fin 9 → ℂ) :
    Module.finrank ℂ ↥(b60_F z ⊓ Module.End.eigenspace b60_omegaC
      (Complex.I * (Real.sqrt 3 : ℂ))) = 3 ∧
    Module.finrank ℂ ↥(b60_F z ⊓ Module.End.eigenspace b60_omegaC
      (-Complex.I * (Real.sqrt 3 : ℂ))) = 3 :=
  b60_weil_dimensions_aux z

example : Module.finrank ℂ ↥(b60_F 0 ⊓ Module.End.eigenspace b60_omegaC
    (Complex.I * (Real.sqrt 3 : ℂ))) = 3 := (b60_weil_dimensions 0).1

/-- All frame coordinates are entire holomorphic functions of the nine entries.
Source: van Geemen, LNM 1594, §5.11; the displayed affine frame. -/
theorem b60_frame_holomorphic (p : Fin 2 × Fin 3) (q : Fin 6 × Fin 2) :
    Differentiable ℂ (fun z : Fin 9 → ℂ => b60_frameCoord z p q) :=
  b60_frame_holomorphic_aux p q

example : DifferentiableAt ℂ (fun z : Fin 9 → ℂ => b60_frameCoord z (0, 0) (0, 0)) 0 :=
  b60_frame_holomorphic (0, 0) (0, 0) 0

end HodgeLean.Foundations.Program
