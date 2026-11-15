import HodgeLean.Foundations.HermitianClassProofs
import HodgeLean.Foundations.Program.UniversalFamilyCoverDefs

/-! # Hermitian classification: first stage

Implication from an explicit Hermitian pairing to rational trace data and diagonal coordinates.
Arithmetic isotropy and the classification isometry remain later work.
HC no distance; AV milestone no distance.
-/

noncomputable section
namespace HodgeLean.Foundations.HermitianClass
open HermitianForm

/-- Recover the K-valued pairing from the trace pairing and multiplication by √−3.
Source: QuadraticAlgebra multiplication with a = −3, b = 0; linearity in the second argument. -/
theorem hermClass_reconstruct (W : Type*) [AddCommGroup W]
    [Module (QuadraticAlgebra ℚ (-3) 0) W] [Module ℚ W]
    [IsScalarTower ℚ (QuadraticAlgebra ℚ (-3) 0) W]
    (h : W →ₗ⋆[QuadraticAlgebra ℚ (-3) 0] W →ₗ[QuadraticAlgebra ℚ (-3) 0]
      QuadraticAlgebra ℚ (-3) 0) (x y : W) :
    h x y = algebraMap ℚ _ (traceBilin W h x y / 2) -
      (QuadraticAlgebra.omega : QuadraticAlgebra ℚ (-3) 0) *
        algebraMap ℚ _ (traceBilin W h x ((QuadraticAlgebra.omega :
          QuadraticAlgebra ℚ (-3) 0) • y) / 6) :=
  hermClass_reconstruct_aux W h x y

example (W : Type*) [AddCommGroup W]
    [Module (QuadraticAlgebra ℚ (-3) 0) W] [Module ℚ W]
    [IsScalarTower ℚ (QuadraticAlgebra ℚ (-3) 0) W]
    (h : W →ₗ⋆[QuadraticAlgebra ℚ (-3) 0] W →ₗ[QuadraticAlgebra ℚ (-3) 0]
      QuadraticAlgebra ℚ (-3) 0) (x y : W) :
    h x y = algebraMap ℚ _ (traceBilin W h x y / 2) -
      (QuadraticAlgebra.omega : QuadraticAlgebra ℚ (-3) 0) *
        algebraMap ℚ _ (traceBilin W h x ((QuadraticAlgebra.omega :
          QuadraticAlgebra ℚ (-3) 0) • y) / 6) :=
  hermClass_reconstruct W h x y

/-- Hermitian symmetry and nondegeneracy pass to the rational trace pairing.
Source: Trace pairing for a separable quadratic extension; `HermitianForm.reBilin`. -/
theorem hermClass_trace_regular (W : Type*) [AddCommGroup W]
    [Module (QuadraticAlgebra ℚ (-3) 0) W] [Module ℚ W]
    [IsScalarTower ℚ (QuadraticAlgebra ℚ (-3) 0) W]
    (h : W →ₗ⋆[QuadraticAlgebra ℚ (-3) 0] W →ₗ[QuadraticAlgebra ℚ (-3) 0]
      QuadraticAlgebra ℚ (-3) 0) (hh : h.IsSymm) (hn : h.Nondegenerate) :
    (traceBilin W h).IsSymm ∧ (traceBilin W h).Nondegenerate :=
  hermClass_trace_regular_aux W h hh hn

example (W : Type*) [AddCommGroup W]
    [Module (QuadraticAlgebra ℚ (-3) 0) W] [Module ℚ W]
    [IsScalarTower ℚ (QuadraticAlgebra ℚ (-3) 0) W]
    (h : W →ₗ⋆[QuadraticAlgebra ℚ (-3) 0] W →ₗ[QuadraticAlgebra ℚ (-3) 0]
      QuadraticAlgebra ℚ (-3) 0) (hh : h.IsSymm) (hn : h.Nondegenerate) :
    (traceBilin W h).IsSymm ∧ (traceBilin W h).Nondegenerate :=
  hermClass_trace_regular W h hh hn

/-- Trace isotropy is exactly Hermitian isotropy, on the same vectors.
Source: `QuadraticAlgebraAux.star_eq_self_iff`, applied to h(x,x). -/
theorem hermClass_trace_zero (W : Type*) [AddCommGroup W]
    [Module (QuadraticAlgebra ℚ (-3) 0) W] [Module ℚ W]
    [IsScalarTower ℚ (QuadraticAlgebra ℚ (-3) 0) W]
    (h : W →ₗ⋆[QuadraticAlgebra ℚ (-3) 0] W →ₗ[QuadraticAlgebra ℚ (-3) 0]
      QuadraticAlgebra ℚ (-3) 0) (hh : h.IsSymm) (x : W) :
    traceQuad W h x = 0 ↔ h x x = 0 :=
  hermClass_trace_zero_aux W h hh x

example (W : Type*) [AddCommGroup W]
    [Module (QuadraticAlgebra ℚ (-3) 0) W] [Module ℚ W]
    [IsScalarTower ℚ (QuadraticAlgebra ℚ (-3) 0) W]
    (h : W →ₗ⋆[QuadraticAlgebra ℚ (-3) 0] W →ₗ[QuadraticAlgebra ℚ (-3) 0]
      QuadraticAlgebra ℚ (-3) 0) (hh : h.IsSymm) (x : W) :
    traceQuad W h x = 0 ↔ h x x = 0 :=
  hermClass_trace_zero W h hh x

/-- A nondegenerate Hermitian form has a rational nonzero diagonal in K-coordinates.
Source: Hermitian Gram–Schmidt over a field of characteristic zero; `HermitianForm.diagForm` convention. -/
theorem hermClass_diagonalize (W : Type*) [AddCommGroup W]
    [Module (QuadraticAlgebra ℚ (-3) 0) W] [Module ℚ W]
    [IsScalarTower ℚ (QuadraticAlgebra ℚ (-3) 0) W]
    [Module.Finite (QuadraticAlgebra ℚ (-3) 0) W]
    (h : W →ₗ⋆[QuadraticAlgebra ℚ (-3) 0] W →ₗ[QuadraticAlgebra ℚ (-3) 0]
      QuadraticAlgebra ℚ (-3) 0) (hh : h.IsSymm) (hn : h.Nondegenerate) :
    ∃ d : Fin (Module.finrank (QuadraticAlgebra ℚ (-3) 0) W) → ℚ,
      (∀ i, d i ≠ 0) ∧
      ∃ e : W ≃ₗ[QuadraticAlgebra ℚ (-3) 0]
        (Fin (Module.finrank (QuadraticAlgebra ℚ (-3) 0) W) →
          QuadraticAlgebra ℚ (-3) 0),
        ∀ x y, diagForm d (e x) (e y) = h x y :=
  hermClass_diagonalize_aux W h hh hn

example (W : Type*) [AddCommGroup W]
    [Module (QuadraticAlgebra ℚ (-3) 0) W] [Module ℚ W]
    [IsScalarTower ℚ (QuadraticAlgebra ℚ (-3) 0) W]
    [Module.Finite (QuadraticAlgebra ℚ (-3) 0) W]
    (h : W →ₗ⋆[QuadraticAlgebra ℚ (-3) 0] W →ₗ[QuadraticAlgebra ℚ (-3) 0]
      QuadraticAlgebra ℚ (-3) 0) (hh : h.IsSymm) (hn : h.Nondegenerate) :
    ∃ d : Fin (Module.finrank (QuadraticAlgebra ℚ (-3) 0) W) → ℚ,
      (∀ i, d i ≠ 0) ∧
      ∃ e : W ≃ₗ[QuadraticAlgebra ℚ (-3) 0]
        (Fin (Module.finrank (QuadraticAlgebra ℚ (-3) 0) W) →
          QuadraticAlgebra ℚ (-3) 0),
        ∀ x y, diagForm d (e x) (e y) = h x y :=
  hermClass_diagonalize W h hh hn

/-- The trace form has twice each Hermitian inertia index.
Source: Sylvester inertia; `HermitianForm.hermSignature_diagForm` and positive scaling by two. -/
theorem hermClass_trace_signature (W : Type*) [AddCommGroup W]
    [Module (QuadraticAlgebra ℚ (-3) 0) W] [Module ℚ W]
    [IsScalarTower ℚ (QuadraticAlgebra ℚ (-3) 0) W]
    [Module.Finite (QuadraticAlgebra ℚ (-3) 0) W]
    (h : W →ₗ⋆[QuadraticAlgebra ℚ (-3) 0] W →ₗ[QuadraticAlgebra ℚ (-3) 0]
      QuadraticAlgebra ℚ (-3) 0) (hh : h.IsSymm) (hn : h.Nondegenerate) :
    sigPos ((traceQuad W h).baseChange ℝ) = 2 * (hermSignature h).1 ∧
      sigNeg ((traceQuad W h).baseChange ℝ) = 2 * (hermSignature h).2 :=
  hermClass_trace_signature_aux W h hh hn

example (W : Type*) [AddCommGroup W]
    [Module (QuadraticAlgebra ℚ (-3) 0) W] [Module ℚ W]
    [IsScalarTower ℚ (QuadraticAlgebra ℚ (-3) 0) W]
    [Module.Finite (QuadraticAlgebra ℚ (-3) 0) W]
    (h : W →ₗ⋆[QuadraticAlgebra ℚ (-3) 0] W →ₗ[QuadraticAlgebra ℚ (-3) 0]
      QuadraticAlgebra ℚ (-3) 0) (hh : h.IsSymm) (hn : h.Nondegenerate) :
    sigPos ((traceQuad W h).baseChange ℝ) = 2 * (hermSignature h).1 ∧
      sigNeg ((traceQuad W h).baseChange ℝ) = 2 * (hermSignature h).2 :=
  hermClass_trace_signature W h hh hn

/-- Satisfiable inputs from the explicit diagonal, using only existing algebra results. -/
example :
    (diagForm (a := -3) (b := 0) ![1, 1, 1, -1, -1, -2]).IsSymm ∧
    (diagForm (a := -3) (b := 0) ![1, 1, 1, -1, -1, -2]).Nondegenerate :=
  ⟨diagForm_isSymm _, diagForm_nondegenerate diag_F1569_ne_zero⟩

/-- Chain check on the actual member form: its trace data retains every K-valued pairing.
The arithmetic isometry is not selected here. -/
example (P : HodgeLean.Papers.g32t_Sixfold) (hP : HodgeLean.Papers.g32t_IsMember P)
    (x y : Program.b60c_V P) :
    Program.b60c_H P hP x y =
      algebraMap ℚ _ (traceBilin _ (Program.b60c_H P hP) x y / 2) -
      (QuadraticAlgebra.omega : QuadraticAlgebra ℚ (-3) 0) *
        algebraMap ℚ _ (traceBilin _ (Program.b60c_H P hP) x
          ((QuadraticAlgebra.omega : QuadraticAlgebra ℚ (-3) 0) • y) / 6) :=
  hermClass_reconstruct _ (Program.b60c_H P hP) x y

/-- The actual member supplies regular trace data and identical isotropic vectors.
These are the linear-algebra inputs of stages C2 and C4 in the route memo. -/
example (P : HodgeLean.Papers.g32t_Sixfold) (hP : HodgeLean.Papers.g32t_IsMember P) :
    (traceBilin _ (Program.b60c_H P hP)).Nondegenerate ∧
      (∀ x : Program.b60c_V P,
        traceQuad _ (Program.b60c_H P hP) x = 0 ↔ Program.b60c_H P hP x x = 0) := by
  have hh : (Program.b60c_H P hP).IsSymm :=
    WeilHermitian.isSymm_weilHermitian
      (HodgeLean.RealDefs.isAlt_polarizationForm _ hP.nondegenerate)
  have hn : (Program.b60c_H P hP).Nondegenerate :=
    WeilHermitian.nondegenerate_weilHermitian
      (HodgeLean.RealDefs.nondegenerate_polarizationForm _ hP.nondegenerate)
  exact ⟨(hermClass_trace_regular _ _ hh hn).2,
    fun x => hermClass_trace_zero _ _ hh x⟩

end HodgeLean.Foundations.HermitianClass
