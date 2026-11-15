import HodgeLean.Foundations.Program.CurveJacobian
import HodgeLean.Foundations.Singular.Circle
import HodgeLean.Foundations.Program.SchoenCycleDifferentialQuotient

/-! # Genus transport to the retained scheme curve
The holomorphic differential dimension is determined by the first rational Betti number.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Manifold CategoryTheory AlgebraicGeometry
open scoped ContDiff
namespace HodgeLean.Foundations.Program

/-- A homeomorphism preserves holomorphic differential dimension for arbitrary
one-dimensional complex chart models. -/
theorem s2e_holForm_finrank_homeomorph
    {E F C D : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [TopologicalSpace C] [TopologicalSpace D] [ChartedSpace E C] [ChartedSpace F D]
    [IsManifold 𝓘(ℂ, E) ω C] [IsManifold 𝓘(ℂ, F) ω D]
    [T2Space C] [T2Space D] [CompactSpace C] [CompactSpace D]
    [ConnectedSpace C] [ConnectedSpace D]
    (hE : Module.finrank ℂ E = 1) (hF : Module.finrank ℂ F = 1) (e : C ≃ₜ D) :
    Module.finrank ℂ (b3_HolForm E C) = Module.finrank ℂ (b3_HolForm F D) := by
  have h := (HodgeLean.Foundations.Singular.cohomologyHomeomorphEquiv e 1).finrank_eq
  rw [b3_finrank_cohomology hE, b3_finrank_cohomology hF] at h
  omega

/-- The retained smooth integral curve has relative dimension one. -/
theorem s2e_scheme_curve_relativeDimension (Z : Over (Spec ↧ℂ))
    [IsIntegral Z.left] [Smooth Z.hom] (hdim : TopologicalSpace.dim Z.left = 1) :
    SmoothOfRelativeDimension 1 Z.hom := by
  have h : SmoothOfRelativeDimension (TopologicalSpace.dim Z.left) Z.hom := inferInstance
  simpa only [hdim] using h

/-- The supplied topological curve comparison transports genus to the scheme-derived manifold. -/
theorem s2e_scheme_holForm_finrank_homeomorph
    {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    (Z : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    (e : C ≃ₜ ComplexPoint Z) :
    Module.finrank ℂ (b3_HolForm ℂ C) =
      Module.finrank ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) := by
  letI : QuasiSeparatedSpace Z.left := quasiSeparatedSpace_of_quasiSeparated Z.hom
  letI : ConnectedSpace (ComplexPoint Z) := AlgebraicGeometry.ComplexPoint.connectedSpace Z
  letI : T2Space C := e.symm.t2Space
  letI : CompactSpace C := e.symm.compactSpace
  letI : ConnectedSpace C := e.connectedSpace_iff.mpr inferInstance
  exact s2e_holForm_finrank_homeomorph (by simp) (Module.finrank_fin_fun (n := 1) ℂ) e

/-- Construct the paired differential family in the retained scheme's native manifold,
using the supplied curve homeomorphism and genus equation. -/
theorem s2e_scheme_paired_differential_family
    {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    (Z : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    (e : C ≃ₜ ComplexPoint Z) (k r : ℕ) (y : Fin (2 * r) → C)
    (hy : Function.Injective y)
    (hgenus : 2 * k + 2 = 2 * Module.finrank ℂ (b3_HolForm ℂ C) + 2 * r) :
    let hE := Module.finrank_fin_fun (n := 1) ℂ
    ∃ w : Fin r → b4c_MeroForm (Fin 1 → ℂ) (ComplexPoint Z) hE,
      (∀ i p, (-1 : WithTop ℤ) ≤ meromorphicOrderAt (HurwitzPrymRR_loc hE (w i) p) 0) ∧
      (∀ i p, p ≠ e (y ⟨2 * i.val, by omega⟩) →
        p ≠ e (y ⟨2 * i.val + 1, by omega⟩) →
        AnalyticAt ℂ (HurwitzPrymRR_loc hE (w i) p) 0) ∧
      (∀ i j,
        b4c_res (hE := hE) (w i) (e (y ⟨2 * j.val, by omega⟩)) =
          (if i = j then -1 else 0) ∧
        b4c_res (hE := hE) (w i) (e (y ⟨2 * j.val + 1, by omega⟩)) =
          (if i = j then 1 else 0)) ∧
      Function.Injective (s2e_pairedDifferentialLinear hE w) ∧
      Module.finrank ℂ (LinearMap.range (s2e_pairedDifferentialLinear hE w)) = k + 1 := by
  letI : QuasiSeparatedSpace Z.left := quasiSeparatedSpace_of_quasiSeparated Z.hom
  letI : ConnectedSpace (ComplexPoint Z) := AlgebraicGeometry.ComplexPoint.connectedSpace Z
  have hg : 2 * k + 2 =
      2 * Module.finrank ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) + 2 * r := by
    rw [← s2e_scheme_holForm_finrank_homeomorph Z e]
    exact hgenus
  exact s2e_paired_slice_differential_family (Module.finrank_fin_fun (n := 1) ℂ)
    k r (fun i => e (y i)) (e.injective.comp hy) hg

end HodgeLean.Foundations.Program
