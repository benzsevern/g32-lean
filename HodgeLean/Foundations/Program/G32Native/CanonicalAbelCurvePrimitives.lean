import HodgeLean.Foundations.Program.G32Native.AbelDiscPrimitive
import HodgeLean.Foundations.Program.G32Native.CanonicalAbelPrimitiveData
import HodgeLean.Foundations.Program.G32Native.AbelDiscCoefficientPairing
import HodgeLean.Foundations.Program.G32Native.CanonicalCoefficientForms
import HodgeLean.Foundations.Curves.AbelAdapter.StageTwo.AbelLocalPrimitives
import HodgeLean.Foundations.Curves.AbelAdapter.StageFour.DiscCoefficientComparison

/-! # Local Abel primitives in the original normalized curve coordinate -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Manifold Filter Set
open HodgeLean.Foundations.Curves.AbelAdapter
open HodgeLean.Foundations.Curves.AbelAdapter.StageTwo
open HodgeLean.Foundations.Curves.AbelAdapter.StageFour
open scoped ContDiff Topology BigOperators
namespace HodgeLean.Foundations.Program.G32Native

/-- Local vector primitives of the original curve Abel map retain every original form derivative. -/
theorem canonical_curve_local_abel_primitive (G : CanonicalAbelGeometry)
    [Module.Finite ℤ (b3_periodLattice (Fin 1 → ℂ) (AlgebraicGeometry.ComplexPoint G.Z))]
    [DiscreteTopology (b2_latticeMap
      (b3_periodLattice (Fin 1 → ℂ) (AlgebraicGeometry.ComplexPoint G.Z))
      (b3_periodF (Fin 1 → ℂ) (AlgebraicGeometry.ComplexPoint G.Z))).range]
    (p q : AlgebraicGeometry.ComplexPoint G.Z) :
    ∃ g : ℂ → b3Rest2_VJ (Fin 1 → ℂ) (AlgebraicGeometry.ComplexPoint G.Z),
      AnalyticAt ℂ g 0 ∧
      (∀ᶠ z in 𝓝 (0 : ℂ), b3Rest2_covHom (E := Fin 1 → ℂ) (C := AlgebraicGeometry.ComplexPoint G.Z) (g z) =
        analyticAbel (Module.finrank_fin_fun (n := 1) ℂ) p (b3A_disc q (b4cov_lineEquiv (Module.finrank_fin_fun (n := 1) ℂ) 1) z)) ∧
      ∀ a : Fin (G.k + 1) → ℂ,
        deriv (fun z => periodLinear (E := Fin 1 → ℂ) (C := AlgebraicGeometry.ComplexPoint G.Z) (canonicalCoefficientForm G a) (g z)) =ᶠ[𝓝 0]
          HurwitzPrymRR_loc (Module.finrank_fin_fun (n := 1) ℂ) (canonicalCoefficientForm G a) q := by
  have hp := canonical_curve_primitive_data G q
  rcases hp with ⟨R, hR, hchart, H, hH⟩
  let h := Module.finrank_fin_fun (n := 1) ℂ
  let b := canonicalFormBasis G
  let L := b4cov_lineEquiv h
  let u := L 1
  let κ := L.symm.toContinuousLinearMap
  have hκ (v : Fin 1 → ℂ) : v = κ v • u := by
    change v = L.symm v • L 1
    rw [← map_smul, smul_eq_mul, mul_one, L.apply_symm_apply]
  have hκu : κ u = 1 := L.symm_apply_apply 1
  have hgen := abel_disc_primitive_of_basis (E := Fin 1 → ℂ)
    (C := AlgebraicGeometry.ComplexPoint G.Z) (ι := Fin (G.k + 1)) h p q b κ u hκ hκu
    R hR hchart H hH
  refine ⟨hgen.choose, hgen.choose_spec.1, hgen.choose_spec.2.1, ?_⟩
  intro a
  exact (hgen.choose_spec.2.2 a).trans (discCoefficient_lineEquiv h (canonicalCoefficientForm G a).val q)

#print axioms canonical_curve_local_abel_primitive
end HodgeLean.Foundations.Program.G32Native
