import HodgeLean.Foundations.Program.G32Native.CanonicalAbelCurvePrimitives
import HodgeLean.Foundations.Program.G32Native.CanonicalPeriodLocalHomeomorph

/-! # Original curve primitives in the retained Abel coefficient space -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter
open HodgeLean.Foundations.Curves.AbelAdapter
open HodgeLean.Foundations.Curves.AbelAdapter.StageTwo
open scoped Topology BigOperators
namespace HodgeLean.Foundations.Program.G32Native

/-- The original period cover and the retained Abel coefficients are linearly equivalent. -/
def canonicalCoverEquiv (G : CanonicalAbelGeometry)
    [Module.Finite ℤ (b3_periodLattice (Fin 1 → ℂ) (AlgebraicGeometry.ComplexPoint G.Z))] :
    (Fin (G.k + 1) → ℂ) ≃ₗ[ℂ]
      b3Rest2_VJ (Fin 1 → ℂ) (AlgebraicGeometry.ComplexPoint G.Z) :=
  (quotientBasisEquiv (Module.finrank_fin_fun (n := 1) ℂ) (canonicalFormBasis G)).symm.trans
    (b2_coord (b3Rest2_QJ (Fin 1 → ℂ) (AlgebraicGeometry.ComplexPoint G.Z)))

/-- The original curve has analytic coefficient primitives with all original local form derivatives. -/
theorem canonical_curve_coefficient_primitive (G : CanonicalAbelGeometry)
    [Module.Finite ℤ (b3_periodLattice (Fin 1 → ℂ) (AlgebraicGeometry.ComplexPoint G.Z))]
    [DiscreteTopology (b2_latticeMap
      (b3_periodLattice (Fin 1 → ℂ) (AlgebraicGeometry.ComplexPoint G.Z))
      (b3_periodF (Fin 1 → ℂ) (AlgebraicGeometry.ComplexPoint G.Z))).range]
    (p q : AlgebraicGeometry.ComplexPoint G.Z) :
    ∃ g : ℂ → (Fin (G.k + 1) → ℂ), AnalyticAt ℂ g 0 ∧
      (∀ᶠ z in 𝓝 (0 : ℂ), canonicalPeriodHom G (g z) =
        analyticAbel (Module.finrank_fin_fun (n := 1) ℂ) p
          (b3A_disc q (b4cov_lineEquiv (Module.finrank_fin_fun (n := 1) ℂ) 1) z)) ∧
      ∀ a : Fin (G.k + 1) → ℂ,
        deriv (fun z => coefficientDual G.k (g z) a) =ᶠ[𝓝 0]
          HurwitzPrymRR_loc (Module.finrank_fin_fun (n := 1) ℂ) (canonicalCoefficientForm G a) q := by
  obtain ⟨g, hg, hcover, hderiv⟩ := canonical_curve_local_abel_primitive G p q
  let J := canonicalCoverEquiv G
  let f := fun z => J.symm (g z)
  have hf : AnalyticAt ℂ f 0 := (J.symm.toLinearMap.toContinuousLinearMap.analyticAt (g 0)).comp hg
  have hq (v : Fin (G.k + 1) → ℂ) :
      b3Rest2_covHom (E := Fin 1 → ℂ) (C := AlgebraicGeometry.ComplexPoint G.Z) (J v) =
        canonicalPeriodHom G v := b3Rest2_covHom_coord _
  refine ⟨f, hf, ?_, ?_⟩
  · filter_upwards [hcover] with z hz
    exact (hq (f z)).symm.trans (by simpa only [f, J.apply_symm_apply] using hz)
  · intro a
    have heval : (fun z => coefficientDual G.k (f z) a) =
        (fun z => periodLinear (canonicalCoefficientForm G a) (g z)) := by
      funext z
      have he := canonicalCoefficientForm_period_pairing G a (f z)
      change periodLinear (canonicalCoefficientForm G a) (J (f z)) = _ at he
      rw [show J (f z) = g z from J.apply_symm_apply (g z)] at he
      exact he.symm
    rw [heval]
    exact hderiv a

#print axioms canonicalCoverEquiv
#print axioms canonical_curve_coefficient_primitive
end HodgeLean.Foundations.Program.G32Native
