import Mathlib.RingTheory.Kaehler.JacobiZariski
import Mathlib.RingTheory.Smooth.Basic

/-! # Relative infinitesimal smoothness from the original differential map -/
noncomputable section
set_option maxHeartbeats 400000
open scoped TensorProduct
namespace HodgeLean.Foundations.Program.G32Native

/-- Injectivity of the original absolute differential pullback removes the
relative first cotangent homology when the absolute source is formally smooth.
Source: Stacks Project, Tags 00S2 and 00TI. -/
theorem residual_relative_h1_of_differential_injective
    (R S T : Type*) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Algebra.FormallySmooth R T]
    (h : Function.Injective (KaehlerDifferential.mapBaseChange R S T)) :
    Subsingleton (Algebra.H1Cotangent S T) := by
  have hz (x : Algebra.H1Cotangent S T) : Algebra.H1Cotangent.δ R S T x = 0 := by
    apply h
    simpa only [map_zero] using
      (Algebra.H1Cotangent.exact_δ_mapBaseChange R S T).apply_apply_eq_zero x
  have hx (x : Algebra.H1Cotangent S T) : x = 0 := by
    obtain ⟨y, hy⟩ := (Algebra.H1Cotangent.exact_map_δ R S T x).mp (hz x)
    rw [Subsingleton.elim y 0, map_zero] at hy
    exact hy.symm
  exact ⟨fun x y => (hx x).trans (hx y).symm⟩

#print axioms residual_relative_h1_of_differential_injective
end HodgeLean.Foundations.Program.G32Native
