import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.LinearAlgebra.Basis.Defs

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Actual representatives of a cotangent basis generate the actual maximal ideal of a Noetherian local algebra.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Atiyah–Macdonald, Introduction to Commutative Algebra, Proposition 2.8. -/
theorem s2e_cotangent_basis_generates_maximalIdeal
    (k R σ : Type*) [CommRing k] [CommRing R] [Algebra k R]
    [IsLocalRing R] [IsNoetherianRing R]
    (c : σ → IsLocalRing.maximalIdeal R)
    (b : Module.Basis σ k (IsLocalRing.maximalIdeal R).Cotangent)
    (hb : ∀ i, b i = (IsLocalRing.maximalIdeal R).toCotangent (c i)) :
    Ideal.span (Set.range (fun i => (c i).val)) = IsLocalRing.maximalIdeal R := by
  have hspan : Submodule.span R (Set.range b) = ⊤ :=
    Submodule.span_eq_top_of_span_eq_top k R _ b.span_eq
  have hrange : Set.range b = (IsLocalRing.maximalIdeal R).toCotangent '' Set.range c := by
    rw [← Set.range_comp]
    exact congrArg Set.range (funext hb)
  rw [hrange, ← Submodule.map_span] at hspan
  have hc : Submodule.span R (Set.range c) = ⊤ :=
    IsLocalRing.CotangentSpace.map_eq_top_iff.mp hspan
  have hh := congrArg (fun M : Submodule R (IsLocalRing.maximalIdeal R) =>
    M.map (IsLocalRing.maximalIdeal R).subtype) hc
  simp only [Submodule.map_span, ← Set.range_comp, Function.comp_def,
    Submodule.map_top, Submodule.range_subtype] at hh
  exact hh

#print axioms s2e_cotangent_basis_generates_maximalIdeal
end HodgeLean.Foundations.Program
