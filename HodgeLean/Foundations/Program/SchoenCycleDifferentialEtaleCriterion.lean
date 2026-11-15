import Mathlib.RingTheory.Etale.Kaehler

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open KaehlerDifferential
namespace HodgeLean.Foundations.Program

/-- A bijective differential base-change map and vanishing first cotangent homology give formal étaleness over the intermediate algebra.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
EGA IV, 17.11.1; the Jacobi–Zariski exact sequence. -/
theorem s2e_formallyEtale_of_differential_baseChange_bijective
    (R S T : Type*) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Subsingleton (Algebra.H1Cotangent R T)]
    (h : Function.Bijective (mapBaseChange R S T)) : Algebra.FormallyEtale S T := by
  constructor
  · apply subsingleton_of_forall_eq 0
    intro x
    obtain ⟨y, rfl⟩ := map_surjective R S T x
    exact (exact_mapBaseChange_map R S T y).mpr (h.surjective y)
  · apply subsingleton_of_forall_eq 0
    intro x
    have hx : Algebra.H1Cotangent.δ R S T x = 0 := by
      apply h.injective
      rw [map_zero]
      exact (Algebra.H1Cotangent.exact_δ_mapBaseChange R S T _).mpr ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := (Algebra.H1Cotangent.exact_map_δ R S T x).mp hx
    rw [← hy, Subsingleton.elim y 0, map_zero]

#print axioms s2e_formallyEtale_of_differential_baseChange_bijective
end HodgeLean.Foundations.Program
