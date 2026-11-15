import HodgeLean.Foundations.Program.G32Native.PairedC3NakayamaGenerators
import Mathlib.RingTheory.Ideal.Cotangent

/-! # The adapted branch equation is a minimal slice generator -/
noncomputable section
set_option maxHeartbeats 200000
namespace HodgeLean.Foundations.Program.G32Native

/-- Transverse branch differentials keep every adapted difference out of the
square of the ambient maximal ideal, with the coefficient retained.
Source: Hartshorne, Algebraic Geometry, II.8, cotangent spaces. -/
theorem paired_c3_adapted_not_mem_square
    {R : Type*} [CommRing R] [IsLocalRing R]
    (u v : IsLocalRing.maximalIdeal R)
    (h : LinearIndependent (R ⧸ IsLocalRing.maximalIdeal R)
      ![(IsLocalRing.maximalIdeal R).toCotangent u,
        (IsLocalRing.maximalIdeal R).toCotangent v]) (a : R) :
    (v : R) - a * (u : R) ∉ IsLocalRing.maximalIdeal R ^ 2 := by
  intro hmem
  have hz : (IsLocalRing.maximalIdeal R).toCotangent v -
      a • (IsLocalRing.maximalIdeal R).toCotangent u = 0 := by
    rw [← map_smul, ← map_sub, Ideal.toCotangent_eq_zero]
    exact hmem
  have hrel : (-(Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) a)) •
      (IsLocalRing.maximalIdeal R).toCotangent u +
      (1 : R ⧸ IsLocalRing.maximalIdeal R) •
        (IsLocalRing.maximalIdeal R).toCotangent v = 0 := by
    rw [neg_smul, one_smul]
    change -(a • (IsLocalRing.maximalIdeal R).toCotangent u) +
      (IsLocalRing.maximalIdeal R).toCotangent v = 0
    simpa only [sub_eq_neg_add] using hz
  exact one_ne_zero ((LinearIndependent.pair_iff.mp h) _ _ hrel).2

/-- A slice ideal contained in the ambient maximal ideal retains the
adapted equation as a nonzero class modulo the maximal ideal times itself.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Proposition 2.8;
Hartshorne, Algebraic Geometry, II.8. -/
theorem paired_c3_adapted_minimal
    {R : Type*} [CommRing R] [IsLocalRing R]
    (I : Ideal R) (hI : I ≤ IsLocalRing.maximalIdeal R)
    (u v : IsLocalRing.maximalIdeal R)
    (h : LinearIndependent (R ⧸ IsLocalRing.maximalIdeal R)
      ![(IsLocalRing.maximalIdeal R).toCotangent u,
        (IsLocalRing.maximalIdeal R).toCotangent v])
    (a : R) (ht : (v : R) - a * (u : R) ∈ I) :
    (⟨(v : R) - a * (u : R), ht⟩ : I) ∉
      IsLocalRing.maximalIdeal R • (⊤ : Submodule R I) := by
  intro hm
  apply paired_c3_adapted_not_mem_square u v h a
  have hmap := Submodule.mem_map_of_mem (f := I.subtype) hm
  rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype,
    Ideal.smul_eq_mul] at hmap
  rw [pow_two]
  exact (Ideal.mul_mono (le_refl (IsLocalRing.maximalIdeal R)) hI) hmap

#print axioms paired_c3_adapted_not_mem_square
#print axioms paired_c3_adapted_minimal
end HodgeLean.Foundations.Program.G32Native
