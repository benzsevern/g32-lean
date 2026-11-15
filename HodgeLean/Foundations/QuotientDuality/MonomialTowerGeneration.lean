import Mathlib.RingTheory.Adjoin.Basic

/-! Combining the coordinate-root and unit-root generating sets through an algebra tower. -/
noncomputable section
set_option maxHeartbeats 200000
namespace HodgeLean.Foundations.QuotientDuality

theorem adjoin_tower_roots_eq_top
    {R T A ι : Type*} [CommRing R] [CommRing T] [CommRing A]
    [Algebra R T] [Algebra T A] [Algebra R A] [IsScalarTower R T A]
    (W : ι → T) (U : A)
    (hW : Algebra.adjoin R (Set.range W) = ⊤)
    (hU : Algebra.adjoin T ({U} : Set A) = ⊤) :
    Algebra.adjoin R (Set.range (fun j => algebraMap T A (W j)) ∪ {U}) = ⊤ := by
  have H := Algebra.adjoin_eq_adjoin_union R (Set.range W) ({U} : Set A) hW
  rw [hU] at H
  have he : algebraMap T A '' Set.range W = Set.range (fun j => algebraMap T A (W j)) := by
    ext x
    constructor
    · rintro ⟨y, ⟨j, rfl⟩, rfl⟩
      exact ⟨j, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨W j, ⟨j, rfl⟩, rfl⟩
  rw [he] at H
  simpa only [Subalgebra.restrictScalars_top] using H.symm

#print axioms adjoin_tower_roots_eq_top
end HodgeLean.Foundations.QuotientDuality
