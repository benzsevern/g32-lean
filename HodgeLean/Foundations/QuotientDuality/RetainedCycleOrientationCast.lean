import HodgeLean.Foundations.QuotientDuality.ProperCycleLocalOrientationDegree

/-! # Inverse degree transport of the specified local orientation

HC no distance; AV milestone no distance.
-/
noncomputable section
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Undoing the degree cast retains the specified local orientation class. -/
theorem retained_local_orientation_normalization_uncast
    (X : TopCat.{0}) (n m : ℕ) (h : n = m) (c : Homology ℚ X m)
    (x : X) (z : orientationGroup X n x)
    (hc : localOrientation X m c x = h ▸ z) :
    localOrientation X n (h.symm ▸ c) x = z := by
  subst m
  exact hc

/-- Literal ambient degree transport retains bijectivity of every orientation line. -/
theorem retained_orientation_line_bijective_cast
    (X : TopCat.{0}) (n m : ℕ) (h : n = m) (c : Homology ℚ X n)
    (ho : ∀ x, Function.Bijective (orientationLine X n c x)) :
    ∀ x, Function.Bijective (orientationLine X m
      ((eqToIso (congrArg (fun j => Homology ℚ X j) h)).hom.hom c) x) := by
  subst m
  exact ho

/-- The homology equality isomorphism acts by the literal transport of the degree. -/
theorem retained_homology_degree_iso_apply
    (X : TopCat.{0}) (n m : ℕ) (h : n = m) (c : Homology ℚ X n) :
    (eqToIso (congrArg (fun j => Homology ℚ X j) h)).hom.hom c = h ▸ c := by
  subst m
  rfl

end HodgeLean.Foundations.QuotientDuality
