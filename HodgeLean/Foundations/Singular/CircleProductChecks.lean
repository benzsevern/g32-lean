import HodgeLean.Foundations.Singular.TorusBetti

/-!
# Checks of the circle product theorem

The equivalence recovers the Betti recurrence and detects the nonzero product of
both circle generators on the two-torus. HC no distance; AV milestone no distance.
Together with S5, S4 supplies C7 for the model torus; no hypothesis is retired.
-/

noncomputable section
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Singular

/-- The product equivalence recovers the previously established Betti recurrence.
Source: Hatcher, *Algebraic Topology*, Theorem 3.15; constructed here from S4.
-/
theorem finrank_cohomology_prod_circle_from_equiv (Y : TopCat.{0})
    [∀ k, FiniteDimensional ℚ (Cohomology ℚ Y k)] (n : ℕ) :
    Module.finrank ℚ (Cohomology ℚ (TopCat.of (Y × UnitAddCircle)) (n + 1)) =
      Module.finrank ℚ (Cohomology ℚ Y (n + 1)) + Module.finrank ℚ (Cohomology ℚ Y n) := by
  rw [← (prodCircleCohomologyEquiv Y n).finrank_eq, Module.finrank_prod]

example (Y : TopCat.{0}) [∀ k, FiniteDimensional ℚ (Cohomology ℚ Y k)] (n : ℕ) :
    finrank_cohomology_prod_circle_from_equiv Y n = finrank_cohomology_prod_circle Y n := rfl

/-- For the point, the second summand's unit maps to the pulled-back circle generator.
Source: constructed here to check the normalization of the S4 product equivalence.
-/
theorem prodCircleCohomologyEquiv_point_generator :
    prodCircleCohomologyEquiv (TopCat.of PUnit) 0 (0, unit (R := ℚ) (TopCat.of PUnit)) =
      cohomologyMap ℚ 1 (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩) circleClass := by
  rw [prodCircleCohomologyEquiv_apply]
  simp only [map_zero, zero_add, cohomologyMap_unit, one_cup]

/-- The point check is nonzero, so the normalization cannot collapse the circle class.
Source: constructed here from injectivity of the S4 product equivalence.
-/
theorem point_prod_circle_generator_ne_zero :
    cohomologyMap ℚ 1
      (TopCat.ofHom (X := TopCat.of (PUnit × UnitAddCircle)) ⟨Prod.snd, continuous_snd⟩)
      circleClass ≠ 0 := by
  rw [← prodCircleCohomologyEquiv_point_generator]
  intro h
  have hz := (prodCircleCohomologyEquiv (TopCat.of PUnit) 0).injective
    (h.trans (map_zero _).symm)
  exact unit_ne_zero (TopCat.of PUnit) (congrArg Prod.snd hz)

example : prodCircleCohomologyEquiv (TopCat.of PUnit) 0
    (0, unit (R := ℚ) (TopCat.of PUnit)) ≠ 0 := by
  rw [prodCircleCohomologyEquiv_point_generator]
  exact point_prod_circle_generator_ne_zero

/-- The second circle generator gives the product orientation class on the two-torus.
Source: Hatcher, *Algebraic Topology*, §3.2, cup products on products of circles.
-/
theorem prodCircleCohomologyEquiv_circle_generator :
    prodCircleCohomologyEquiv (TopCat.of UnitAddCircle) 1 (0, circleClass) =
      cup (TopCat.of (UnitAddCircle × UnitAddCircle)) rfl
        (cohomologyMap ℚ 1 (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩) circleClass)
        (cohomologyMap ℚ 1 (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩) circleClass) := by
  rw [prodCircleCohomologyEquiv_apply, map_zero, zero_add]

/-- Explicit nonvanishing of the cup product of the two degree-one circle classes.
Source: Hatcher, *Algebraic Topology*, §3.2; detected here by the S4 equivalence.
HC no distance; AV milestone no distance.
-/
theorem torus_two_circle_cup_ne_zero :
    cup (TopCat.of (UnitAddCircle × UnitAddCircle)) rfl
      (cohomologyMap ℚ 1 (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩) circleClass)
      (cohomologyMap ℚ 1 (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩) circleClass) ≠ 0 := by
  rw [← prodCircleCohomologyEquiv_circle_generator]
  intro h
  have hz := (prodCircleCohomologyEquiv (TopCat.of UnitAddCircle) 1).injective
    (h.trans (map_zero _).symm)
  exact circleClass_ne_zero (congrArg Prod.snd hz)

example : prodCircleCohomologyEquiv (TopCat.of UnitAddCircle) 1 (0, circleClass) ≠ 0 := by
  rw [prodCircleCohomologyEquiv_circle_generator]
  exact torus_two_circle_cup_ne_zero

#print axioms finrank_cohomology_prod_circle_from_equiv
#print axioms prodCircleCohomologyEquiv_point_generator
#print axioms point_prod_circle_generator_ne_zero
#print axioms prodCircleCohomologyEquiv_circle_generator
#print axioms torus_two_circle_cup_ne_zero

end HodgeLean.Foundations.Singular
