import HodgeLean.Foundations.Singular.TorusExteriorIso

/-!
# Falsification checks for the model-torus ring calculation

HC no distance; AV milestone no distance. These are rational singular cohomology
checks on the model torus, not statements about `HQ` or abelian varieties.
-/
noncomputable section
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Singular

/-- The ordered product of all coordinate classes is a nonzero top class.
Source: Hatcher, *Algebraic Topology*, Example 3.11 and Theorem 3.15;
detected here by the monomial basis obtained from S4.
-/
theorem torus_top_cupMulti_ne_zero (n : ℕ) :
    cupMulti (TopCat.of (UnitAddTorus (Fin n))) n torusCoordinateClass ≠ 0 := by
  let I : Set.powersetCard (Fin n) n :=
    Set.powersetCard.ofFinEmbEquiv (OrderEmbedding.id (Fin n))
  have he := (torusMonomialBasis n n).ne_zero I
  rw [torusMonomialBasis_apply] at he
  simpa only [I, Equiv.symm_apply_apply, OrderEmbedding.coe_id, id_eq] using he

/-- The two coordinate classes have nonzero product in `H²(T²; ℚ)`.
Source: Hatcher, *Algebraic Topology*, Example 3.11; the top monomial basis vector.
-/
theorem torus_coordinate_two_cup_ne_zero :
    cup (TopCat.of (UnitAddTorus (Fin 2))) rfl
      (torusCoordinateClass 0) (torusCoordinateClass 1) ≠ 0 := by
  have he := torus_top_cupMulti_ne_zero 2
  rw [cupMulti_succ _ 1 rfl, cupMulti_succ _ 0 rfl, cupMulti_zero, cup_one] at he
  exact he

/-- The three coordinate classes have nonzero product in `H³(T³; ℚ)`.
Source: Hatcher, *Algebraic Topology*, Example 3.11; the top monomial basis vector.
-/
theorem torus_coordinate_three_cup_ne_zero :
    cup (TopCat.of (UnitAddTorus (Fin 3))) rfl
      (cup (TopCat.of (UnitAddTorus (Fin 3))) rfl
        (torusCoordinateClass 0) (torusCoordinateClass 1)) (torusCoordinateClass 2) ≠ 0 := by
  have he := torus_top_cupMulti_ne_zero 3
  rw [cupMulti_succ _ 2 rfl, cupMulti_succ _ 1 rfl, cupMulti_succ _ 0 rfl,
    cupMulti_zero, cup_one] at he
  rw [cup_assoc _ rfl rfl rfl rfl]
  exact he

/-- Every class above the dimension of the model torus is zero.
Source: Hatcher, *Algebraic Topology*, Example 3.11; T11 and finite dimensionality.
-/
theorem torus_cohomology_eq_zero_of_dimension_lt (n m : ℕ) (h : n < m)
    (a : Cohomology ℚ (TopCat.of (UnitAddTorus (Fin n))) m) : a = 0 := by
  let := finite_cohomology_unitAddTorus n m
  have hd : Module.finrank ℚ (Cohomology ℚ (TopCat.of (UnitAddTorus (Fin n))) m) = 0 := by
    rw [finrank_cohomology_unitAddTorus, Nat.choose_eq_zero_of_lt h]
  let := (Module.finrank_eq_zero_iff_of_free ℚ _).mp hd
  exact Subsingleton.elim _ _

example : cup (TopCat.of (UnitAddTorus (Fin 2))) rfl
    (torusCoordinateClass 0) (torusCoordinateClass 1) ≠ 0 := torus_coordinate_two_cup_ne_zero

example : cup (TopCat.of (UnitAddTorus (Fin 3))) rfl
    (cup (TopCat.of (UnitAddTorus (Fin 3))) rfl (torusCoordinateClass 0) (torusCoordinateClass 1))
    (torusCoordinateClass 2) ≠ 0 := torus_coordinate_three_cup_ne_zero

example (a : Cohomology ℚ (TopCat.of (UnitAddTorus (Fin 2))) 3) : a = 0 :=
  torus_cohomology_eq_zero_of_dimension_lt 2 3 (by decide) a

example (a b c : Cohomology ℚ (TopCat.of (UnitAddTorus (Fin 2))) 1) :
    cup (TopCat.of (UnitAddTorus (Fin 2))) rfl
      (cup (TopCat.of (UnitAddTorus (Fin 2))) rfl a b) c = 0 :=
  torus_cohomology_eq_zero_of_dimension_lt 2 3 (by decide) _

example : cup (TopCat.of (UnitAddTorus (Fin 2))) rfl
    (torusCoordinateClass 0) (torusCoordinateClass 0) = 0 := torusCoordinateClass_square_zero 0

#print axioms torus_top_cupMulti_ne_zero
#print axioms torus_coordinate_two_cup_ne_zero
#print axioms torus_coordinate_three_cup_ne_zero
#print axioms torus_cohomology_eq_zero_of_dimension_lt

end HodgeLean.Foundations.Singular
