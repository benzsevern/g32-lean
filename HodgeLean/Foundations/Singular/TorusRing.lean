import HodgeLean.Foundations.Singular.CircleProductChecks
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Coordinate classes of the model torus

Rational singular cohomology of `UnitAddTorus (Fin n)`.
HC no distance; AV milestone no distance. These constructions concern the model
torus only, not `HQ` or abelian varieties, and retire no stated hypothesis.
-/

noncomputable section
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Singular

/-- The pullback of the normalized circle generator along coordinate `i`.
Source: Hatcher, *Algebraic Topology*, Example 3.11 and Theorem 3.15.
-/
def torusCoordinateClass {n : ℕ} (i : Fin n) :
    Cohomology ℚ (TopCat.of (UnitAddTorus (Fin n))) 1 :=
  cohomologyMap ℚ 1 (TopCat.ofHom ⟨fun t => t i, continuous_apply i⟩) circleClass

example {n : ℕ} (i : Fin n) : torusCoordinateClass i =
    cohomologyMap ℚ 1 (TopCat.ofHom ⟨fun t : UnitAddTorus (Fin n) => t i,
      continuous_apply i⟩) circleClass := rfl

/-- The first Betti number of the model torus, by induction with the S4 cup-product equivalence.
Source: Hatcher, *Algebraic Topology*, Example 3.11 and Theorem 3.15.
-/
theorem finrank_cohomology_one_unitAddTorus (n : ℕ) :
    Module.finrank ℚ (Cohomology ℚ (TopCat.of (UnitAddTorus (Fin n))) 1) = n := by
  induction n with
  | zero => simpa using finrank_cohomology_of_contractible (UnitAddTorus (Fin 0)) 1
  | succ n ih =>
    let := finite_cohomology_unitAddTorus n 1
    let := finite_cohomology_unitAddTorus n 0
    rw [(cohomologyHomeomorphEquiv (unitAddTorusSuccHomeomorph n) 1).finrank_eq,
      ← (prodCircleCohomologyEquiv (TopCat.of (UnitAddTorus (Fin n))) 0).finrank_eq,
      Module.finrank_prod, ih, finrank_cohomology_zero_of_pathConnected]

example : Module.finrank ℚ (Cohomology ℚ (TopCat.of (UnitAddTorus (Fin 2))) 1) = 2 :=
  finrank_cohomology_one_unitAddTorus 2

private def torusAxis {n : ℕ} (i : Fin n) :
    TopCat.of UnitAddCircle ⟶ TopCat.of (UnitAddTorus (Fin n)) :=
  TopCat.ofHom ⟨fun z j => if j = i then z else 0,
    continuous_pi fun j => by split_ifs <;> fun_prop⟩

private theorem constant_pullback_one (Y : TopCat.{0}) (z : UnitAddCircle) :
    cohomologyMap ℚ 1 (TopCat.ofHom ⟨fun _ : Y => z, continuous_const⟩) circleClass = 0 := by
  let f : Y ⟶ TopCat.of PUnit := TopCat.ofHom ⟨fun _ => PUnit.unit, continuous_const⟩
  let g : TopCat.of PUnit ⟶ TopCat.of UnitAddCircle :=
    TopCat.ofHom ⟨fun _ => z, continuous_const⟩
  have he : TopCat.ofHom ⟨fun _ : Y => z, continuous_const⟩ = f ≫ g := rfl
  rw [he, cohomologyMap_comp, LinearMap.comp_apply]
  let := ModuleCat.subsingleton_of_isZero (isZero_cohomology_succ_of_contractible PUnit 0)
  rw [Subsingleton.elim (cohomologyMap ℚ 1 g circleClass) 0, map_zero]

private theorem torusAxis_coordinate {n : ℕ} (i j : Fin n) :
    cohomologyMap ℚ 1 (torusAxis i) (torusCoordinateClass j) =
      if j = i then circleClass else 0 := by
  unfold torusCoordinateClass
  rw [← LinearMap.comp_apply, ← cohomologyMap_comp]
  by_cases h : j = i
  · subst j
    have he : torusAxis i ≫ TopCat.ofHom ⟨fun t : UnitAddTorus (Fin n) => t i,
        continuous_apply i⟩ = 𝟙 _ := by ext z; simp [torusAxis]
    rw [he, cohomologyMap_id]
    simp
  · have he : torusAxis i ≫ TopCat.ofHom ⟨fun t : UnitAddTorus (Fin n) => t j,
        continuous_apply j⟩ = TopCat.ofHom ⟨fun _ => 0, continuous_const⟩ := by
      ext z; simp [torusAxis, h]
    rw [he, ite_eq_right h]
    exact constant_pullback_one (TopCat.of UnitAddCircle) 0

private theorem torusCoordinates_independent (n : ℕ) :
    LinearIndependent ℚ (torusCoordinateClass (n := n)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have he := congrArg (cohomologyMap ℚ 1 (torusAxis i)) hc
  simp only [map_sum, map_smul, torusAxis_coordinate, map_zero] at he
  have hz : c i • circleClass = 0 := by simpa using he
  exact (smul_eq_zero.mp hz).resolve_right circleClass_ne_zero

/-- The coordinate pullbacks form a basis of degree-one rational cohomology.
Source: Hatcher, *Algebraic Topology*, Example 3.11; axis restrictions detect
independence and the circle-factor Betti induction gives the dimension.
-/
def torusCoordinateBasis (n : ℕ) :
    Module.Basis (Fin n) ℚ (Cohomology ℚ (TopCat.of (UnitAddTorus (Fin n))) 1) := by
  letI := finite_cohomology_unitAddTorus n 1
  exact basisOfLinearIndependentOfCardEqFinrank' _ (torusCoordinates_independent n)
    (by simpa using (finrank_cohomology_one_unitAddTorus n).symm)

/-- The coordinate basis is normalized by the chosen circle generator.
Source: constructed here for the coordinate basis of the model torus.
-/
theorem torusCoordinateBasis_apply {n : ℕ} (i : Fin n) :
    torusCoordinateBasis n i = torusCoordinateClass i := by
  simp [torusCoordinateBasis, coe_basisOfLinearIndependentOfCardEqFinrank']

example : torusCoordinateBasis 2 0 = torusCoordinateClass 0 := torusCoordinateBasis_apply 0

/-- The circle generator has zero square since the circle has no degree-two cohomology.
Source: Hatcher, *Algebraic Topology*, Example 3.11.
-/
theorem circleClass_square_zero : cup (TopCat.of UnitAddCircle) rfl circleClass circleClass = 0 := by
  let := ModuleCat.subsingleton_of_isZero (isZero_cohomology_circle_add_two 0)
  exact Subsingleton.elim _ _

example : cup (TopCat.of UnitAddCircle) (show 1 + 1 = 2 from rfl) circleClass circleClass = 0 :=
  circleClass_square_zero

/-- Every coordinate generator of the model torus has zero square, by naturality.
Source: Hatcher, *Algebraic Topology*, Example 3.11 and Theorem 3.15.
-/
theorem torusCoordinateClass_square_zero {n : ℕ} (i : Fin n) :
    cup (TopCat.of (UnitAddTorus (Fin n))) rfl
      (torusCoordinateClass i) (torusCoordinateClass i) = 0 := by
  unfold torusCoordinateClass
  rw [← cohomologyMap_cup, circleClass_square_zero, map_zero]

example : cup (TopCat.of (UnitAddTorus (Fin 2))) rfl
    (torusCoordinateClass 0) (torusCoordinateClass 0) = 0 := torusCoordinateClass_square_zero 0

private theorem torusAxis_apply {n : ℕ}
    (a : Cohomology ℚ (TopCat.of (UnitAddTorus (Fin n))) 1) (i : Fin n) :
    cohomologyMap ℚ 1 (torusAxis i) a = (torusCoordinateBasis n).repr a i • circleClass := by
  conv_lhs => rw [← (torusCoordinateBasis n).sum_repr a]
  simp [torusCoordinateBasis_apply, torusAxis_coordinate]

private theorem torusAxis_ext {n : ℕ}
    (a b : Cohomology ℚ (TopCat.of (UnitAddTorus (Fin n))) 1)
    (h : ∀ i, cohomologyMap ℚ 1 (torusAxis i) a = cohomologyMap ℚ 1 (torusAxis i) b) :
    a = b := by
  apply (torusCoordinateBasis n).repr.injective
  ext i
  have he := h i
  rw [torusAxis_apply, torusAxis_apply] at he
  exact (smul_left_injective ℚ circleClass_ne_zero) he

private def torusTwoAddition : TopCat.of (UnitAddTorus (Fin 2)) ⟶ TopCat.of UnitAddCircle :=
  TopCat.ofHom ⟨fun t => t 0 + t 1, (continuous_apply 0).add (continuous_apply 1)⟩

private theorem torusTwoAddition_class :
    cohomologyMap ℚ 1 torusTwoAddition circleClass =
      torusCoordinateClass 0 + torusCoordinateClass 1 := by
  apply torusAxis_ext
  intro i
  rw [← LinearMap.comp_apply, ← cohomologyMap_comp, map_add,
    torusAxis_coordinate, torusAxis_coordinate]
  have he : torusAxis i ≫ torusTwoAddition = 𝟙 _ := by
    fin_cases i <;> ext z <;> simp [torusAxis, torusTwoAddition]
  rw [he, cohomologyMap_id]
  fin_cases i <;> simp

private theorem torusTwo_anticomm :
    cup (TopCat.of (UnitAddTorus (Fin 2))) rfl (torusCoordinateClass 0) (torusCoordinateClass 1) =
      -cup (TopCat.of (UnitAddTorus (Fin 2))) rfl (torusCoordinateClass 1) (torusCoordinateClass 0) := by
  have he := congrArg (cohomologyMap ℚ 2 torusTwoAddition) circleClass_square_zero
  rw [cohomologyMap_cup, torusTwoAddition_class, map_zero] at he
  simp only [map_add, LinearMap.add_apply, torusCoordinateClass_square_zero, zero_add, add_zero] at he
  exact eq_neg_of_add_eq_zero_right he

private def torusPair {n : ℕ} (i j : Fin n) :
    TopCat.of (UnitAddTorus (Fin n)) ⟶ TopCat.of (UnitAddTorus (Fin 2)) :=
  TopCat.ofHom ⟨fun t => ![t i, t j], continuous_pi fun k => by fin_cases k <;> fun_prop⟩

private theorem torusPair_coordinate {n : ℕ} (i j : Fin n) (k : Fin 2) :
    cohomologyMap ℚ 1 (torusPair i j) (torusCoordinateClass k) =
      torusCoordinateClass (![i, j] k) := by
  unfold torusCoordinateClass
  rw [← LinearMap.comp_apply, ← cohomologyMap_comp]
  congr 1
  fin_cases k <;> rfl

/-- Degree-one coordinate classes anticommute. The proof pulls back the
two-torus addition-map argument, and does not use general graded commutativity.
Source: Hatcher, *Algebraic Topology*, Example 3.11; constructed here using the
addition map and axis restrictions as in `docs/roadmap/torus-track.md`, §4.
-/
theorem torusCoordinateClass_anticomm {n : ℕ} (i j : Fin n) :
    cup (TopCat.of (UnitAddTorus (Fin n))) rfl (torusCoordinateClass i) (torusCoordinateClass j) =
      -cup (TopCat.of (UnitAddTorus (Fin n))) rfl (torusCoordinateClass j) (torusCoordinateClass i) := by
  have he := congrArg (cohomologyMap ℚ 2 (torusPair i j)) torusTwo_anticomm
  simpa only [cohomologyMap_cup, map_neg, torusPair_coordinate, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons] using he

example : cup (TopCat.of (UnitAddTorus (Fin 2))) rfl (torusCoordinateClass 0) (torusCoordinateClass 1) =
    -cup (TopCat.of (UnitAddTorus (Fin 2))) rfl (torusCoordinateClass 1) (torusCoordinateClass 0) :=
  torusCoordinateClass_anticomm 0 1

/-- All degree-one rational classes on the model torus anticommute.
Source: constructed here by bilinearity from the coordinate-basis relations
of Hatcher, *Algebraic Topology*, Example 3.11.
-/
theorem torus_cup_comm_one (n : ℕ) {k : ℕ} (h : 1 + 1 = k)
    (a b : Cohomology ℚ (TopCat.of (UnitAddTorus (Fin n))) 1) :
    cup (TopCat.of (UnitAddTorus (Fin n))) h a b =
      -cup (TopCat.of (UnitAddTorus (Fin n))) h b a := by
  subst k
  have he : cup (R := ℚ) (TopCat.of (UnitAddTorus (Fin n))) (show 1 + 1 = 2 from rfl) =
      -(cup (R := ℚ) (TopCat.of (UnitAddTorus (Fin n))) (show 1 + 1 = 2 from rfl)).flip := by
    apply (torusCoordinateBasis n).ext
    intro i
    apply (torusCoordinateBasis n).ext
    intro j
    change cup _ rfl (torusCoordinateBasis n i) (torusCoordinateBasis n j) =
      -cup _ rfl (torusCoordinateBasis n j) (torusCoordinateBasis n i)
    rw [torusCoordinateBasis_apply, torusCoordinateBasis_apply]
    exact torusCoordinateClass_anticomm i j
  exact congrArg (fun f => f a b) he

example (a b : Cohomology ℚ (TopCat.of (UnitAddTorus (Fin 2))) 1) :
    cup (TopCat.of (UnitAddTorus (Fin 2))) rfl a b =
      -cup (TopCat.of (UnitAddTorus (Fin 2))) rfl b a := torus_cup_comm_one 2 rfl a b

/-- Every degree-one rational class on the model torus has zero square.
Source: constructed here from degree-one anticommutation in characteristic zero;
Hatcher, *Algebraic Topology*, Example 3.11.
-/
theorem torus_cup_self_eq_zero (n : ℕ) {k : ℕ} (h : 1 + 1 = k)
    (a : Cohomology ℚ (TopCat.of (UnitAddTorus (Fin n))) 1) :
    cup (TopCat.of (UnitAddTorus (Fin n))) h a a = 0 := by
  have he := torus_cup_comm_one n h a a
  have h2 : (2 : ℚ) • cup (TopCat.of (UnitAddTorus (Fin n))) h a a = 0 := by
    rw [two_smul]
    nth_rewrite 1 [he]
    exact neg_add_cancel _
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

example (a : Cohomology ℚ (TopCat.of (UnitAddTorus (Fin 2))) 1) :
    cup (TopCat.of (UnitAddTorus (Fin 2))) rfl a a = 0 := torus_cup_self_eq_zero 2 rfl a

#print axioms torus_cup_comm_one
#print axioms torus_cup_self_eq_zero
#print axioms torusCoordinateClass_anticomm
#print axioms circleClass_square_zero
#print axioms torusCoordinateClass_square_zero
#print axioms torusCoordinateBasis
#print axioms torusCoordinateBasis_apply
#print axioms finrank_cohomology_one_unitAddTorus

end HodgeLean.Foundations.Singular
