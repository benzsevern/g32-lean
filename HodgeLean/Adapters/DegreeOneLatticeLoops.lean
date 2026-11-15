import HodgeLean.Adapters.DegreeOneLatticeDefs

/-! # Loop periods: homotopy invariance, additivity and the coordinate torus

Helper lemmas for the degree-one period bridge. Periods along loops are invariant under
homotopy and natural for continuous maps; a translate of a loop in a path-connected group has the
same periods. Additivity in the loop is reduced to the 2-torus map `(s, t) ↦ p s + q t`, whose
diagonal is `p + q` and whose axes are translates of `p` and `q`; on the 2-torus the diagonal
period of a class is the sum of its axis periods because the coordinate classes form a basis.
HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Foundations HodgeLean.Foundations.Singular

namespace HodgeLean.Adapters

/-- Homotopic maps induce the same map on rational singular cohomology.
Source: Hatcher, *Algebraic Topology*, Theorem 2.10 and §3.1; Mathlib
`TopCat.Homotopy.singularChainComplexFunctorObjMap`. -/
theorem cohomologyMap_eq_of_homotopy {Y Z : TopCat.{0}} {f g : Y ⟶ Z}
    (H : TopCat.Homotopy f g) (n : ℕ) : cohomologyMap ℚ n f = cohomologyMap ℚ n g := by
  unfold cohomologyMap
  rw [(HomologicalComplex.linearDualHomotopy
    (H.singularChainComplexFunctorObjMap (ModuleCat.of ℚ ℚ))).homologyMap_eq n]

/-- Periods are natural: the period of a pullback along `f` is the period along `f ∘ p`.
Source: functoriality of singular cohomology. -/
theorem loopPeriod_comp {T U : Type} [TopologicalSpace T] [TopologicalSpace U] (f : C(T, U))
    (p : C(UnitAddCircle, T)) (x : Cohomology ℚ (TopCat.of U) 1) :
    loopPeriod (f.comp p) x = loopPeriod p (cohomologyMap ℚ 1 (TopCat.ofHom f) x) := by
  have h : TopCat.ofHom (f.comp p) = TopCat.ofHom p ≫ TopCat.ofHom f := rfl
  simp only [loopPeriod, LinearMap.comp_apply, h, cohomologyMap_comp]

/-- Homotopic loops have the same periods.
Source: Hatcher, *Algebraic Topology*, Theorem 2.10. -/
theorem loopPeriod_eq_of_homotopy {T : Type} [TopologicalSpace T] {p q : C(UnitAddCircle, T)}
    (H : ContinuousMap.Homotopy p q) : loopPeriod p = loopPeriod q := by
  have h := cohomologyMap_eq_of_homotopy (f := TopCat.ofHom p) (g := TopCat.ofHom q) H 1
  simp only [loopPeriod, h]

/-- A constant loop has zero periods: it factors through a point.
Source: Hatcher, *Algebraic Topology*, §3.1 (cohomology of a point). -/
theorem loopPeriod_const {T : Type} [TopologicalSpace T] (t : T) :
    loopPeriod (ContinuousMap.const UnitAddCircle t) = 0 := by
  ext x
  let f : C(UnitAddCircle, PUnit) := ContinuousMap.const _ PUnit.unit
  let g : C(PUnit, T) := ContinuousMap.const _ t
  have he : ContinuousMap.const UnitAddCircle t = g.comp f := rfl
  rw [he, loopPeriod_comp]
  let := ModuleCat.subsingleton_of_isZero (isZero_cohomology_succ_of_contractible PUnit 0)
  rw [Subsingleton.elim (cohomologyMap ℚ 1 (TopCat.ofHom g) x) 0, map_zero]
  rfl

/-- The identity loop has period one on `circleClass`.
Source: Hatcher, *Algebraic Topology*, §2.2 (degree of the identity). -/
theorem loopPeriod_id_circleClass : loopPeriod (ContinuousMap.id UnitAddCircle) circleClass = 1 := by
  have h : circleClass = circleClassBasis 0 := by simp [circleClassBasis]
  change circleDegree (cohomologyMap ℚ 1 (𝟙 (TopCat.of UnitAddCircle)) circleClass) = 1
  rw [cohomologyMap_id, LinearMap.id_apply, circleDegree, h, Module.Basis.coord_apply,
    Module.Basis.repr_self, Finsupp.single_eq_same]

/-- Translating a loop in a path-connected topological group does not change its periods.
Source: Hatcher, *Algebraic Topology*, Theorem 2.10 (homotopy along a path to `0`). -/
theorem loopPeriod_add_const {T : Type} [AddCommGroup T] [TopologicalSpace T]
    [IsTopologicalAddGroup T] [PathConnectedSpace T] (p : C(UnitAddCircle, T)) (c : T) :
    loopPeriod (p + ContinuousMap.const UnitAddCircle c) = loopPeriod p := by
  let γ : Path c 0 := PathConnectedSpace.somePath c 0
  let H : ContinuousMap.Homotopy (p + ContinuousMap.const UnitAddCircle c) p :=
    { toFun := fun x => p x.2 + γ x.1
      continuous_toFun := by fun_prop
      map_zero_left := fun z => by simp
      map_one_left := fun z => by simp }
  exact loopPeriod_eq_of_homotopy H

/-- The loop `z ↦ k • z` of the circle. -/
def circleZsmul (k : ℤ) : C(UnitAddCircle, UnitAddCircle) :=
  ⟨fun z => k • z, continuous_zsmul k⟩

/-- The coordinate `j` of the straight torus loop of `l` is `z ↦ l j • z`. -/
theorem torusCoordinate_comp_torusLoop {n : ℕ} (l : Fin n → ℤ) (j : Fin n) :
    (⟨fun t : UnitAddTorus (Fin n) => t j, continuous_apply j⟩ :
      C(UnitAddTorus (Fin n), UnitAddCircle)).comp (torusLoop l) = circleZsmul (l j) := rfl

/-- The period of a coordinate class along a straight loop is the degree of `z ↦ l j • z`. -/
theorem loopPeriod_torusLoop_coordinate {n : ℕ} (l : Fin n → ℤ) (j : Fin n) :
    loopPeriod (torusLoop l) (torusCoordinateClass j) =
      loopPeriod (circleZsmul (l j)) circleClass := by
  rw [← torusCoordinate_comp_torusLoop, loopPeriod_comp]
  rfl

theorem loopPeriod_circleZsmul_zero : loopPeriod (circleZsmul 0) circleClass = 0 := by
  have h : circleZsmul 0 = ContinuousMap.const UnitAddCircle 0 := by
    ext z; simp [circleZsmul]
  rw [h, loopPeriod_const]
  rfl

theorem loopPeriod_circleZsmul_one : loopPeriod (circleZsmul 1) circleClass = 1 := by
  have h : circleZsmul 1 = ContinuousMap.id UnitAddCircle := by
    ext z; simp [circleZsmul]
  rw [h, loopPeriod_id_circleClass]

/-- On the 2-torus, the period along the diagonal is the sum of the periods along the axes. -/
theorem loopPeriod_torusLoop_diagonal (y : Cohomology ℚ (TopCat.of (UnitAddTorus (Fin 2))) 1) :
    loopPeriod (torusLoop ![1, 1]) y =
      loopPeriod (torusLoop ![1, 0]) y + loopPeriod (torusLoop ![0, 1]) y := by
  rw [← (torusCoordinateBasis 2).sum_repr y, Fin.sum_univ_two]
  simp only [map_add, map_smul, torusCoordinateBasis_apply, loopPeriod_torusLoop_coordinate]
  simp [loopPeriod_circleZsmul_zero, loopPeriod_circleZsmul_one]

/-- The torus map `t ↦ p (t 0) + q (t 1)`. -/
def torusSumMap {T : Type} [AddCommGroup T] [TopologicalSpace T] [IsTopologicalAddGroup T]
    (p q : C(UnitAddCircle, T)) : C(UnitAddTorus (Fin 2), T) :=
  ⟨fun t => p (t 0) + q (t 1), by fun_prop⟩

/-- Additivity of periods in the loop, for a path-connected topological abelian group.
Source: Hatcher, *Algebraic Topology*, §3.C (H-spaces) and §3.1. -/
theorem loopPeriod_add {T : Type} [AddCommGroup T] [TopologicalSpace T]
    [IsTopologicalAddGroup T] [PathConnectedSpace T] (p q : C(UnitAddCircle, T)) :
    loopPeriod (p + q) = loopPeriod p + loopPeriod q := by
  ext x
  have h11 : (torusSumMap p q).comp (torusLoop ![1, 1]) = p + q := by
    ext z; simp [torusSumMap, torusLoop]
  have h10 : (torusSumMap p q).comp (torusLoop ![1, 0]) =
      p + ContinuousMap.const UnitAddCircle (q 0) := by
    ext z; simp [torusSumMap, torusLoop]
  have h01 : (torusSumMap p q).comp (torusLoop ![0, 1]) =
      q + ContinuousMap.const UnitAddCircle (p 0) := by
    ext z; simp [torusSumMap, torusLoop, add_comm]
  have hd := loopPeriod_torusLoop_diagonal
    (cohomologyMap ℚ 1 (TopCat.ofHom (torusSumMap p q)) x)
  rw [← loopPeriod_comp, ← loopPeriod_comp, ← loopPeriod_comp, h11, h10, h01,
    loopPeriod_add_const, loopPeriod_add_const] at hd
  simpa using hd

/-- The degree of `z ↦ k • z` is `k`.
Source: Hatcher, *Algebraic Topology*, §2.2 (degree of `z ↦ zᵏ`). -/
theorem loopPeriod_circleZsmul (k : ℤ) : loopPeriod (circleZsmul k) circleClass = k := by
  have hadd : ∀ a b : ℤ, circleZsmul (a + b) = circleZsmul a + circleZsmul b := by
    intro a b; ext z; simp [circleZsmul, add_zsmul]
  have hk : ∀ a b : ℤ, loopPeriod (circleZsmul (a + b)) circleClass =
      loopPeriod (circleZsmul a) circleClass + loopPeriod (circleZsmul b) circleClass := by
    intro a b
    rw [hadd, loopPeriod_add]
    rfl
  induction k using Int.induction_on with
  | zero => simpa using loopPeriod_circleZsmul_zero
  | succ k ih => rw [hk, ih, loopPeriod_circleZsmul_one]; push_cast; ring
  | pred k ih =>
    have h := hk (-(k : ℤ) - 1) 1
    rw [sub_add_cancel, ih, loopPeriod_circleZsmul_one] at h
    push_cast at h ⊢
    linarith

/-- The period of the coordinate class `j` along the straight loop of `l` is `l j`. -/
theorem torusPeriod_coordinate (n : ℕ) (j : Fin n) (l : Fin n → ℤ) :
    torusPeriod n (torusCoordinateClass j) l = l j := by
  change loopPeriod (torusLoop l) (torusCoordinateClass j) = l j
  rw [loopPeriod_torusLoop_coordinate, loopPeriod_circleZsmul]

/-- Periods on the coordinate torus in coordinates: `Σⱼ xⱼ lⱼ`. -/
theorem torusPeriod_eq_sum (n : ℕ) (x : Cohomology ℚ (TopCat.of (UnitAddTorus (Fin n))) 1)
    (l : Fin n → ℤ) :
    torusPeriod n x l = ∑ j, (torusCoordinateBasis n).repr x j * l j := by
  conv_lhs => rw [← (torusCoordinateBasis n).sum_repr x]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, torusCoordinateBasis_apply,
    torusPeriod_coordinate, smul_eq_mul]

end HodgeLean.Adapters
