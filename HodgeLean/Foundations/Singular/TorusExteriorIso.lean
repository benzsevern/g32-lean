import HodgeLean.Foundations.Singular.TorusExterior
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# C7 for rational singular cohomology of the model torus

The endpoint is degreewise linear equivalences compatible with cup and wedge,
including the unit. HC no distance; AV milestone no distance. This is a theorem
about `UnitAddTorus (Fin n)`, not `HQ` or abelian varieties. No stated hypothesis
is retired.
-/
noncomputable section
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Singular

private def torusDrop (n : ℕ) :
    TopCat.of (UnitAddTorus (Fin (n + 1))) ⟶ TopCat.of (UnitAddTorus (Fin n)) :=
  TopCat.ofHom ⟨fun t => (unitAddTorusSuccHomeomorph n t).1,
    continuous_fst.comp (unitAddTorusSuccHomeomorph n).continuous⟩

private def torusLast (n : ℕ) :
    TopCat.of (UnitAddTorus (Fin (n + 1))) ⟶ TopCat.of UnitAddCircle :=
  TopCat.ofHom ⟨fun t => (unitAddTorusSuccHomeomorph n t).2,
    continuous_snd.comp (unitAddTorusSuccHomeomorph n).continuous⟩

private theorem torus_product_decomposition (n m : ℕ)
    (c : Cohomology ℚ (TopCat.of (UnitAddTorus (Fin (n + 1)))) (m + 1)) :
    ∃ (a : Cohomology ℚ (TopCat.of (UnitAddTorus (Fin n))) (m + 1))
      (b : Cohomology ℚ (TopCat.of (UnitAddTorus (Fin n))) m),
      cohomologyMap ℚ (m + 1) (torusDrop n) a +
        cup (TopCat.of (UnitAddTorus (Fin (n + 1)))) rfl
          (cohomologyMap ℚ m (torusDrop n) b)
          (cohomologyMap ℚ 1 (torusLast n) circleClass) = c := by
  let e := cohomologyHomeomorphEquiv (unitAddTorusSuccHomeomorph n) (m + 1)
  obtain ⟨⟨a, b⟩, hab⟩ := (prodCircleCohomologyEquiv
    (TopCat.of (UnitAddTorus (Fin n))) m).surjective (e c)
  refine ⟨a, b, ?_⟩
  have he := congrArg e.symm hab
  rw [LinearEquiv.symm_apply_apply, prodCircleCohomologyEquiv_apply] at he
  change cohomologyMap ℚ (m + 1)
    (TopCat.ofHom ⟨unitAddTorusSuccHomeomorph n, (unitAddTorusSuccHomeomorph n).continuous⟩)
    (_ + _) = c at he
  rw [map_add, cohomologyMap_cup] at he
  simp only [← LinearMap.comp_apply, ← cohomologyMap_comp] at he
  exact he

private theorem wedge_zero_surjective (n : ℕ) : Function.Surjective (wedgeToCohomology n 0) := by
  let := finite_cohomology_unitAddTorus n 0
  intro c
  obtain ⟨r, hr⟩ := (finrank_eq_one_iff_of_nonzero'
    (unit (R := ℚ) (TopCat.of (UnitAddTorus (Fin n)))) (unit_ne_zero _)).mp
      (by simpa using finrank_cohomology_unitAddTorus n 0) c
  refine ⟨r • exteriorPower.ιMulti ℚ 0 Fin.elim0, ?_⟩
  rw [map_smul, wedgeToCohomology_zero, hr]

/-- The wedge map is onto, by the circle-product equivalence in every positive
degree, with the empty product supplying degree zero.
Source: Hatcher, *Algebraic Topology*, Example 3.11 and Theorem 3.15; constructed
here by induction through S4 and `unitAddTorusSuccHomeomorph`.
-/
theorem wedgeToCohomology_surjective (n m : ℕ) :
    Function.Surjective (wedgeToCohomology n m) := by
  induction n generalizing m with
  | zero =>
    cases m with
    | zero => exact wedge_zero_surjective 0
    | succ m =>
      let := ModuleCat.subsingleton_of_isZero
        (isZero_cohomology_succ_of_contractible (UnitAddTorus (Fin 0)) m)
      intro c
      exact ⟨0, Subsingleton.elim _ _⟩
  | succ n ih =>
    cases m with
    | zero => exact wedge_zero_surjective (n + 1)
    | succ m =>
      intro c
      obtain ⟨a, b, hab⟩ := torus_product_decomposition n m c
      obtain ⟨α, hα⟩ := ih (m + 1) a
      obtain ⟨β, hβ⟩ := ih m b
      let x := cohomologyMap ℚ 1 (torusLast n) circleClass
      refine ⟨exteriorPower.map (m + 1) (cohomologyMap ℚ 1 (torusDrop n)) α +
        exteriorPower.wedge ℚ _ m 1
          (exteriorPower.map m (cohomologyMap ℚ 1 (torusDrop n)) β)
          (exteriorPower.ιMulti ℚ 1 (fun _ => x)), ?_⟩
      rw [map_add, wedgeToCohomology_wedge, wedgeToCohomology_naturality,
        wedgeToCohomology_naturality, wedgeToCohomology_single, hα, hβ]
      exact hab

/-- C7 for the model torus: the specified singular wedge map is bijective in
every degree. T11 supplies the dimension `n.choose m` on both sides.
Source: Hatcher, *Algebraic Topology*, Example 3.11 and Theorem 3.15.
HC no distance; AV milestone no distance. No stated hypothesis is retired.
-/
theorem wedgeToCohomology_bijective (n m : ℕ) :
    Function.Bijective (wedgeToCohomology n m) := by
  let := finite_cohomology_unitAddTorus n 1
  let := finite_cohomology_unitAddTorus n m
  have hd : Module.finrank ℚ (⋀[ℚ]^m (Cohomology ℚ (TopCat.of (UnitAddTorus (Fin n))) 1)) =
      Module.finrank ℚ (Cohomology ℚ (TopCat.of (UnitAddTorus (Fin n))) m) := by
    rw [exteriorPower.finrank_eq, finrank_cohomology_one_unitAddTorus,
      finrank_cohomology_unitAddTorus]
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mpr
    (wedgeToCohomology_surjective n m), wedgeToCohomology_surjective n m⟩

/-- The degreewise C7 equivalence for the model torus, given by cup products.
Source: Hatcher, *Algebraic Topology*, Example 3.11 and Theorem 3.15.
HC no distance; AV milestone no distance. This retires no stated hypothesis.
-/
def torusWedgeEquiv (n m : ℕ) :
    (⋀[ℚ]^m (Cohomology ℚ (TopCat.of (UnitAddTorus (Fin n))) 1)) ≃ₗ[ℚ]
      Cohomology ℚ (TopCat.of (UnitAddTorus (Fin n))) m :=
  LinearEquiv.ofBijective (wedgeToCohomology n m) (wedgeToCohomology_bijective n m)

/-- The degreewise equivalence is exactly the wedge map constructed from cups.
Source: constructed here for the degreewise model-torus C7 interface.
-/
theorem torusWedgeEquiv_apply (n m : ℕ)
    (v : ⋀[ℚ]^m (Cohomology ℚ (TopCat.of (UnitAddTorus (Fin n))) 1)) :
    torusWedgeEquiv n m v = wedgeToCohomology n m v := rfl

/-- The degreewise C7 equivalences preserve multiplication in all bidegrees.
Source: Hatcher, *Algebraic Topology*, Example 3.11 and Theorem 3.15;
constructed here from the multiplicative singular wedge map.
-/
theorem torusWedgeEquiv_wedge (n p q : ℕ)
    (v : ⋀[ℚ]^p (Cohomology ℚ (TopCat.of (UnitAddTorus (Fin n))) 1))
    (w : ⋀[ℚ]^q (Cohomology ℚ (TopCat.of (UnitAddTorus (Fin n))) 1)) :
    torusWedgeEquiv n (p + q) (exteriorPower.wedge ℚ _ p q v w) =
      cup (TopCat.of (UnitAddTorus (Fin n))) rfl
        (torusWedgeEquiv n p v) (torusWedgeEquiv n q w) :=
  wedgeToCohomology_wedge n p q v w

example (n : ℕ) : torusWedgeEquiv n 0 (exteriorPower.ιMulti ℚ 0 Fin.elim0) =
    unit (R := ℚ) (TopCat.of (UnitAddTorus (Fin n))) := wedgeToCohomology_zero n

/-- Increasing coordinate cup monomials form a basis in every degree.
Source: Hatcher, *Algebraic Topology*, Example 3.11 and Theorem 3.15; the
circle-factor induction proves surjectivity and T11 proves independence.
-/
def torusMonomialBasis (n m : ℕ) :
    Module.Basis (Set.powersetCard (Fin n) m) ℚ
      (Cohomology ℚ (TopCat.of (UnitAddTorus (Fin n))) m) :=
  ((torusCoordinateBasis n).exteriorPower m).map (torusWedgeEquiv n m)

/-- Each basis vector is the ordered cup product of the coordinates in its index set.
Source: constructed here from the exterior-power basis and the singular wedge map.
-/
theorem torusMonomialBasis_apply (n m : ℕ) (I : Set.powersetCard (Fin n) m) :
    torusMonomialBasis n m I = cupMulti (TopCat.of (UnitAddTorus (Fin n))) m
      (fun j => torusCoordinateClass (Set.powersetCard.ofFinEmbEquiv.symm I j)) := by
  simp only [torusMonomialBasis, Module.Basis.map_apply, exteriorPower.basis_apply,
    exteriorPower.ιMulti_family, torusWedgeEquiv_apply, wedgeToCohomology_ιMulti,
    Function.comp_def, torusCoordinateBasis_apply]

example (n m : ℕ) : LinearIndependent ℚ (torusMonomialBasis n m) :=
  (torusMonomialBasis n m).linearIndependent

#print axioms torusWedgeEquiv
#print axioms torusWedgeEquiv_apply
#print axioms torusWedgeEquiv_wedge
#print axioms torusMonomialBasis
#print axioms torusMonomialBasis_apply
#print axioms wedgeToCohomology_surjective
#print axioms wedgeToCohomology_bijective

end HodgeLean.Foundations.Singular
