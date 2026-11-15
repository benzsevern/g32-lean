import HodgeLean.Foundations.RationalHomologyManifold.RelativeSubdivisionHomotopy
import HodgeLean.Foundations.RationalHomologyManifold.SubdivisionSmallChains

/-! Actual relative subdivision iterates and their effect on relative cycle classes.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Iterate the actual rational relative subdivision chain map.
Source: Hatcher, Algebraic Topology, section 2.1; iterated relative subdivision.
HC no distance; AV milestone no distance.
-/
def relativeSubdivisionIterate (P : TopPair.{0}) :
    ℕ → (((relativeChainFunctor ℚ).obj P) ⟶ ((relativeChainFunctor ℚ).obj P))
  | 0 => 𝟙 _
  | r + 1 => relativeSubdivisionIterate P r ≫ relativeSubdivision P

#print axioms relativeSubdivisionIterate
/-- Actual ambient subdivision iterates commute with the relative projection for every topological pair.
Source: Hatcher, Algebraic Topology, section 2.1; naturality of relative subdivision.
HC no distance; AV milestone no distance.
-/
theorem relativeSubdivisionIterate_projection (P : TopPair.{0}) (r : ℕ) :
    relativeChainProjection ℚ P ≫ relativeSubdivisionIterate P r =
      rationalSubdivisionIterate P.fst r ≫ relativeChainProjection ℚ P := by
  induction r with
  | zero => simp [relativeSubdivisionIterate, rationalSubdivisionIterate_zero]
  | succ r ih =>
    change relativeChainProjection ℚ P ≫ (relativeSubdivisionIterate P r ≫ relativeSubdivision P) = _
    rw [rationalSubdivisionIterate_succ, ← Category.assoc, ih, Category.assoc,
      relativeSubdivision_projection, ← Category.assoc]

#print axioms relativeSubdivisionIterate_projection
/-- The actual relative subdivision iterates retain the prism homotopy to the identity.
Source: Hatcher, Algebraic Topology, section 2.1; iterated subdivision prism homotopies.
HC no distance; AV milestone no distance.
-/
def relativeSubdivisionIterateHomotopy (P : TopPair.{0}) : ∀ r : ℕ,
    Homotopy (relativeSubdivisionIterate P r) (𝟙 ((relativeChainFunctor ℚ).obj P))
  | 0 => Homotopy.refl _
  | r + 1 => by
      simpa [relativeSubdivisionIterate] using
        (relativeSubdivisionIterateHomotopy P r).comp (relativeSubdivisionHomotopy P)

#print axioms relativeSubdivisionIterateHomotopy
/-- Every actual relative subdivision iterate acts identically on relative singular homology.
Source: Hatcher, Algebraic Topology, section 2.1; homology invariance of subdivision.
HC no distance; AV milestone no distance.
-/
theorem relativeSubdivisionIterate_homology (P : TopPair.{0}) (r n : ℕ) :
    HomologicalComplex.homologyMap (relativeSubdivisionIterate P r) n = 𝟙 _ := by
  simpa using (relativeSubdivisionIterateHomotopy P r).homologyMap_eq n

#print axioms relativeSubdivisionIterate_homology
/-- An actual relative cycle and its subdivided image represent the same homology class.
Source: Hatcher, Algebraic Topology, section 2.1; subdivision on cycle representatives.
HC no distance; AV milestone no distance.
-/
theorem relativeSubdivisionIterate_cycleClass (P : TopPair.{0}) (r n : ℕ)
    (z : LinearMap.ker ((((relativeChainFunctor ℚ).obj P).sc n).g.hom)) :
    (((relativeChainFunctor ℚ).obj P).sc n).moduleCatHomologyClass
      (ShortComplex.moduleCatCycleMap
        ((HomologicalComplex.shortComplexFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) n).map
          (relativeSubdivisionIterate P r)) z) =
      (((relativeChainFunctor ℚ).obj P).sc n).moduleCatHomologyClass z := by
  have h := ShortComplex.moduleCatHomologyClass_naturality
    ((HomologicalComplex.shortComplexFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) n).map
      (relativeSubdivisionIterate P r)) z
  change (HomologicalComplex.homologyMap (relativeSubdivisionIterate P r) n).hom
      ((((relativeChainFunctor ℚ).obj P).sc n).moduleCatHomologyClass z) = _ at h
  rw [relativeSubdivisionIterate_homology] at h
  exact h.symm

#print axioms relativeSubdivisionIterate_cycleClass
end HodgeLean.Foundations.RationalHomologyManifold
