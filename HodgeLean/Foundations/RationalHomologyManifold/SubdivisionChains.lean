import HodgeLean.Foundations.RationalHomologyManifold.Defs
import HodgeLean.Foundations.Port.AlgebraicTopology.Singular.CoefficientExcision
import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Subdivision.AffinePrism

/-! Rational affine subdivision for the supported singular-chain model.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Extend the actual integral affine subdivision operator to rational singular chains.
Source: Hatcher, Algebraic Topology, section 2.1, barycentric subdivision.
HC no distance; AV milestone no distance.
-/
def rationalSubdivision (X : TopCat.{0}) :
    SingularChainComplex ℚ X ⟶ SingularChainComplex ℚ X :=
  coefficientizeSimplicialChainMap ℚ (TopCat.toSSet.obj X) (TopCat.toSSet.obj X)
    (affineSingularSubdivisionChainMap X)

#print axioms rationalSubdivision
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Rational subdivision commutes with the actual singular chain map of a continuous map.
Source: Hatcher, Algebraic Topology, section 2.1, naturality of subdivision.
HC no distance; AV milestone no distance.
-/
theorem rationalSubdivision_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) :
    (SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℚ ℚ)) ≫
      rationalSubdivision Y = rationalSubdivision X ≫
        SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℚ ℚ) := by
  have h := congrArg
    (coefficientizeSimplicialChainMap ℚ (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y))
    (affineSingularSubdivisionChainMap_naturality f)
  simpa only [coefficientizeSimplicialChainMap_comp,
    coefficientizeSimplicialChainMap_chainComplexMap, rationalSubdivision] using h

#print axioms rationalSubdivision_naturality
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Rational affine subdivision has the actual coefficient extension of the integral prism.
Source: Hatcher, Algebraic Topology, section 2.1, subdivision prism homotopy.
HC no distance; AV milestone no distance.
-/
def rationalSubdivisionHomotopy (X : TopCat.{0}) :
    Homotopy (rationalSubdivision X) (𝟙 (SingularChainComplex ℚ X)) :=
  (coefficientizeSimplicialChainHomotopy ℚ (TopCat.toSSet.obj X) (TopCat.toSSet.obj X)
    (affineSingularSubdivisionHomotopy X)).trans
      (Homotopy.ofEq (coefficientizeSimplicialChainMap_id ℚ (TopCat.toSSet.obj X)))

#print axioms rationalSubdivisionHomotopy
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The rational prism components respect every continuous map, including support inclusions.
Source: Hatcher, Algebraic Topology, section 2.1, naturality of the subdivision prism.
HC no distance; AV milestone no distance.
-/
theorem rationalSubdivisionHomotopy_naturality {X Y : TopCat.{0}} (f : X ⟶ Y)
    (i j : ℕ) :
    (SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℚ ℚ)).f i ≫
      (rationalSubdivisionHomotopy Y).hom i j =
    (rationalSubdivisionHomotopy X).hom i j ≫
      (SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℚ ℚ)).f j := by
  have hI :
      (SSet.chainComplexMap (TopCat.toSSet.map f) (AddCommGrpCat.of ℤ)).f i ≫
        (affineSingularSubdivisionHomotopy Y).hom i j =
      (affineSingularSubdivisionHomotopy X).hom i j ≫
        (SSet.chainComplexMap (TopCat.toSSet.map f) (AddCommGrpCat.of ℤ)).f j := by
    by_cases hij : i + 1 = j
    · subst j
      simpa only [affineSingularSubdivisionHomotopy, affineSingularSubdivisionPrismHom_succ]
        using affineSingularSubdivisionPrismComponent_naturality f i
    · rw [(affineSingularSubdivisionHomotopy Y).zero i j
          (by simpa only [ComplexShape.down_Rel] using hij),
        (affineSingularSubdivisionHomotopy X).zero i j
          (by simpa only [ComplexShape.down_Rel] using hij), comp_zero, zero_comp]
  have h := congrArg
    (coefficientizeSimplicialChainComponent ℚ (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y) i j) hI
  simpa only [coefficientizeSimplicialChainComponent_comp,
    coefficientizeSimplicialChainComponent_chainComplexMap, rationalSubdivisionHomotopy,
    Homotopy.trans, Homotopy.ofEq, coefficientizeSimplicialChainHomotopy,
    Pi.add_apply, add_zero] using h

#print axioms rationalSubdivisionHomotopy_naturality
end HodgeLean.Foundations.RationalHomologyManifold
