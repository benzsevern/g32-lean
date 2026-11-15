import HodgeLean.Foundations.RationalHomologyManifold.SubdivisionChains
import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.RelativeHomotopyInvariance

/-! Affine subdivision on the actual relative singular-chain quotients.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Rational affine subdivision descends to the actual relative-chain cokernel.
Source: Hatcher, Algebraic Topology, section 2.1, relative subdivision.
HC no distance; AV milestone no distance.
-/
def relativeSubdivision (P : TopPair.{0}) :
    (relativeChainFunctor ℚ).obj P ⟶ (relativeChainFunctor ℚ).obj P :=
  cokernel.map ((chainPairFunctor ℚ).obj P).hom ((chainPairFunctor ℚ).obj P).hom
    (rationalSubdivision P.snd) (rationalSubdivision P.fst)
    (rationalSubdivision_naturality P.map)

#print axioms relativeSubdivision
/-- Projection to relative chains preserves the literal subdivision operator.
Source: Hatcher, Algebraic Topology, section 2.1, relative subdivision.
HC no distance; AV milestone no distance.
-/
theorem relativeSubdivision_projection (P : TopPair.{0}) :
    relativeChainProjection ℚ P ≫ relativeSubdivision P =
      rationalSubdivision P.fst ≫ relativeChainProjection ℚ P := by
  simp only [relativeSubdivision, relativeChainProjection, cokernel.map, cokernel.π_desc]

#print axioms relativeSubdivision_projection
/-- Relative subdivision respects every map of actual topological pairs.
Source: Hatcher, Algebraic Topology, section 2.1, naturality of relative subdivision.
HC no distance; AV milestone no distance.
-/
theorem relativeSubdivision_naturality {P Q : TopPair.{0}} (f : P ⟶ Q) :
    (relativeChainFunctor ℚ).map f ≫ relativeSubdivision Q =
      relativeSubdivision P ≫ (relativeChainFunctor ℚ).map f := by
  let A := SSet.chainComplexMap (TopCat.toSSet.map f.hom.right) (ModuleCat.of ℚ ℚ)
  have hf : relativeChainProjection ℚ P ≫ (relativeChainFunctor ℚ).map f =
      A ≫ relativeChainProjection ℚ Q :=
    TopPair.Homotopy.relativeChainProjection_naturality f
  have hn : A ≫ rationalSubdivision Q.fst = rationalSubdivision P.fst ≫ A :=
    rationalSubdivision_naturality f.hom.right
  letI : Epi (relativeChainProjection ℚ P) := by
    unfold relativeChainProjection
    infer_instance
  apply (cancel_epi (relativeChainProjection ℚ P)).1
  calc
    _ = A ≫ (relativeChainProjection ℚ Q ≫ relativeSubdivision Q) := by
      rw [← Category.assoc, hf, Category.assoc]
    _ = A ≫ (rationalSubdivision Q.fst ≫ relativeChainProjection ℚ Q) := by
      rw [relativeSubdivision_projection]
    _ = rationalSubdivision P.fst ≫ (A ≫ relativeChainProjection ℚ Q) := by
      rw [← Category.assoc, hn, Category.assoc]
    _ = rationalSubdivision P.fst ≫
        (relativeChainProjection ℚ P ≫ (relativeChainFunctor ℚ).map f) := by rw [hf]
    _ = _ := by rw [← Category.assoc, ← relativeSubdivision_projection, Category.assoc]

#print axioms relativeSubdivision_naturality
end HodgeLean.Foundations.RationalHomologyManifold
