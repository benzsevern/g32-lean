import HodgeLean.Foundations.RationalHomologyManifold.SubdivisionSheaf
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Functor.OfSequence

/-! The concrete sequence of repeated subdivision on supported chains.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- The actual relative-chain presheaf complex repeated with subdivision as transition.
Source: Bredon, Sheaf Theory, second edition, VI.12; subdivision of supported chains.
HC no distance; AV milestone no distance.
-/
def presheafSubdivisionDiagram (X : TopCat.{0}) :
    ℕ ⥤ ChainComplex (TopCat.Presheaf AddCommGrpCat X) ℕ :=
  Functor.ofSequence (X := fun _ : ℕ => singularChainPresheafComplex ℚ X)
    (fun _ => presheafSubdivision X)

#print axioms presheafSubdivisionDiagram
/-- The supported-chain presheaf complex after passing through all finite subdivision stages.
Source: Bredon, Sheaf Theory, second edition, VI.12; subdivision of supported chains.
HC no distance; AV milestone no distance.
-/
def subdivisionLimitPresheafComplex (X : TopCat.{0}) :
    ChainComplex (TopCat.Presheaf AddCommGrpCat X) ℕ :=
  colimit (presheafSubdivisionDiagram X)

#print axioms subdivisionLimitPresheafComplex
/-- Every successor transition in the sequence is the actual supported subdivision map.
Source: Bredon, Sheaf Theory, second edition, VI.12; the subdivision sequence.
HC no distance; AV milestone no distance.
-/
theorem presheafSubdivisionDiagram_transition (X : TopCat.{0}) (m : ℕ) :
    (presheafSubdivisionDiagram X).map (homOfLE (Nat.le_succ m)) = presheafSubdivision X :=
  Functor.ofSequence_map_homOfLE_succ _ m

#print axioms presheafSubdivisionDiagram_transition
/-- Exact sheafification of the actual presheaf subdivision colimit.
Source: Bredon, Sheaf Theory, second edition, V.9 and VI.12; the supported-chain sheaf model.
HC no distance; AV milestone no distance.
-/
def subdivisionLimitSheafComplex (X : TopCat.{0}) :
    ChainComplex (TopCat.Sheaf AddCommGrpCat X) ℕ :=
  ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (subdivisionLimitPresheafComplex X)

#print axioms subdivisionLimitSheafComplex
/-- The canonical map from each finite subdivision stage to the actual sheafified colimit.
Source: Bredon, Sheaf Theory, second edition, VI.12; the subdivision limit comparison.
HC no distance; AV milestone no distance.
-/
def subdivisionSheafStage (X : TopCat.{0}) (m : ℕ) :
    singularChainSheafComplex ℚ X ⟶ subdivisionLimitSheafComplex X :=
  ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).mapHomologicalComplex
    (ComplexShape.down ℕ)).map (colimit.ι (presheafSubdivisionDiagram X) m)

#print axioms subdivisionSheafStage
/-- Canonical finite-stage maps obey the actual subdivision relation in the sheafified limit.
Source: Bredon, Sheaf Theory, second edition, VI.12; the subdivision limit comparison.
HC no distance; AV milestone no distance.
-/
theorem subdivisionSheafStage_transition (X : TopCat.{0}) (m : ℕ) :
    sheafSubdivision X ≫ subdivisionSheafStage X (m + 1) = subdivisionSheafStage X m := by
  let F := (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).mapHomologicalComplex
    (ComplexShape.down ℕ)
  change F.map (presheafSubdivision X) ≫ F.map (colimit.ι (presheafSubdivisionDiagram X) (m + 1)) =
    F.map (colimit.ι (presheafSubdivisionDiagram X) m)
  rw [← F.map_comp]
  have h := colimit.w (presheafSubdivisionDiagram X) (homOfLE (Nat.le_succ m))
  rw [presheafSubdivisionDiagram_transition] at h
  exact congrArg F.map h

#print axioms subdivisionSheafStage_transition
/-- All finite subdivision stages give the same map on actual homology sheaves.
Source: Bredon, Sheaf Theory, second edition, VI.12; subdivision invariance.
HC no distance; AV milestone no distance.
-/
theorem subdivisionSheafStage_homology (X : TopCat.{0}) (m n : ℕ) :
    HomologicalComplex.homologyMap (subdivisionSheafStage X m) n =
      HomologicalComplex.homologyMap (subdivisionSheafStage X 0) n := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have h := congrArg (fun f => HomologicalComplex.homologyMap f n)
      (subdivisionSheafStage_transition X m)
    rw [HomologicalComplex.homologyMap_comp, sheafSubdivision_homology, Category.id_comp] at h
    exact h.trans ih

#print axioms subdivisionSheafStage_homology
end HodgeLean.Foundations.RationalHomologyManifold
