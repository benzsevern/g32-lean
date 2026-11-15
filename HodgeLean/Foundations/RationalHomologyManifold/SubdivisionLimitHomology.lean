import HodgeLean.Foundations.RationalHomologyManifold.SubdivisionLimit
import HodgeLean.Foundations.RationalHomologyManifold.FilteredHomology
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
import Mathlib.Algebra.Category.Grp.AB

/-! Homology of the actual supported subdivision limit.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Supported presheaf subdivision induces the identity on homology.
Source: Bredon, Sheaf Theory, second edition, VI.12; the subdivision prism.
HC no distance; AV milestone no distance.
-/
theorem presheafSubdivision_homology (X : TopCat.{0}) (n : ℕ) :
    HomologicalComplex.homologyMap (presheafSubdivision X) n = 𝟙 _ := by
  simpa using (presheafSubdivisionHomotopy X).homologyMap_eq n

#print axioms presheafSubdivision_homology
/-- Every transition in the supported subdivision sequence acts identically on homology.
Source: Bredon, Sheaf Theory, second edition, VI.12; subdivision invariance.
HC no distance; AV milestone no distance.
-/
theorem presheafSubdivisionDiagram_homology (X : TopCat.{0}) (n i j : ℕ) (h : i ≤ j) :
    HomologicalComplex.homologyMap
      ((presheafSubdivisionDiagram X).map (homOfLE h)) n = 𝟙 _ := by
  induction j, h using Nat.le_induction with
  | base => simp
  | succ j hij ih =>
    have heq : homOfLE (Nat.le_succ_of_le hij) =
        homOfLE hij ≫ homOfLE (Nat.le_succ j) := Subsingleton.elim _ _
    rw [heq, Functor.map_comp, HomologicalComplex.homologyMap_comp,
      presheafSubdivisionDiagram_transition, presheafSubdivision_homology, ih, Category.id_comp]
    rfl

#print axioms presheafSubdivisionDiagram_homology
/-- The homology colimit receives an isomorphism from the initial subdivision stage.
Source: Bredon, Sheaf Theory, second edition, VI.12; subdivision invariance.
HC no distance; AV milestone no distance.
-/
theorem subdivisionHomologyColimit_stage_isIso (X : TopCat.{0}) (n : ℕ) :
    IsIso (colimit.ι (presheafSubdivisionDiagram X ⋙
      HomologicalComplex.homologyFunctor _ (ComplexShape.down ℕ) n) 0) := by
  let F := presheafSubdivisionDiagram X ⋙
    HomologicalComplex.homologyFunctor _ (ComplexShape.down ℕ) n
  have h : F.IsEventuallyConstantFrom 0 := by
    intro j f
    have hf : f = homOfLE (leOfHom f) := Subsingleton.elim _ _
    change IsIso (HomologicalComplex.homologyMap ((presheafSubdivisionDiagram X).map f) n)
    rw [hf, presheafSubdivisionDiagram_homology]
    infer_instance
  exact h.isIso_ι_of_isColimit (colimit.isColimit F)

#print axioms subdivisionHomologyColimit_stage_isIso
/-- The actual initial-stage map to the supported presheaf subdivision limit is a quasi-isomorphism.
Source: Bredon, Sheaf Theory, second edition, VI.12; subdivision invariance and exact filtered colimits.
HC no distance; AV milestone no distance.
-/
theorem subdivisionPresheafStage_zero_quasiIso (X : TopCat.{0}) :
    QuasiIso (colimit.ι (presheafSubdivisionDiagram X) 0) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let H := HomologicalComplex.homologyFunctor (TopCat.Presheaf AddCommGrpCat X)
    (ComplexShape.down ℕ) n
  letI : HasExactColimitsOfShape ℕ (TopCat.Presheaf AddCommGrpCat X) := by
    unfold TopCat.Presheaf
    infer_instance
  letI : PreservesColimit (presheafSubdivisionDiagram X) H :=
    complexHomology_preservesColimit (ComplexShape.down ℕ) n (presheafSubdivisionDiagram X)
  letI := subdivisionHomologyColimit_stage_isIso X n
  have heq := ι_preservesColimitIso_inv H (presheafSubdivisionDiagram X) 0
  change IsIso (H.map (colimit.ι (presheafSubdivisionDiagram X) 0))
  rw [← heq]
  infer_instance

#print axioms subdivisionPresheafStage_zero_quasiIso
/-- The canonical initial-stage map to the sheafified subdivision limit is a quasi-isomorphism.
Source: Bredon, Sheaf Theory, second edition, VI.12; subdivision invariance under sheafification.
HC no distance; AV milestone no distance.
-/
theorem subdivisionSheafStage_zero_quasiIso (X : TopCat.{0}) :
    QuasiIso (subdivisionSheafStage X 0) := by
  letI := subdivisionPresheafStage_zero_quasiIso X
  exact inferInstanceAs (QuasiIso
    (((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).mapHomologicalComplex (ComplexShape.down ℕ)).map
        (colimit.ι (presheafSubdivisionDiagram X) 0)))

#print axioms subdivisionSheafStage_zero_quasiIso
/-- Each actual finite-stage map to the supported sheaf subdivision limit is a quasi-isomorphism.
Source: Bredon, Sheaf Theory, second edition, VI.12; subdivision invariance.
HC no distance; AV milestone no distance.
-/
theorem subdivisionSheafStage_quasiIso (X : TopCat.{0}) (m : ℕ) :
    QuasiIso (subdivisionSheafStage X m) := by
  letI := subdivisionSheafStage_zero_quasiIso X
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap, subdivisionSheafStage_homology]
  infer_instance

#print axioms subdivisionSheafStage_quasiIso
end HodgeLean.Foundations.RationalHomologyManifold
