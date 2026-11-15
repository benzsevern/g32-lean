import HodgeLean.Foundations.RationalHomologyManifold.SubdivisionSmallChains
import HodgeLean.Foundations.RationalHomologyManifold.SubdivisionLimit

/-! Actual ambient projections through supported subdivision stages.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Ambient projection is an actual natural transformation from rational subdivision to supported subdivision on an open set.
Source: Bredon, Sheaf Theory, second edition, VI.12; naturality of supported subdivision.
HC no distance; AV milestone no distance.
-/
def supportedSubdivisionProjection (X : TopCat.{0}) (n : ℕ) (U : Opens X) :
    rationalSubdivisionDiagram X ⋙
      (HomologicalComplex.eval (ModuleCat ℚ) (ComplexShape.down ℕ) n ⋙
        forget₂ (ModuleCat ℚ) AddCommGrpCat) ⟶
    presheafSubdivisionDiagram X ⋙
      (HomologicalComplex.eval (TopCat.Presheaf AddCommGrpCat X) (ComplexShape.down ℕ) n ⋙
        (evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (Opposite.op U)) := by
  let F := forget₂ (ModuleCat ℚ) AddCommGrpCat
  let P := TopPair.ofSubset (X := X) (U : Set X)ᶜ
  refine NatTrans.ofSequence (fun _ => F.map ((relativeChainProjection ℚ P).f n)) ?_
  intro m
  change F.map (((rationalSubdivisionDiagram X).map (homOfLE (Nat.le_succ m))).f n) ≫
      F.map ((relativeChainProjection ℚ P).f n) =
    F.map ((relativeChainProjection ℚ P).f n) ≫
      (((presheafSubdivisionDiagram X).map (homOfLE (Nat.le_succ m))).f n).app (Opposite.op U)
  have hs : (rationalSubdivisionDiagram X).map (homOfLE (Nat.le_succ m)) =
      rationalSubdivision X := Functor.ofSequence_map_homOfLE_succ _ _
  rw [hs, presheafSubdivisionDiagram_transition]
  change F.map ((rationalSubdivision X).f n) ≫ F.map ((relativeChainProjection ℚ P).f n) =
    F.map ((relativeChainProjection ℚ P).f n) ≫ F.map ((relativeSubdivision P).f n)
  rw [← F.map_comp, ← F.map_comp]
  have h := congrArg (fun f => f.f n) (relativeSubdivision_projection P)
  change (relativeChainProjection ℚ P).f n ≫ (relativeSubdivision P).f n =
    (rationalSubdivision X).f n ≫ (relativeChainProjection ℚ P).f n at h
  exact congrArg F.map h.symm

#print axioms supportedSubdivisionProjection
/-- Ambient rational subdivision and the actual supported transition give the same relative-chain map.
Source: Bredon, Sheaf Theory, second edition, VI.12; supported subdivision and relative projections.
HC no distance; AV milestone no distance.
-/
theorem supportedSubdivisionProjection_iterate (X : TopCat.{0}) (n : ℕ) (U : Opens X) (m r : ℕ) :
    (forget₂ (ModuleCat ℚ) AddCommGrpCat).map ((rationalSubdivisionIterate X r).f n) ≫
      (forget₂ (ModuleCat ℚ) AddCommGrpCat).map
        ((relativeChainProjection ℚ (TopPair.ofSubset (X := X) (U : Set X)ᶜ)).f n) =
    (forget₂ (ModuleCat ℚ) AddCommGrpCat).map
        ((relativeChainProjection ℚ (TopPair.ofSubset (X := X) (U : Set X)ᶜ)).f n) ≫
      (((presheafSubdivisionDiagram X).map (homOfLE (Nat.le_add_right m r))).f n).app
        (Opposite.op U) := by
  have h := (supportedSubdivisionProjection X n U).naturality (homOfLE (Nat.le_add_right m r))
  change (forget₂ (ModuleCat ℚ) AddCommGrpCat).map
        (((rationalSubdivisionDiagram X).map (homOfLE (Nat.le_add_right m r))).f n) ≫
      (forget₂ (ModuleCat ℚ) AddCommGrpCat).map
        ((relativeChainProjection ℚ (TopPair.ofSubset (X := X) (U : Set X)ᶜ)).f n) = _ at h
  rw [rationalSubdivisionDiagram_map_add] at h
  exact h

#print axioms supportedSubdivisionProjection_iterate
end HodgeLean.Foundations.RationalHomologyManifold
