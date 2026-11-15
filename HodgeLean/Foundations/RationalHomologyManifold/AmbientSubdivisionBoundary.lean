import HodgeLean.Foundations.RationalHomologyManifold.AmbientSubdivisionSections

/-! Actual boundary compatibility of ambient subdivision sheaf sections.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Taking the actual boundary of an ambient chain commutes with its subdivision-limit sheaf section in every stage and open set.
Source: Hatcher, Algebraic Topology, section 2.1, and Bredon, Sheaf Theory, second edition, VI.12; the supported-chain comparison.
HC no distance; AV milestone no distance.
-/
theorem subdivisionAmbientSectionMap_boundary (X : TopCat.{0}) (n m : ℕ) (U : Opens X) :
    subdivisionAmbientSectionMap X (n + 1) U m ≫
      (((subdivisionLimitSheafComplex X).d (n + 1) n).hom.app (Opposite.op U)) =
    (forget₂ (ModuleCat ℚ) AddCommGrpCat).map ((SingularChainComplex ℚ X).d (n + 1) n) ≫
      subdivisionAmbientSectionMap X n U m := by
  let F := forget₂ (ModuleCat ℚ) AddCommGrpCat
  let R := TopPair.ofSubset (X := X) (U : Set X)ᶜ
  let P := subdivisionLimitPresheafComplex X
  let a (i : ℕ) := F.map ((relativeChainProjection ℚ R).f i)
  let b (i : ℕ) := ((colimit.ι (presheafSubdivisionDiagram X) m).f i).app (Opposite.op U)
  let u (i : ℕ) := (toSheafify (Opens.grothendieckTopology X) (P.X i)).app (Opposite.op U)
  let dP := (P.d (n + 1) n).app (Opposite.op U)
  let dC := ((singularChainPresheafComplex ℚ X).d (n + 1) n).app (Opposite.op U)
  let dS := ((subdivisionLimitSheafComplex X).d (n + 1) n).hom.app (Opposite.op U)
  have hu : u (n + 1) ≫ dS = dP ≫ u n := by
    have h := congrArg (fun f => f.app (Opposite.op U))
      (toSheafify_naturality (Opens.grothendieckTopology X) (P.d (n + 1) n))
    exact h.symm
  have hc : b (n + 1) ≫ dP = dC ≫ b n := by
    have h := congrArg (fun f => f.app (Opposite.op U))
      ((colimit.ι (presheafSubdivisionDiagram X) m).comm (n + 1) n)
    exact h
  have hp : a (n + 1) ≫ dC = F.map ((SingularChainComplex ℚ X).d (n + 1) n) ≫ a n := by
    change F.map ((relativeChainProjection ℚ R).f (n + 1)) ≫
        ((singularChainPresheafComplex ℚ X).d (n + 1) n).app (Opposite.op U) =
      F.map ((SingularChainComplex ℚ X).d (n + 1) n) ≫ F.map ((relativeChainProjection ℚ R).f n)
    rw [singularChainPresheafComplex_d]
    change F.map ((relativeChainProjection ℚ R).f (n + 1)) ≫
        F.map (((relativeChainFunctor ℚ).obj R).d (n + 1) n) =
      F.map ((SingularChainComplex ℚ X).d (n + 1) n) ≫ F.map ((relativeChainProjection ℚ R).f n)
    rw [← F.map_comp, ← F.map_comp]
    exact congrArg F.map ((relativeChainProjection ℚ R).comm (n + 1) n)
  change (a (n + 1) ≫ b (n + 1) ≫ u (n + 1)) ≫ dS =
    F.map ((SingularChainComplex ℚ X).d (n + 1) n) ≫ a n ≫ b n ≫ u n
  calc
    _ = a (n + 1) ≫ b (n + 1) ≫ dP ≫ u n := by
      simp only [Category.assoc]
      rw [hu]
    _ = a (n + 1) ≫ dC ≫ b n ≫ u n := by rw [reassoc_of% hc]
    _ = _ := by
      rw [← Category.assoc (a (n + 1)) dC (b n ≫ u n), hp]
      simp only [Category.assoc]

#print axioms subdivisionAmbientSectionMap_boundary
end HodgeLean.Foundations.RationalHomologyManifold
