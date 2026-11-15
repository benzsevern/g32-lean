import HodgeLean.Foundations.RationalHomologyManifold.SupportedSubdivisionStages
import HodgeLean.Foundations.RationalHomologyManifold.SubdivisionSections
import HodgeLean.Foundations.RationalHomologyManifold.AmbientChainPresheaf

/-! Actual maps from ambient chains to supported subdivision-limit sheaf sections.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Project an ambient chain at a specified stage to an actual supported subdivision-limit sheaf section.
Source: Bredon, Sheaf Theory, second edition, VI.12; the supported-chain subdivision model.
HC no distance; AV milestone no distance.
-/
def subdivisionAmbientSectionMap (X : TopCat.{0}) (n : ℕ) (U : Opens X) (m : ℕ) :
    (forget₂ (ModuleCat ℚ) AddCommGrpCat).obj ((SingularChainComplex ℚ X).X n) ⟶
      ((subdivisionLimitSheafComplex X).X n).obj.obj (Opposite.op U) :=
  (forget₂ (ModuleCat ℚ) AddCommGrpCat).map
      ((relativeChainProjection ℚ (TopPair.ofSubset (X := X) (U : Set X)ᶜ)).f n) ≫
    (((colimit.ι (presheafSubdivisionDiagram X) m).f n).app (Opposite.op U)) ≫
      ((toSheafify (Opens.grothendieckTopology X)
        ((subdivisionLimitPresheafComplex X).X n)).app (Opposite.op U))

#print axioms subdivisionAmbientSectionMap
/-- Subdividing an ambient chain and advancing its stage retains its actual sheaf section.
Source: Bredon, Sheaf Theory, second edition, VI.12; the subdivision limit relation.
HC no distance; AV milestone no distance.
-/
theorem subdivisionAmbientSectionMap_transition (X : TopCat.{0}) (n : ℕ) (U : Opens X) (m r : ℕ) :
    (forget₂ (ModuleCat ℚ) AddCommGrpCat).map ((rationalSubdivisionIterate X r).f n) ≫
      subdivisionAmbientSectionMap X n U (m + r) = subdivisionAmbientSectionMap X n U m := by
  have h := congrArg (fun f => f.f n)
    (colimit.w (presheafSubdivisionDiagram X) (homOfLE (Nat.le_add_right m r)))
  have hU := congrArg (fun f => f.app (Opposite.op U)) h
  change (((presheafSubdivisionDiagram X).map (homOfLE (Nat.le_add_right m r))).f n).app
      (Opposite.op U) ≫ (((colimit.ι (presheafSubdivisionDiagram X) (m + r)).f n).app
        (Opposite.op U)) =
    (((colimit.ι (presheafSubdivisionDiagram X) m).f n).app (Opposite.op U)) at hU
  unfold subdivisionAmbientSectionMap
  simp only [← Category.assoc]
  rw [supportedSubdivisionProjection_iterate X n U m r]
  simp only [Category.assoc]
  rw [reassoc_of% hU]

#print axioms subdivisionAmbientSectionMap_transition
/-- Restricting an actual ambient subdivision section is the same as projecting the same chain on the smaller open set.
Source: Bredon, Sheaf Theory, second edition, VI.12; supported-chain restriction.
HC no distance; AV milestone no distance.
-/
theorem subdivisionAmbientSectionMap_restriction (X : TopCat.{0}) (n m : ℕ)
    (U V : Opens X) (hV : V ≤ U) :
    subdivisionAmbientSectionMap X n U m ≫
      ((subdivisionLimitSheafComplex X).X n).obj.map (homOfLE hV).op =
        subdivisionAmbientSectionMap X n V m := by
  let A := ambientChainPresheafProjection X n ≫
    (colimit.ι (presheafSubdivisionDiagram X) m).f n ≫
      toSheafify (Opens.grothendieckTopology X) ((subdivisionLimitPresheafComplex X).X n)
  have h := A.naturality (homOfLE hV).op
  simp only [CategoryTheory.Functor.const_obj_map, Category.id_comp] at h
  change subdivisionAmbientSectionMap X n V m =
    subdivisionAmbientSectionMap X n U m ≫
      ((subdivisionLimitSheafComplex X).X n).obj.map (homOfLE hV).op at h
  exact h.symm

#print axioms subdivisionAmbientSectionMap_restriction
end HodgeLean.Foundations.RationalHomologyManifold
