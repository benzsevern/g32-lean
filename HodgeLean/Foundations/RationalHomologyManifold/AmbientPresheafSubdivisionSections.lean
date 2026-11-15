import HodgeLean.Foundations.RationalHomologyManifold.SupportedSubdivisionStages
import HodgeLean.Foundations.RationalHomologyManifold.SubdivisionSections

/-! Actual ambient representatives before sheafifying the supported subdivision limit.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Project an ambient chain at a specified stage to an actual supported subdivision-limit presheaf section.
Source: Bredon, Sheaf Theory, second edition, VI.12; the supported-chain subdivision presheaf.
HC no distance; AV milestone no distance.
-/
def subdivisionAmbientPresheafSectionMap (X : TopCat.{0}) (n : ℕ) (U : Opens X) (m : ℕ) :
    (forget₂ (ModuleCat ℚ) AddCommGrpCat).obj ((SingularChainComplex ℚ X).X n) ⟶
      ((subdivisionLimitPresheafComplex X).X n).obj (Opposite.op U) :=
  (forget₂ (ModuleCat ℚ) AddCommGrpCat).map
      ((relativeChainProjection ℚ (TopPair.ofSubset (X := X) (U : Set X)ᶜ)).f n) ≫
    (((colimit.ι (presheafSubdivisionDiagram X) m).f n).app (Opposite.op U))

#print axioms subdivisionAmbientPresheafSectionMap
/-- Subdividing an ambient chain and advancing its stage retains its actual presheaf-limit section.
Source: Bredon, Sheaf Theory, second edition, VI.12; the subdivision limit relation before sheafification.
HC no distance; AV milestone no distance.
-/
theorem subdivisionAmbientPresheafSectionMap_transition (X : TopCat.{0}) (n : ℕ)
    (U : Opens X) (m r : ℕ) :
    (forget₂ (ModuleCat ℚ) AddCommGrpCat).map ((rationalSubdivisionIterate X r).f n) ≫
      subdivisionAmbientPresheafSectionMap X n U (m + r) =
        subdivisionAmbientPresheafSectionMap X n U m := by
  have h := congrArg (fun f => f.f n)
    (colimit.w (presheafSubdivisionDiagram X) (homOfLE (Nat.le_add_right m r)))
  have hU := congrArg (fun f => f.app (Opposite.op U)) h
  change (((presheafSubdivisionDiagram X).map (homOfLE (Nat.le_add_right m r))).f n).app
      (Opposite.op U) ≫ (((colimit.ι (presheafSubdivisionDiagram X) (m + r)).f n).app
        (Opposite.op U)) =
    (((colimit.ι (presheafSubdivisionDiagram X) m).f n).app (Opposite.op U)) at hU
  unfold subdivisionAmbientPresheafSectionMap
  rw [← Category.assoc, supportedSubdivisionProjection_iterate X n U m r, Category.assoc, hU]

#print axioms subdivisionAmbientPresheafSectionMap_transition
/-- Every section of the actual subdivision-limit presheaf is represented by an ambient chain at a finite stage.
Source: Bredon, Sheaf Theory, second edition, VI.12; actual supported-chain representatives before sheafification.
HC no distance; AV milestone no distance.
-/
theorem subdivisionLimitPresheaf_ambient_section_exists (X : TopCat.{0}) (n : ℕ) (U : Opens X)
    (a : ((subdivisionLimitPresheafComplex X).X n).obj (Opposite.op U)) :
    ∃ (m : ℕ) (z : (SingularChainComplex ℚ X).X n),
      (subdivisionAmbientPresheafSectionMap X n U m).hom z = a := by
  obtain ⟨m, y, hy⟩ := subdivisionLimitPresheaf_section_exists X n U a
  obtain ⟨z, hz⟩ := relativeChainProjection_surjective
    (TopPair.ofSubset (X := X) (U : Set X)ᶜ) n y
  refine ⟨m, z, ?_⟩
  change (((colimit.ι (presheafSubdivisionDiagram X) m).f n).app (Opposite.op U))
      ((relativeChainProjection ℚ (TopPair.ofSubset (X := X) (U : Set X)ᶜ)).f n z) = a
  rw [hz]
  exact hy

#print axioms subdivisionLimitPresheaf_ambient_section_exists
end HodgeLean.Foundations.RationalHomologyManifold
