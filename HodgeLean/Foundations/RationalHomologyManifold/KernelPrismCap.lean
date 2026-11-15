import HodgeLean.Foundations.RationalHomologyManifold.PresheafPrismCap
import HodgeLean.Foundations.RationalHomologyManifold.LocalPrismStabilization
import HodgeLean.Foundations.RationalHomologyManifold.LocallyStationaryPresheafMap

/-! Actual finite prism-cap maps on the ambient-to-local cochain kernel.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicTopology.Singular AlgebraicTopology.Simplicial
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Restrict the actual finite prism-cap morphism to the kernel of ambient cochain restriction.
Source: Bredon, Sheaf Theory, second edition, VI.12; the subdivision homotopy on the local cochain kernel.
HC no distance; AV milestone no distance.
-/
def kernelPrismCapPresheafMap (X : TopCat.{0}) (n p q : ℕ)
    (z : (SingularChainComplex ℚ X).X n) (m : ℕ) :
    (ambientLocalZeroPresheafComplex X).X p ⟶ ((subdivisionLimitSheafComplex X).X q).obj :=
  (kernel.ι (ambientCochainPresheafComplexRestriction X)).f p ≫
    ambientPrismCapPresheafMap X n p q z m

#print axioms kernelPrismCapPresheafMap
/-- Every actual kernel section keeps the literal finite cap representative after restriction to the kernel.
Source: Hatcher, Algebraic Topology, sections 2.1 and 3.3; actual cap of the finite subdivision prism.
HC no distance; AV milestone no distance.
-/
theorem kernelPrismCapPresheafMap_apply (X : TopCat.{0}) (n p q : ℕ)
    (z : (SingularChainComplex ℚ X).X n) (m : ℕ) (U : Opens X)
    (b : ((ambientLocalZeroPresheafComplex X).X p).obj (Opposite.op U)) :
    (kernelPrismCapPresheafMap X n p q z m).app (Opposite.op U) b =
      subdivisionAmbientSectionMap X q U 0
        (cap ℚ p q (((kernel.ι (ambientCochainPresheafComplexRestriction X)).f p).app (Opposite.op U) b)
          (rationalPrismSum X n (p + q) m z)) := by
  exact ambientPrismCapPresheafMap_apply X n p q z m U _

#print axioms kernelPrismCapPresheafMap_apply
/-- The actual finite prism-cap morphisms on the local kernel are locally stationary on every open set.
Source: Bredon, Sheaf Theory, second edition, VI.12; uniform local stabilization of subordinate prism caps.
HC no distance; AV milestone no distance.
-/
theorem kernelPrismCapPresheafMap_locally_stationary (X : TopCat.{0}) [RegularSpace X]
    (n p q : ℕ) (z : (SingularChainComplex ℚ X).X n) (U : Opens X)
    (b : ((ambientLocalZeroPresheafComplex X).X p).obj (Opposite.op U)) (x : U) :
    ∃ (V : Opens X) (hV : V ≤ U), x.val ∈ V ∧ ∃ m : ℕ, ∀ r : ℕ,
      ((subdivisionLimitSheafComplex X).X q).obj.map (homOfLE hV).op
          ((kernelPrismCapPresheafMap X n p q z (m + r)).app (Opposite.op U) b) =
        ((subdivisionLimitSheafComplex X).X q).obj.map (homOfLE hV).op
          ((kernelPrismCapPresheafMap X n p q z m).app (Opposite.op U) b) := by
  let φ : Cochain ℚ (TopCat.toSSet.obj X) p :=
    ((kernel.ι (ambientCochainPresheafComplexRestriction X)).f p).app (Opposite.op U) b
  have hφ := ambientLocalZeroPresheaf_restriction_zero X p U b
  change cochainMap ℚ (TopCat.toSSet.map (TopPair.ofSubset (X := X) (U : Set X)).map) p φ = 0 at hφ
  obtain ⟨V, hxV, hVU, m, hm⟩ := local_cap_prismSum_stabilizes X x.val U x.property n p q φ hφ z
  refine ⟨V, hVU, hxV, m, fun r => ?_⟩
  rw [kernelPrismCapPresheafMap_apply, kernelPrismCapPresheafMap_apply]
  have hr (w : (SingularChainComplex ℚ X).X q) :
      ((subdivisionLimitSheafComplex X).X q).obj.map (homOfLE hVU).op
          (subdivisionAmbientSectionMap X q U 0 w) = subdivisionAmbientSectionMap X q V 0 w :=
    ConcreteCategory.congr_hom (subdivisionAmbientSectionMap_restriction X q 0 U V hVU) w
  rw [hr, hr]
  exact congrArg (fun w =>
    (toSheafify (Opens.grothendieckTopology X) ((subdivisionLimitPresheafComplex X).X q)).app (Opposite.op V)
      (((colimit.ι (presheafSubdivisionDiagram X) 0).f q).app (Opposite.op V) w)) (hm r)

#print axioms kernelPrismCapPresheafMap_locally_stationary

/-- Glue the actual finite prism caps on the kernel by their uniform local stationarity.
Source: Bredon, Sheaf Theory, second edition, I.1 and VI.12; the stabilized local kernel homotopy.
HC no distance; AV milestone no distance.
-/
def kernelPrismCapPresheafLimit (X : TopCat.{0}) [RegularSpace X] (n p q : ℕ)
    (z : (SingularChainComplex ℚ X).X n) :
    (ambientLocalZeroPresheafComplex X).X p ⟶ ((subdivisionLimitSheafComplex X).X q).obj :=
  locallyStationaryPresheafMap _ _ (kernelPrismCapPresheafMap X n p q z)
    (kernelPrismCapPresheafMap_locally_stationary X n p q z)

#print axioms kernelPrismCapPresheafLimit
/-- The stabilized actual kernel prism caps induce a morphism of the existing sheafifications.
Source: Bredon, Sheaf Theory, second edition, I.1 and VI.12; sheafification of the local kernel homotopy.
HC no distance; AV milestone no distance.
-/
def kernelPrismCapSheafMap (X : TopCat.{0}) [RegularSpace X] (n p q : ℕ)
    (z : (SingularChainComplex ℚ X).X n) :
    (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj
        ((ambientLocalZeroPresheafComplex X).X p) ⟶ (subdivisionLimitSheafComplex X).X q :=
  ⟨sheafifyLift (Opens.grothendieckTopology X) (kernelPrismCapPresheafLimit X n p q z)
    ((subdivisionLimitSheafComplex X).X q).property⟩

#print axioms kernelPrismCapSheafMap
/-- The sheafified kernel prism-cap map keeps the actual stabilized presheaf map on original sections.
Source: Bredon, Sheaf Theory, second edition, I.1; the sheafification universal property.
HC no distance; AV milestone no distance.
-/
theorem kernelPrismCapSheafMap_unit (X : TopCat.{0}) [RegularSpace X] (n p q : ℕ)
    (z : (SingularChainComplex ℚ X).X n) :
    toSheafify (Opens.grothendieckTopology X) ((ambientLocalZeroPresheafComplex X).X p) ≫
      (kernelPrismCapSheafMap X n p q z).hom = kernelPrismCapPresheafLimit X n p q z :=
  toSheafify_sheafifyLift _ _ _

#print axioms kernelPrismCapSheafMap_unit
end HodgeLean.Foundations.RationalHomologyManifold
