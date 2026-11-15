import HodgeLean.Foundations.RationalHomologyManifold.ScalarCycleSectionEvaluation

/-! Actual absolute cycle classes underlying scalar homology sheaf sections.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicTopology.Singular
open HodgeLean.RealDefs
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Regard a specified actual ambient cycle as the original singular short-complex cycle.
Source: Hatcher, Algebraic Topology, section 2.1; actual cycles in singular homology.
HC no distance; AV milestone no distance.
-/
def scalarAmbientCycle (X : TopCat.{0}) (n : ℕ)
    (z : (SingularChainComplex ℚ X).X (n + 1))
    (hz : (SingularChainComplex ℚ X).d (n + 1) n z = 0) :
    LinearMap.ker (((SingularChainComplex ℚ X).sc (n + 1)).g.hom) :=
  ⟨z, by
    change (SingularChainComplex ℚ X).d (n + 1) ((ComplexShape.down ℕ).next (n + 1)) z = 0
    rw [ChainComplex.next_nat_succ]
    exact hz⟩

#print axioms scalarAmbientCycle
/-- The actual scalar cycle homology section at the constant unit is the section of the original absolute class projected to each open support.
Source: Bredon, Sheaf Theory, second edition, VI.12; naturality of actual relative singular classes.
HC no distance; AV milestone no distance.
-/
theorem scalarCycleHomologySheafMap_absolute_section (X : TopCat.{0}) (n : ℕ)
    (z : (SingularChainComplex ℚ X).X (n + 1))
    (hz : (SingularChainComplex ℚ X).d (n + 1) n z = 0) (U : Opens X) :
    (scalarCycleHomologySheafMap X n z hz).hom.app (op U)
        (constSection (AddCommGrpCat.of ℚ) U 1) =
      relativeHomologyToHomologySheafSection ℚ X U (n + 1)
        ((relativeHomologyProjection ℚ (TopPair.ofSubset (U : Set X)ᶜ) (n + 1)).hom
          (((SingularChainComplex ℚ X).sc (n + 1)).moduleCatHomologyClass
            (scalarAmbientCycle X n z hz))) := by
  let w := scalarAmbientCycle X n z hz
  let P := TopPair.ofSubset (X := X) (U : Set X)ᶜ
  let φ := (HomologicalComplex.shortComplexFunctor (ModuleCat.{0} ℚ) (.down ℕ) (n + 1)).map
    (relativeChainProjection ℚ P)
  let v := ShortComplex.moduleCatCycleMap φ w
  have hv : v.val = (relativeChainProjection ℚ P).f (n + 1) z := rfl
  have hnat := ShortComplex.moduleCatHomologyClass_naturality φ w
  rw [scalarCycleHomologySheafMap_constSection,
    scalarCycleHomologyPresheafMap_relative_class X n z hz U v hv]
  change relativeHomologyToHomologySheafSection ℚ X U (n + 1)
      ((((relativeChainFunctor ℚ).obj P).sc (n + 1)).moduleCatHomologyClass v) = _
  exact congrArg (fun a => relativeHomologyToHomologySheafSection ℚ X U (n + 1) a) hnat.symm

#print axioms scalarCycleHomologySheafMap_absolute_section
end HodgeLean.Foundations.RationalHomologyManifold
