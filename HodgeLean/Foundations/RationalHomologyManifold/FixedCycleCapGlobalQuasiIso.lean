import HodgeLean.Foundations.RationalHomologyManifold.FixedCycleCapGlobalComplex
import HodgeLean.Foundations.RationalHomologyManifold.FixedCycleCapInjectiveMap
import HodgeLean.Foundations.RationalHomologyManifold.FixedCycleCapQuasiIsoDescent
import HodgeLean.Foundations.RationalHomologyManifold.NaturalSoftGlobalQuasiIso
import HodgeLean.Foundations.RationalHomologyManifold.CapTargetSoftness

/-! Actual global fixed-cycle cap and the bounded soft comparison.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
open HodgeLean.Foundations.QuotientDuality
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- The actual ordinary global fixed-cycle cap map into the bounded supported-chain model is a quasi-isomorphism for a normalized cycle on a compact finite triangulated rational homology manifold.
Source: Bredon, Sheaf Theory, second edition, V.16 and VI.12; actual local cap descent and global soft comparison.
HC no distance; AV milestone no distance.
-/
theorem globalFixedCycleCapComplexHom_quasiIso (X : TopCat.{0}) [CompactSpace X] [T2Space X]
    (t : FiniteTriangulation X) (n : ℕ) (o : LocalRationalOrientation X (n + 1))
    (z : (SingularChainComplex ℚ X).X (n + 1))
    (hz : ∀ i, (SingularChainComplex ℚ X).d (n + 1) i z = 0)
    (hc : localization X (n + 1)
      (((SingularChainComplex ℚ X).sc (n + 1)).moduleCatHomologyClass
        (scalarAmbientCycle X n z (hz n))) = o.generator) :
    QuasiIso (globalFixedCycleCapComplexHom X (n + 1) z hz) := by
  let E := subdivisionGlobalSectionsFunctor X
  let G := E.mapHomologicalComplex (.up ℕ)
  let I := (TopCat.Sheaf.ambientConstantInjectiveResolution X (AddCommGrpCat.of ℚ)).cocomplex
  let j := fixedCycleCapInjectiveMap X n o z hz hc
  letI := fixedCycleCapInjectiveMap_quasiIso X n o z hz hc
  letI (p : ℕ) : Injective (I.X p) :=
    (TopCat.Sheaf.ambientConstantInjectiveResolution X (AddCommGrpCat.of ℚ)).injective p
  obtain ⟨d, ⟨h⟩, hd, hq⟩ := exists_fixedCycleCap_descent_quasiIso X t n o z hz hc I j
  have hI (p : ℕ) : IsSoft (I.X p) := by
    letI := TopCat.Sheaf.injective_isFlasque X (I.X p)
    exact spec_isSoft_of_isFlasque _
  have hS (p : ℕ) : IsSoft ((singularCochainSheafComplex ℚ X).X p) := by
    change IsSoft (singularCochainSheaf ℚ X p)
    letI : ∀ U : TopologicalSpace.Opens X, ParacompactSpace U := finiteTriangulation_opens_paracompact X t
    letI := singularCochainSheaf_isFlasque_of_opens_paracompact (R := ℚ) (X := X) p
    exact spec_isSoft_of_isFlasque _
  letI : QuasiIso (G.map j) := natural_soft_global_quasiIso X j inferInstance
    (capTargetComplex_term_isSoft X t n o) hI
  letI : QuasiIso (G.map d) := natural_soft_global_quasiIso X d hq hS hI
  letI := HodgeLean.Foundations.Program.singularGlobalComparison_quasiIso X
  have hh : Homotopy (globalFixedCycleCapComplexHom X (n + 1) z hz ≫ G.map j)
      (HodgeLean.Foundations.Program.singularGlobalComparison X ≫ G.map d) := by
    have hh := (E.mapHomotopy h).compLeft (ambientCochainGlobalUnit X)
    simp only [Functor.map_comp, ← Category.assoc] at hh
    change Homotopy (globalFixedCycleCapComplexHom X (n + 1) z hz ≫ G.map j)
      ((ambientCochainGlobalUnit X ≫ G.map (ambientCochainSheafRestriction X)) ≫ G.map d) at hh
    have hr : ambientCochainGlobalUnit X ≫ G.map (ambientCochainSheafRestriction X) =
        HodgeLean.Foundations.Program.singularGlobalComparison X := ambientCochainGlobalUnit_restriction X
    rw [hr] at hh
    exact hh
  haveI : QuasiIso (globalFixedCycleCapComplexHom X (n + 1) z hz ≫ G.map j) := by
    rw [quasiIso_iff]
    intro i
    rw [quasiIsoAt_iff_isIso_homologyMap, hh.homologyMap_eq i]
    infer_instance
  exact quasiIso_of_comp_right (globalFixedCycleCapComplexHom X (n + 1) z hz) (G.map j)

#print axioms globalFixedCycleCapComplexHom_quasiIso
end HodgeLean.Foundations.RationalHomologyManifold
