import HodgeLean.Adapters.NormalConeB4aDefs
import Mathlib.Topology.Compactness.Paracompact

/-! # Topological hypotheses for the nonprojective support comparison

Route: finite-type separated analytifications are Hausdorff and second
countable. Their analytic charts give local compactness, also on each open.
Local compactness and sigma compactness then give paracompactness.
-/

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.Foundations.Analytic

/-- Every analytic open of a separated scheme quasi-compact and locally of finite
type over the complex numbers is paracompact. -/
theorem a3b4a_class_openParacompact
    {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ)) [LocallyOfFiniteType q]
    [QuasiCompact q] [IsSeparated q] (U : Opens (ComplexPoint (Over.mk q))) :
    ParacompactSpace U := by
  letI : LocallyOfFiniteType (Over.mk q).hom := ‹LocallyOfFiniteType q›
  letI : QuasiCompact (Over.mk q).hom := ‹QuasiCompact q›
  letI : IsSeparated (Over.mk q).hom := ‹IsSeparated q›
  letI : T2Space (ComplexPoint (Over.mk q)) := f4_t2Space (Over.mk q)
  letI : SecondCountableTopology (ComplexPoint (Over.mk q)) := f4_secondCountable (Over.mk q)
  letI : LocallyCompactSpace (ComplexPoint (Over.mk q)) :=
    an_locallyCompactSpace (f4_analytification (Over.mk q))
  letI : LocallyCompactSpace U := U.isOpen.isOpenEmbedding_subtypeVal.locallyCompactSpace
  infer_instance

end HodgeLean.Adapters
