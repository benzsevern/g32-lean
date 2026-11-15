import HodgeLean.Foundations.AlgebraicGeometry.ComplexTopology.Basis
import HodgeLean.Foundations.QuotientDuality.ProperCycleDefs

/-! # Contractible neighborhoods for the singular ambient scheme -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.Adapters
namespace HodgeLean.Foundations.QuotientDuality

/-- Finite-type complex points have the actual contractible open basis used by singular resolutions.
Source: Łojasiewicz, Triangulation of semi-analytic sets (1964), triangulation theorem;
HodgeLean.Foundations.ComplexTopology.finiteType_basis.
HC no distance; AV milestone no distance. -/
lemma properCycle_contractible_open_basis (X : Over (Spec ↧ℂ))
    [LocallyOfFiniteType X.hom] (x : a3b4_an X.hom)
    (U : Opens (a3b4_an X.hom)) (hx : x ∈ U) :
    ∃ V : Opens (a3b4_an X.hom), x ∈ V ∧ ContractibleSpace V ∧ V ≤ U :=
  HodgeLean.Foundations.ComplexTopology.finiteType_basis X x U hx

/-- Every analytic open in a projective complex scheme is paracompact.
Source: Munkres, Topology, section 41; compact Hausdorff spaces are locally compact,
and second-countable locally compact Hausdorff spaces are paracompact.
HC no distance; AV milestone no distance. -/
lemma properCycle_open_paracompact (X : Over (Spec ↧ℂ)) [IsProjective X.hom]
    (U : Opens (a3b4_an X.hom)) : ParacompactSpace U := by
  letI : T2Space (a3b4_an X.hom) := HodgeLean.Foundations.Analytic.f4_t2Space X
  letI : SecondCountableTopology (a3b4_an X.hom) :=
    HodgeLean.Foundations.Analytic.f4_secondCountable X
  letI : LocallyCompactSpace (a3b4_an X.hom) :=
    HodgeLean.Foundations.Analytic.an_locallyCompactSpace
      (HodgeLean.Foundations.Analytic.f4_analytification X)
  letI : LocallyCompactSpace U := U.isOpen.isOpenEmbedding_subtypeVal.locallyCompactSpace
  letI : SecondCountableTopology U := inferInstance
  letI : SigmaCompactSpace U := inferInstance
  letI : T2Space U := inferInstance
  infer_instance

end HodgeLean.Foundations.QuotientDuality
