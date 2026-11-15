import HodgeLean.Foundations.RationalHomologyManifold.Defs
import HodgeLean.Foundations.Program.SchoenTransferQ2a1
import HodgeLean.Foundations.Topology.RationalSheafComparison
import Mathlib.Topology.EMetricSpace.Paracompact

/-! The cohomology side of the finite-polyhedron sheaf comparison.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- A finite triangulation supplies a basis of open contractible neighborhoods.
Source: Hatcher, Algebraic Topology, Appendix A, local topology of polyhedra.
HC no distance; AV milestone no distance.
-/
theorem finiteTriangulation_contractible_basis (X : TopCat.{0}) (t : FiniteTriangulation X)
    (x : X) (U : Opens X) (hx : x ∈ U) :
    ∃ V : Opens X, x ∈ V ∧ ContractibleSpace V ∧ V ≤ U := by
  let e := t.realization
  obtain ⟨V, hVo, hxV, hVU, hVC⟩ :=
    HodgeLean.Foundations.Program.s4_q2a1_open_basis t.ambient t.complex t.finite_faces
      (e.symm x) (e ⁻¹' (U : Set X))
      ((U.isOpen.preimage e.continuous).mem_nhds (by simpa using hx))
  let W : Opens X := ⟨e '' V, e.isOpenMap V hVo⟩
  refine ⟨W, ⟨e.symm x, hxV, e.apply_symm_apply x⟩, ?_, ?_⟩
  · letI := hVC
    exact (e.image V).symm.contractibleSpace
  · rintro y ⟨v, hv, rfl⟩
    exact hVU hv

#print axioms finiteTriangulation_contractible_basis
/-- All open subsets of a finite triangulated space are paracompact.
Source: Hatcher, Algebraic Topology, Appendix A, finite polyhedra as metrizable spaces.
HC no distance; AV milestone no distance.
-/
theorem finiteTriangulation_opens_paracompact (X : TopCat.{0}) (t : FiniteTriangulation X)
    (U : Opens X) : ParacompactSpace U := by
  letI : MetrizableSpace X := t.realization.symm.isEmbedding.metrizableSpace
  letI : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  infer_instance

#print axioms finiteTriangulation_opens_paracompact
/-- The canonical singular-to-constant-sheaf comparison is rationally linear and bijective.
Source: Bredon, Sheaf Theory, second edition, II.4, II.6 and III.1.
HC no distance; AV milestone no distance.
-/
theorem finiteTriangulation_cohomology_comparison (X : TopCat.{0}) [T2Space X]
    (t : FiniteTriangulation X) (n : ℕ) :
    Function.Bijective (HodgeLean.Topology.RationalSheafComparison.comparison X
      (finiteTriangulation_contractible_basis X t) n) ∧
    ∃ e : Cohomology ℚ X n ≃ₗ[ℚ]
      Sheaf.H (HodgeLean.Topology.RationalSheafComparison.constants X) n,
      ∀ v, e v = HodgeLean.Topology.RationalSheafComparison.comparison X
        (finiteTriangulation_contractible_basis X t) n v := by
  letI : ∀ U : Opens X, ParacompactSpace U := finiteTriangulation_opens_paracompact X t
  exact HodgeLean.Topology.RationalSheafComparison.comparison_linearEquiv X
    (finiteTriangulation_contractible_basis X t) n

#print axioms finiteTriangulation_cohomology_comparison
end HodgeLean.Foundations.RationalHomologyManifold
