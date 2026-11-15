import HodgeLean.Foundations.Program.SchoenTransferC1a5PreProofs
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.AlgebraicTopology.SimplicialSet.Finite
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Nondegenerate
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Homology.QuasiIso

/-! Implication from the explicit inputs to a supporting construction piece.
The realization unit compares finite simplicial chains with integral singular chains.
The specified normalization transports this comparison to the finite chain model.
Finite singular homology and integral lattice transport remain later work.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory
namespace HodgeLean.Foundations.Program
/-- The realization unit, followed by a specified realization isomorphism, induces integral homology isomorphisms.
Source: Hatcher, Algebraic Topology, Theorem 2.27, simplicial and singular homology comparison; simplicial-set realization via characteristic simplices; SSet.homotopyEquivNormalizedChainComplex. -/
theorem s4_c1a5_realization_comparison_aux (K : SSet.{0}) [K.Finite]
    (X : TopCat.{0}) (e : SSet.toTop.obj K ≅ X) :
    let R := ModuleCat.of ℤ ℤ
    let u := sSetTopAdj.unit.app K ≫ TopCat.toSSet.map e.hom
    let c := SSet.chainComplexMap u R
    QuasiIso c ∧ QuasiIso (K.fromNormalizedChainComplex R ≫ c) := by
  exact s4_c1a5_pre2_assembly_aux K (s4_c1a5_pre_finite_aux K) X e

end HodgeLean.Foundations.Program
