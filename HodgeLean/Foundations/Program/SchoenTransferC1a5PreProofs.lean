import HodgeLean.Foundations.Program.SchoenTransferC1a5Pre2Proofs
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.AlgebraicTopology.SimplicialSet.Finite
import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Nondegenerate
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Homology.QuasiIso

/-! Implications from explicit inputs for integral realization comparison.
Skeleton n contains simplices of dimension strictly less than n.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory
open scoped Simplicial
namespace HodgeLean.Foundations.Program
/-- The chain comparison sends a simplex to its realized characteristic singular simplex.
Source: Mathlib sSetTopAdj_unit_app_app_down; Hatcher §2.1. -/
theorem s4_c1a5_pre_characteristic_aux (K : SSet.{0}) (n : ℕ) (σ : K _⦋n⦌) :
    (K.ιChainComplex (R := ModuleCat.of ℤ ℤ) σ ≫
        (SSet.chainComplexMap (sSetTopAdj.unit.app K) (ModuleCat.of ℤ ℤ)).f n =
      (TopCat.toSSet.obj (SSet.toTop.obj K)).ιChainComplex
        (R := ModuleCat.of ℤ ℤ)
        ((sSetTopAdj.unit.app K).app (Opposite.op ⦋n⦌) σ)) ∧
    ((sSetTopAdj.unit.app K).app (Opposite.op ⦋n⦌) σ).down =
      SSet.toTopSimplex.inv.app ⦋n⦌ ≫ SSet.toTop.map (SSet.yonedaEquiv.symm σ) := by
  exact ⟨SSet.ι_chainComplexMap_f _ _ _ _ _, sSetTopAdj_unit_app_app_down _ _ _⟩

/-- Comparison on each standard simplex.
Source: Hatcher, Algebraic Topology, §2.1, Theorem 2.27. -/
theorem s4_c1a5_pre_simplex_aux (n : ℕ) :
    QuasiIso (SSet.chainComplexMap (sSetTopAdj.unit.app (Δ[n] : SSet.{0})) (ModuleCat.of ℤ ℤ)) := by
  obtain ⟨hc, hs⟩ := s4_c1a5_pre2_augmentations_aux n
  exact s4_c1a5_pre2_simplex_transport_aux n hc hs c1a5_point_comparison

/-- Comparison on the boundary, including the empty degree zero boundary.
Source: Hatcher, Algebraic Topology, §2.1 and §2.3; Mathlib SSet.boundary. -/
theorem s4_c1a5_pre_boundary_aux (n : ℕ) :
    QuasiIso (SSet.chainComplexMap (sSetTopAdj.unit.app (SSet.boundary.{0} n : SSet)) (ModuleCat.of ℤ ℤ)) := by
  exact c1a5_bounded_unit_comparison n (SSet.boundary.{0} n : SSet)

/-- Comparison passes through the degree n cell attachments.
Source: Hatcher, Algebraic Topology, §2.3, relative homology; Mathlib SSet.skeleton. -/
theorem s4_c1a5_pre_attachment_aux (K : SSet.{0}) [K.Finite] (n : ℕ)
    (hprev : QuasiIso (SSet.chainComplexMap (sSetTopAdj.unit.app (K.skeleton n : SSet)) (ModuleCat.of ℤ ℤ)))
    (hcell : QuasiIso (SSet.chainComplexMap (sSetTopAdj.unit.app (Δ[n] : SSet.{0})) (ModuleCat.of ℤ ℤ)))
    (hboundary : QuasiIso (SSet.chainComplexMap (sSetTopAdj.unit.app (SSet.boundary.{0} n : SSet)) (ModuleCat.of ℤ ℤ))) :
    QuasiIso (SSet.chainComplexMap (sSetTopAdj.unit.app (K.skeleton (n + 1) : SSet)) (ModuleCat.of ℤ ℤ)) := by
  exact c1a5_skeletal_attachment_comparison K n hprev hcell hboundary

/-- Finite skeletal induction compares every stage.
Source: Hatcher, Algebraic Topology, §2.3; Mathlib SSet.skeleton_zero and SSet.skeleton_succ. -/
theorem s4_c1a5_pre_skeletal_aux (K : SSet.{0}) [K.Finite] (n : ℕ) :
    QuasiIso (SSet.chainComplexMap (sSetTopAdj.unit.app (K.skeleton n : SSet)) (ModuleCat.of ℤ ℤ)) := by
  induction n with
  | zero =>
    rw [K.skeleton_zero]
    exact c1a5_empty_comparison _ SSet.Subcomplex.isInitialBot
  | succ n ih =>
    exact s4_c1a5_pre_attachment_aux K n ih
      (s4_c1a5_pre_simplex_aux n) (s4_c1a5_pre_boundary_aux n)

/-- Comparison for a finite simplicial set at its final skeletal stage.
Source: Hatcher, Algebraic Topology, Theorem 2.27; Mathlib SSet.hasDimensionLT_of_finite. -/
theorem s4_c1a5_pre_finite_aux (K : SSet.{0}) [K.Finite] :
    QuasiIso (SSet.chainComplexMap (sSetTopAdj.unit.app K) (ModuleCat.of ℤ ℤ)) := by
  obtain ⟨d, hd⟩ := K.hasDimensionLT_of_finite
  have := hd
  exact c1a5_bounded_unit_comparison d K

/-- Transport through a realization isomorphism and the specified normalization inverse.
Source: Hatcher, Algebraic Topology, Theorem 2.27; Mathlib SSet.homotopyEquivNormalizedChainComplex. -/
theorem s4_c1a5_pre_assembly_aux (K : SSet.{0}) [K.Finite]
    (X : TopCat.{0}) (e : SSet.toTop.obj K ≅ X) :
    let R := ModuleCat.of ℤ ℤ
    let u := sSetTopAdj.unit.app K ≫ TopCat.toSSet.map e.hom
    let c := SSet.chainComplexMap u R
    QuasiIso c ∧ QuasiIso (K.fromNormalizedChainComplex R ≫ c) := by
  exact s4_c1a5_pre2_assembly_aux K (s4_c1a5_pre_finite_aux K) X e

end HodgeLean.Foundations.Program
