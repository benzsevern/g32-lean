import HodgeLean.Foundations.BundleThom.RealProductComplementHomologyHelpers
import HodgeLean.Foundations.BundleThom.ChainCokernelHomologyZeroHelpers

/-! # Lower-degree vanishing for actual real product pairs

HC no distance; AV milestone no distance. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.BundleThom

/-- Actual real product relative homology vanishes strictly below the real normal dimension over every topological base.
Source: Hatcher, Algebraic Topology, §2.1 and §2.2, relative sequence and the two-cap induction. -/
theorem i1_realProductNormalRelativeHomology_isZero_of_lt
    (B : Type) [TopologicalSpace B] (d n : ℕ) (hn : n < d) :
    IsZero (RelativeHomology ℚ (i1_realProductNormalPair B d) n) := by
  have hd : 0 < d := by omega
  have hw : (fun _ : Fin d => (1 : ℝ)) ≠ 0 := by
    intro h
    exact one_ne_zero (congrFun h ⟨0, hd⟩)
  cases n with
  | zero =>
    haveI := i1_realProductComplementHomology_epi B d (fun _ => 1) hw 0
    change IsZero ((cokernel ((chainPairFunctor ℚ).obj (i1_realProductNormalPair B d)).hom).homology 0)
    exact i1_chainCokernelHomologyZero_isZero _
  | succ n =>
    haveI := i1_realProductComplementHomology_isIso B d n (by omega)
    haveI := i1_realProductComplementHomology_epi B d (fun _ => 1) hw (n + 1)
    exact i1_relativeHomologySuccessor_isZero (i1_realProductNormalPair B d) n

end HodgeLean.Foundations.BundleThom
