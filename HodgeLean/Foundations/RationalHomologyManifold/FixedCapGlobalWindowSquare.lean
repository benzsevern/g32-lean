import HodgeLean.Foundations.RationalHomologyManifold.SingularCapTargetStandardWindow
import HodgeLean.Foundations.RationalHomologyManifold.GlobalCapSourceWindow
import HodgeLean.Foundations.RationalHomologyManifold.GlobalFixedCapMiddle
import HodgeLean.Foundations.RationalHomologyManifold.FixedCapCycleTransport

/-! The actual fixed cap and global bounded cap window have the same middle component.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicTopology.Singular AlgebraicTopology.Simplicial
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- The original fixed-cycle cap short-complex morphism agrees in its literal middle component with the checked global bounded cap map after the original singular-chain window comparison.
Source: Hatcher, Algebraic Topology, section 3.3; Bredon, Sheaf Theory, second edition, VI.12.
HC no distance; AV milestone no distance.
-/
theorem fixedCycleCapHom_global_window_middle (X : TopCat.{0}) (p q : ℕ)
    (z : ChainGroup ℚ (TopCat.toSSet.obj X) (p + q + 2))
    (hz : boundary ℚ (p + q + 1) z = 0) :
    (((forget₂ (ModuleCat ℚ) AddCommGrpCat).mapShortComplex.map (fixedCycleCapHom X p q z hz)) ≫
        singularCapTargetStandardWindowComparison X p q).τ₂ =
      (globalFixedCycleCapWindow X p q z (fixedCapCycle_all_differentials X p q z hz)).τ₂ := by
  let E := subdivisionGlobalSectionsFunctor X
  let F := forget₂ (ModuleCat ℚ) AddCommGrpCat
  let hN : (p + 1) + (q + 1) = p + q + 2 := by omega
  let e := capTargetTermIso X (p + q + 2) (p + 1) (q + 1) (by omega) hN
  have hm : (F.mapShortComplex.map (fixedCycleCapHom X p q z hz)).τ₂ =
      AddCommGrpCat.ofHom (((capLinear ℚ (p + 1) (q + 1)).flip
        (((SingularChainComplex ℚ X).XIsoOfEq hN.symm).hom z)).toAddMonoidHom) := by
    change F.map (fixedCycleCapHom X p q z hz).τ₂ = _
    rw [fixedCycleCapHom_middle]
    rfl
  rw [ShortComplex.comp_τ₂, hm, singularCapTargetStandardWindowComparison_middle,
    singularCapTargetWindowComparison_middle, globalFixedCycleCapWindow_middle]
  apply (cancel_mono (E.map e.hom)).mp
  simp only [Category.assoc]
  rw [← E.map_comp, Iso.inv_hom_id, E.map_id]
  exact (congrArg (fun k => AddCommGrpCat.ofHom
    (((capLinear ℚ (p + 1) (q + 1)).flip
      (((SingularChainComplex ℚ X).XIsoOfEq hN.symm).hom z)).toAddMonoidHom) ≫ k)
    (Category.comp_id (subdivisionAmbientSectionMap X (q + 1) ⊤ 0))).trans
    (globalFixedCycleCapComplexHom_component X (p + q + 2) (p + 1) (q + 1)
    (by omega) hN z (fixedCapCycle_all_differentials X p q z hz)).symm

#print axioms fixedCycleCapHom_global_window_middle
end HodgeLean.Foundations.RationalHomologyManifold
