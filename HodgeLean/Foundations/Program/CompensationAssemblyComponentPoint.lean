import HodgeLean.Foundations.Program.CompensationAssemblyRelativeGerm
import HodgeLean.Foundations.Program.CompensationAssemblyFiniteEtale

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 10000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

theorem cq_componentBoundary_singleton
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (x : X.left) :
    ccm5_componentBoundary X 1 (fun _ => x) = cycleComponentSingularAnalyticClosedFiltration X x 0 := by
  classical
  have hp : (⨆ i : Fin 1, ⨆ j : Fin 1,
      if i = j then (⊥ : Closeds (ComplexPoint X)) else
        cycleComponentAnalyticClosedSupport X x ⊓ cycleComponentAnalyticClosedSupport X x) = ⊥ := by
    apply le_antisymm _ bot_le
    apply iSup_le
    intro i
    apply iSup_le
    intro j
    rw [if_pos (Subsingleton.elim i j)]
  change (⨆ _ : Fin 1, cycleComponentSingularAnalyticClosedFiltration X x 0) ⊔ _ = _
  rw [hp, iSup_const, sup_bot_eq]

theorem cq_component_regular_complex_point_on_open
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (x : X.left) (U : (a2r_component X x).left.Opens)
    (hU : (U : Set (a2r_component X x).left).Nonempty) :
    ∃ z : ComplexPoint (a2r_component X x), z.underlying ∈ U ∧
      Point.map (Over.homMk (cycleComponentι X.left x) rfl) z ∈
        cycleComponentAnalyticClosedSupport X x ∧
      Point.map (Over.homMk (cycleComponentι X.left x) rfl) z ∈
        (ccm5_componentBoundary X 1 (fun _ => x)).compl := by
  obtain ⟨z, hz, hzU⟩ := (dense_cycleComponent_smooth_closedPoints X x).exists_mem_open U.isOpen hU
  let Z := a2r_component X x
  let q := (pointEquivClosedPoint Z.hom).symm ⟨z, hz.2⟩
  let b : ComplexPoint Z := Over.homMk q.1 q.2
  have hb : b.underlying = z := pointOfClosedPoint_apply Z.hom z hz.2 _
  refine ⟨b, hb.symm ▸ hzU, ?_, ?_⟩
  · change cycleComponentι X.left x b.underlying ∈ closure ({x} : Set X.left)
    rw [← range_cycleComponentι]
    exact ⟨b.underlying, rfl⟩
  · rw [cq_componentBoundary_singleton]
    change cycleComponentι X.left x b.underlying ∉
      (cycleComponentι X.left x '' (cycleComponentSingularClosedFiltration X x 0 : Set _))
    rw [hb]
    rintro ⟨w, hw, he⟩
    have heq : w = z := (cycleComponentι X.left x).isClosedEmbedding.injective he
    subst w
    change z ∉ (cycleComponentι X.left x ≫ X.hom).smoothLocus at hw
    exact hw hz.1

end HodgeLean.Foundations.Program
