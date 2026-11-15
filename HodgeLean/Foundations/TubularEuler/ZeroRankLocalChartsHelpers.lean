import HodgeLean.Foundations.TubularEuler.ZeroRankAmbientHelpers
import HodgeLean.Foundations.TubularEuler.ZeroRankNormalHelpers
import HodgeLean.Foundations.TubularEuler.TubeDefs
import HodgeLean.Foundations.Program.SchoenCycleC2SupportHelpers

/-! # Local normal coordinates for the original rank-zero immersion

The local maps retain the prescribed normal topology and ambient inclusion.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Topology Bundle
open HodgeLean.Foundations.Program HodgeLean.Adapters
namespace HodgeLean.Foundations.TubularEuler
open BundleThom

variable {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left]
variable [LocallyOfFiniteType Q.hom] [QuasiCompact Q.hom] [IsSeparated Q.hom]
variable [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
variable (ι : Q ⟶ W) [IsClosedImmersion ι.left]
variable {V : Scheme} (v : V ⟶ W.left) [IsOpenImmersion v]
variable (j : Q.left ⟶ V) [IsClosedImmersion j] (hj : j ≫ v = ι.left)
variable [SmoothOfRelativeDimension 0 Q.hom]
variable [SmoothOfRelativeDimension 0 (v ≫ W.hom)]
private local instance normalFibreTop (x : ComplexPoint Q) :
    TopologicalSpace (i1_normalFibre j x) := i1_normalFibreTopology j x
private local instance normalTotalTop :
    TopologicalSpace (TotalSpace (Fin 0 → ℂ) (i1_normalFibre j)) :=
  i1_normalTotalTopology j 0

include v hj in
theorem zeroRankLocalCharts
    (L : OpenPartialHomeomorph (TotalSpace (Fin 0 → ℂ) (i1_normalFibre j)) (ComplexPoint W))
    (hL : ∀ z ∈ L.source, L z = Point.map ι z.proj)
    (z : TotalSpace (Fin 0 → ℂ) (i1_normalFibre j)) (hz : z ∈ L.source) :
    ∃ (b : OpenPartialHomeomorph (ComplexPoint Q) (Fin 0 → ℂ))
      (e : Trivialization (Fin 0 → ℂ) (π (Fin 0 → ℂ) (i1_normalFibre j)))
      (a : OpenPartialHomeomorph (ComplexPoint W) ((Fin 0 → ℂ) × (Fin 0 → ℂ))),
      a3b4_IsHolChart Q.hom (b.trans
        ((Homeomorph.prodUnique (Fin 0 → ℂ) (Fin 0 → ℂ)).symm.toOpenPartialHomeomorph)) ∧
      e.IsLinear ℂ ∧ a3b4_IsHolChart W.hom a ∧
      z.proj ∈ b.source ∧ z ∈ e.source ∧ L z ∈ a.source ∧
      (∀ y ∈ a.source, y ∈ a3b4_cycleSupport W.hom (s2e_componentCycle ι ℚ) ↔
        (a y).2 = 0) ∧
      let c := ((e.toOpenPartialHomeomorph.trans
        (b.prod (OpenPartialHomeomorph.refl (Fin 0 → ℂ)))).symm.trans L).trans a
      (b z.proj, (0 : Fin 0 → ℂ)) ∈ c.source ∧
      ContDiffOn ℝ ⊤ c c.source ∧ ContDiffOn ℝ ⊤ c.symm c.target ∧
      ∃ A : (Fin 0 → ℂ) ≃L[ℂ] (Fin 0 → ℂ),
        HasFDerivAt (fun w : Fin 0 → ℂ => (c (b z.proj, w)).2)
          A.toContinuousLinearMap 0 := by
  letI := complexPoint_discreteTopology_of_smooth_zero Q
  let fr := i1_smoothConormalFrameAt j 0 (v ≫ W.hom)
    (Over.w (i1_smoothLift ι v j hj)) z.proj
  let b := isolatedPointChart (F := Fin 0 → ℂ) z.proj (isOpen_discrete _)
  let e := i1_normalFrameTrivialization j 0 fr.1 fr.2.1
  have hopen : IsOpen ({Point.map ι z.proj} : Set (ComplexPoint W)) := by
    simpa only [Set.image_singleton] using
      (zeroRankImmersion_points_isOpenEmbedding ι v j hj).isOpenMap
        {z.proj} (isOpen_discrete _)
  letI : Unique ((Fin 0 → ℂ) × (Fin 0 → ℂ)) :=
    ⟨⟨0⟩, fun _ => Subsingleton.elim _ _⟩
  let a := isolatedPointChart (F := (Fin 0 → ℂ) × (Fin 0 → ℂ)) (Point.map ι z.proj) hopen
  have he : e.IsLinear ℂ := i1_normalFrameTrivialization_isLinear j 0 fr.1 fr.2.1
  have hzb : z.proj ∈ b.source := Set.mem_singleton _
  have hze : z ∈ e.source := fr.2.2
  have hza : L z ∈ a.source := by
    change L z ∈ ({Point.map ι z.proj} : Set (ComplexPoint W))
    exact Set.mem_singleton_iff.mpr (hL z hz)
  let P := e.toOpenPartialHomeomorph.trans (b.prod (OpenPartialHomeomorph.refl (Fin 0 → ℂ)))
  let c := (P.symm.trans L).trans a
  have hzP : z ∈ P.source := by
    refine ⟨hze, ?_⟩
    change (e z).1 ∈ b.source ∧ (e z).2 ∈ Set.univ
    rw [e.coe_fst' (e.mem_source.mp hze)]
    exact ⟨hzb, Set.mem_univ _⟩
  have hcz : P z ∈ c.source := by
    change (P z ∈ P.target ∧ P.symm (P z) ∈ L.source) ∧ L (P.symm (P z)) ∈ a.source
    rw [P.left_inv hzP]
    exact ⟨⟨P.map_source hzP, hz⟩, hza⟩
  have hP : P z = (b z.proj, (0 : Fin 0 → ℂ)) := Subsingleton.elim _ _
  rw [hP] at hcz
  refine ⟨b, e, a, ?_, he, ?_, hzb, hze, hza, ?_, hcz,
    contDiffOn_of_subsingleton, contDiffOn_of_subsingleton, ContinuousLinearEquiv.refl ℂ _, ?_⟩
  · constructor <;> intro i <;> exact Fin.elim0 i
  · constructor <;> intro i <;> exact Fin.elim0 i
  · intro y hy
    have hy' : y = Point.map ι z.proj := by
      change y ∈ ({Point.map ι z.proj} : Set (ComplexPoint W)) at hy
      exact Set.mem_singleton_iff.mp hy
    have hs : Point.map ι z.proj ∈ a3b4_cycleSupport W.hom (s2e_componentCycle ι ℚ) := by
      rw [s2e_componentCycle_analytic_support]
      exact ⟨z.proj.underlying, rfl⟩
    exact iff_of_true (hy'.symm ▸ hs) (Subsingleton.elim _ _)
  · have hA : (ContinuousLinearEquiv.refl ℂ (Fin 0 → ℂ)).toContinuousLinearMap = 0 :=
      Subsingleton.elim _ _
    rw [hA]
    exact hasFDerivAt_of_subsingleton _ _

#print axioms zeroRankLocalCharts

end HodgeLean.Foundations.TubularEuler
