import HodgeLean.Foundations.Program.SchoenTransferR2CompactFlatDeformation
import HodgeLean.Foundations.Program.SchoenTransferR2FlatChartTransport
import HodgeLean.Foundations.Program.SchoenTransferR2ImmersionCharts
import HodgeLean.Foundations.Program.SchoenCycleC2ComponentUniquenessHelpers
import HodgeLean.Adapters.NormalConeB4aClassTopology
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ProjectiveCompact

/-! # Actual ambient deformation around a compact smooth component

HC no distance; AV milestone no distance.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.Adapters HodgeLean.Foundations.Analytic
namespace HodgeLean.Foundations.Program

/-- The actual compact smooth component has a neighbourhood mapped into it by
an ambient map homotopic to the identity, even if the ambient scheme is singular
outside the given smooth neighbourhood.
Source: Hartshorne, Algebraic Geometry, III.10; Hatcher, Algebraic Topology, §0.
HC no distance; AV milestone no distance. -/
theorem s4_assembly_component_ambient_deformation
    {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left] [Smooth Q.hom] [IsProjective Q.hom]
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
    (ι : Q ⟶ W) [IsClosedImmersion ι.left] (k : ℕ)
    (U : W.left.Opens) (hU : Set.range ι.left ⊆ U) (hsm : Smooth (U.ι ≫ W.hom))
    (hcodim : ∀ x ∈ (s2e_componentCycle ι ℚ).support, Order.coheight x = k) :
    ∃ (F : C(ComplexPoint W, ComplexPoint W)),
      Nonempty (ContinuousMap.Homotopy (ContinuousMap.id (ComplexPoint W)) F) ∧
      (∀ x ∈ Set.range (Point.map ι), F x = x) ∧
      ∃ V : Opens (ComplexPoint W), Set.range (Point.map ι) ⊆ V ∧
        Set.MapsTo F V (Set.range (Point.map ι)) := by
  letI : T2Space (ComplexPoint W) := f4_t2Space W
  letI : LocallyCompactSpace (ComplexPoint W) := an_locallyCompactSpace (f4_analytification W)
  have hcompact : IsCompact (Set.range (Point.map ι)) :=
    isCompact_range (Point.continuous_map ι)
  obtain ⟨j, hj, hji, _⟩ := s2e_componentCycle_factor_open ι U hU k hcodim
  letI : IsClosedImmersion j.left := hji
  letI : Smooth (ComplexPoint.openScheme W U).hom := hsm
  let i := ComplexPoint.openInclusion W U
  have hf : Topology.IsOpenEmbedding (Point.map i) := ComplexPoint.isOpenEmbedding_map_open W U
  apply s4_assembly_compact_flat_deformation (Set.range (Point.map ι)) hcompact
  rintro x ⟨z, rfl⟩
  obtain ⟨r, c, e, hze, hflat⟩ := s4_assembly_smooth_immersion_flat_charts j z
  have hflat' : ∀ y ∈ e.source, Point.map i y ∈ Set.range (Point.map ι) ↔ (e y).2 = 0 := by
    intro y hy
    have hpre : Point.map i y ∈ Set.range (Point.map ι) ↔ y ∈ Set.range (Point.map j) := by
      rw [← hj]
      constructor
      · rintro ⟨q, hq⟩
        exact ⟨q, hf.injective hq⟩
      · rintro ⟨q, rfl⟩
        exact ⟨q, rfl⟩
    exact hpre.trans (hflat y hy)
  letI : Nonempty (ComplexPoint (ComplexPoint.openScheme W U)) := ⟨Point.map j z⟩
  obtain ⟨E, hsource, _, hEflat⟩ :=
    s4_assembly_flat_chart_open_transport (Point.map i) hf (Set.range (Point.map ι)) e hflat'
  refine ⟨r, c, E, ?_, hEflat⟩
  rw [hsource, ← hj]
  exact ⟨Point.map j z, hze, rfl⟩

#print axioms s4_assembly_component_ambient_deformation
end HodgeLean.Foundations.Program
