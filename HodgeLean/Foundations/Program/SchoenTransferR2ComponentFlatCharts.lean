import HodgeLean.Foundations.Program.SchoenTransferR2CompactFlatDeformation
import HodgeLean.Foundations.Program.SchoenTransferR2FlatChartTransport
import HodgeLean.Foundations.Program.SchoenTransferR2ImmersionCharts
import HodgeLean.Foundations.Program.SchoenCycleC2ComponentUniquenessHelpers
import HodgeLean.Adapters.NormalConeB4aClassTopology
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ProjectiveCompact

/-! # Flat charts in the original ambient scheme

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

/-- A smooth containing open supplies flat complex charts around every actual
point of the component in the original ambient space.
Source: Hartshorne, Algebraic Geometry, III.10; the analytic inverse function theorem.
HC no distance; AV milestone no distance. -/
theorem s4_assembly_component_flat_charts
    {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left] [Smooth Q.hom] [IsProjective Q.hom]
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
    (ι : Q ⟶ W) [IsClosedImmersion ι.left] (k : ℕ)
    (U : W.left.Opens) (hU : Set.range ι.left ⊆ U) (hsm : Smooth (U.ι ≫ W.hom))
    (hcodim : ∀ x ∈ (s2e_componentCycle ι ℚ).support, Order.coheight x = k) :
    ∀ x ∈ Set.range (Point.map ι), ∃ r c : ℕ,
      ∃ e : OpenPartialHomeomorph (ComplexPoint W) ((Fin r → ℂ) × (Fin c → ℂ)),
        x ∈ e.source ∧
          ∀ y ∈ e.source, y ∈ Set.range (Point.map ι) ↔ (e y).2 = 0 := by
  obtain ⟨j, hj, hji, _⟩ := s2e_componentCycle_factor_open ι U hU k hcodim
  letI : IsClosedImmersion j.left := hji
  letI : Smooth (ComplexPoint.openScheme W U).hom := hsm
  let i := ComplexPoint.openInclusion W U
  have hf : Topology.IsOpenEmbedding (Point.map i) := ComplexPoint.isOpenEmbedding_map_open W U
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

#print axioms s4_assembly_component_flat_charts
end HodgeLean.Foundations.Program
