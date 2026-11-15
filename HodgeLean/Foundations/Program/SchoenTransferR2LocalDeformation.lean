import HodgeLean.Foundations.Program.SchoenTransferR2NormalChartShrinking

/-! # Local ambient deformations around a flat support

HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
open TopologicalSpace Topology
namespace HodgeLean.Foundations.Program

/-- A flat normal chart gives an ambient deformation sending an open
neighbourhood of its marked point into the subset and fixing that subset.
Source: Hatcher, Algebraic Topology, §0; Urysohn cutoff functions.
HC no distance; AV milestone no distance. -/
theorem s4_assembly_local_flat_deformation
    {X E F : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (S : Set X) (e : OpenPartialHomeomorph X (E × F))
    (hflat : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0)
    (x : X) (hx : x ∈ S) (hxe : x ∈ e.source) :
    ∃ (U : Opens X), x ∈ U ∧ ∃ f : C(X, X),
      Nonempty (ContinuousMap.Homotopy (ContinuousMap.id X) f) ∧
        (∀ y ∈ S, f y = y) ∧ Set.MapsTo f U S := by
  obtain ⟨d, hxd, hde, hval, hstar⟩ :=
    s4_assembly_normal_chart_shrinking e x hxe ((hflat x hxe).mp hx)
  obtain ⟨K, hK, hxK, hKd⟩ := exists_compact_between isCompact_singleton
    d.open_source (Set.singleton_subset_iff.mpr hxd)
  obtain ⟨b, hbK, _, hbs, hb⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hK d.open_source hKd
  have hflatd : ∀ y ∈ d.source, y ∈ S ↔ (d y).2 = 0 := by
    intro y hy
    rw [hval y]
    exact hflat y (hde hy)
  obtain ⟨f, H, hfix, hinto⟩ := s4_assembly_flat_chart_deformation S d hflatd hstar b hbs hb
  refine ⟨⟨interior K, isOpen_interior⟩, hxK (Set.mem_singleton x), f, H, hfix, ?_⟩
  intro y hy
  apply hinto
  exact hbK (interior_subset hy)

#print axioms s4_assembly_local_flat_deformation
end HodgeLean.Foundations.Program
