import HodgeLean.Adapters.NormalConeB4aClassComponentCharts

/-! # Holomorphic charts for a smooth source open

Route: remove the discarded source from the ambient space, construct the
normal chart of the resulting immersion, and transport through the ambient
open inclusion.
-/
noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry Topology TopologicalSpace

set_option backward.isDefEq.respectTransparency false in
/-- A fixed-dimensional smooth open of a component supplies a chart for the
whole immersion image near each point of that open. -/
theorem a3b4a_classSourceOpen_exists_holomorphic_flattening
    (X Y : Over (Spec (CommRingCat.of ℂ))) (i : Y ⟶ X) (m d : ℕ)
    [Smooth X.hom] [SmoothOfRelativeDimension d X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom] [IsClosedImmersion i.left]
    (A : Y.left.Opens) [SmoothOfRelativeDimension m (ComplexPoint.openScheme Y A).hom]
    (z : ComplexPoint (ComplexPoint.openScheme Y A)) :
    ∃ e : OpenPartialHomeomorph (ComplexPoint X) ((Fin m → ℂ) × (Fin (d-m) → ℂ)),
      Point.map (ComplexPoint.openInclusion Y A ≫ i) z ∈ e.source ∧
      a3b4_IsHolChart X.hom e ∧
      ∀ x ∈ e.source, x ∈ Set.range (Point.map i) ↔ (e x).2 = 0 := by
  let O := closedImmersionSourceOpenTarget i.left A
  let OX := ComplexPoint.openScheme X O
  let AY := ComplexPoint.openScheme Y A
  let j₀ := closedImmersionSourceOpenLift i.left A
  have hj : j₀ ≫ OX.hom = AY.hom := by
    change j₀ ≫ (O.ι ≫ X.hom) = A.ι ≫ Y.hom
    rw [← Category.assoc, closedImmersionSourceOpenLift_ι, Category.assoc, i.w]
  let j : AY ⟶ OX := Over.homMk j₀ hj
  letI : IsClosedImmersion j.left := closedImmersionSourceOpenLift_isClosedImmersion i.left A
  letI : SmoothOfRelativeDimension d OX.hom := by
    change SmoothOfRelativeDimension d (O.ι ≫ X.hom)
    simpa only [Nat.zero_add] using smoothOfRelativeDimension_comp 0 d O.ι X.hom
  letI : LocallyOfFiniteType OX.hom := inferInstanceAs (LocallyOfFiniteType (O.ι ≫ X.hom))
  letI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  letI : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  letI : IsNoetherian X.left := ⟨⟩
  letI : QuasiCompact OX.hom := inferInstanceAs (QuasiCompact (O.ι ≫ X.hom))
  letI : IsSeparated OX.hom := inferInstanceAs (IsSeparated (O.ι ≫ X.hom))
  letI : Nonempty (ComplexPoint OX) := ⟨Point.map j z⟩
  obtain ⟨e, hze, he, hflat⟩ :=
    a3b4a_classSmoothClosedImmersion_exists_holomorphic_flattening OX AY j m d z
  obtain ⟨E, hE, hsource, heval⟩ :=
    a3b4a_classHolomorphicChart_openTransport X O m (d-m) e he
  let f := Point.map (ComplexPoint.openInclusion X O)
  have hpoint : f (Point.map j z) = Point.map (ComplexPoint.openInclusion Y A ≫ i) z := by
    apply Over.OverMorphism.ext
    change (z.left ≫ j₀) ≫ O.ι = z.left ≫ (A.ι ≫ i.left)
    rw [Category.assoc, closedImmersionSourceOpenLift_ι]
  have hS : f ⁻¹' Set.range (Point.map i) = Set.range (Point.map j) := by
    rw [ComplexPoint.range_map_of_isImmersion_of_comm X Y i,
      ComplexPoint.range_map_of_isImmersion_of_comm OX AY j]
    change _ = (Point.underlying : ComplexPoint OX → OX.left) ⁻¹' Set.range j₀
    rw [range_closedImmersionSourceOpenLift]
    rfl
  refine ⟨E, ?_, hE, ?_⟩
  · rw [hsource, ← hpoint]
    exact ⟨Point.map j z, hze, rfl⟩
  · intro x hx
    rw [hsource] at hx
    obtain ⟨w, hw, rfl⟩ := hx
    rw [heval]
    change w ∈ f ⁻¹' Set.range (Point.map i) ↔ _
    rw [hS]
    exact hflat w hw

end HodgeLean.Adapters
