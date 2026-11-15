import HodgeLean.Foundations.Program.SchoenTransferQ3HolomorphicAdaptedCharts
import HodgeLean.Foundations.Program.SchoenTransferQ3HolomorphicFibreCharts

/-! Actual holomorphic point charts on the algebraic normal slices. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open TopologicalSpace Topology HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The actual cartesian normal slice has a holomorphic point chart centred
at the support point, with exactly the ambient support-normal coordinates. -/
theorem s4_q3_actual_cartesian_slice_point_chart
    (S X D T : Over (Spec ↧ℂ)) (i : D ⟶ X) (h : X ⟶ T) (j : S ⟶ X) (r d : ℕ)
    [SmoothOfRelativeDimension r D.hom] [SmoothOfRelativeDimension d X.hom]
    [SmoothOfRelativeDimension r T.hom] [IsClosedImmersion i.left]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    [Etale (i ≫ h).left] (z : ComplexPoint D)
    (hsquare : IsPullback j.left S.hom h.left (Point.map (i ≫ h) z).left) :
    ∃ (xs : ComplexPoint S)
      (e : OpenPartialHomeomorph (ComplexPoint X) ((Fin r → ℂ) × (Fin (d - r) → ℂ)))
      (es : OpenPartialHomeomorph (ComplexPoint S) ((Fin 0 → ℂ) × (Fin (d - r) → ℂ))),
      Point.map j xs = Point.map i z ∧ Point.map i z ∈ e.source ∧ xs ∈ es.source ∧
      a3b4_IsHolChart X.hom e ∧ a3b4_IsHolChart S.hom es ∧
      (∀ y ∈ e.source, y ∈ Set.range (Point.map i) ↔ (e y).2 = 0) ∧
      (∀ y, (es y).2 = (e (Point.map j y)).2) ∧ es xs = 0 := by
  let t := Point.map (i ≫ h) z
  letI : IsClosedImmersion t.left := isClosedImmersion_of_comp_eq_id T.hom t.left (Over.w t)
  letI : IsClosedImmersion j.left :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) hsquare.flip inferInstance
  obtain ⟨_, hrange⟩ := s4_q3_cartesian_point_fibre_embedding j h t hsquare
  have hxrange : Point.map i z ∈ Set.range (Point.map j) := by
    rw [hrange]
    exact (Point.map_comp_apply i h z).symm
  obtain ⟨xs, hxs⟩ := hxrange
  obtain ⟨e, hxe, he, _, hflat, hlevel⟩ :=
    s4_q3_actual_holomorphic_adapted_normal_chart X D T i h r d z
  have hlevel' : ∀ m ∈ e.source, m ∈ Set.range (Point.map j) ↔
      (e m).1 = localChart T r t t := by
    intro m hm
    rw [hrange]
    exact hlevel m hm
  obtain ⟨es, _, hxes, hes, hnormal⟩ := s4_q3_holomorphic_fibre_normal_chart j r (d - r)
    e he (localChart T r t t) hlevel' xs (hxs.symm ▸ hxe)
  refine ⟨xs, e, es, hxs, hxe, hxes, he, hes, hflat, hnormal, ?_⟩
  apply Prod.ext (Subsingleton.elim _ _) ?_
  rw [hnormal, hxs]
  exact (hflat (Point.map i z) hxe).mp ⟨z, rfl⟩

end HodgeLean.Foundations.Program
