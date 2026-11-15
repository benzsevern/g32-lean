import HodgeLean.Foundations.Program.SchoenTransferQ3ActualSliceCharts

/-! Compatible point charts on the source and target of an actual normal slice. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The two actual cartesian fibres have centred holomorphic point charts
with their ambient normal coordinates and compatible marked points. -/
theorem s4_q3_paired_cartesian_slice_point_charts
    (P Q X W C D T : Over (Spec ↧ℂ))
    (i : C ⟶ X) (j : D ⟶ W) (f : C ⟶ D) (q : X ⟶ W) (h : W ⟶ T)
    (u : P ⟶ X) (v : Q ⟶ W) (g : P ⟶ Q) (r d : ℕ)
    [SmoothOfRelativeDimension r C.hom] [SmoothOfRelativeDimension r D.hom]
    [SmoothOfRelativeDimension d X.hom] [SmoothOfRelativeDimension d W.hom]
    [SmoothOfRelativeDimension r T.hom]
    [IsClosedImmersion i.left] [IsClosedImmersion j.left]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
    [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
    [LocallyOfFiniteType Q.hom] [QuasiCompact Q.hom] [IsSeparated Q.hom]
    [Etale (i ≫ q ≫ h).left] [Etale (j ≫ h).left]
    (z : ComplexPoint C) (hsupport : i ≫ q = f ≫ j)
    (hslice : u ≫ q = g ≫ v)
    (hP : IsPullback u.left P.hom (q ≫ h).left (Point.map (i ≫ q ≫ h) z).left)
    (hQ : IsPullback v.left Q.hom h.left (Point.map (j ≫ h) (Point.map f z)).left) :
    ∃ (xp : ComplexPoint P) (xq : ComplexPoint Q)
      (eX : OpenPartialHomeomorph (ComplexPoint X) ((Fin r → ℂ) × (Fin (d - r) → ℂ)))
      (eW : OpenPartialHomeomorph (ComplexPoint W) ((Fin r → ℂ) × (Fin (d - r) → ℂ)))
      (sP : OpenPartialHomeomorph (ComplexPoint P) ((Fin 0 → ℂ) × (Fin (d - r) → ℂ)))
      (sQ : OpenPartialHomeomorph (ComplexPoint Q) ((Fin 0 → ℂ) × (Fin (d - r) → ℂ))),
      Point.map u xp = Point.map i z ∧ Point.map v xq = Point.map j (Point.map f z) ∧
      Point.map g xp = xq ∧
      Point.map i z ∈ eX.source ∧ Point.map j (Point.map f z) ∈ eW.source ∧
      xp ∈ sP.source ∧ xq ∈ sQ.source ∧
      a3b4_IsHolChart X.hom eX ∧ a3b4_IsHolChart W.hom eW ∧
      a3b4_IsHolChart P.hom sP ∧ a3b4_IsHolChart Q.hom sQ ∧
      (∀ y ∈ eX.source, y ∈ Set.range (Point.map i) ↔ (eX y).2 = 0) ∧
      (∀ y ∈ eW.source, y ∈ Set.range (Point.map j) ↔ (eW y).2 = 0) ∧
      (∀ y, (sP y).2 = (eX (Point.map u y)).2) ∧
      (∀ y, (sQ y).2 = (eW (Point.map v y)).2) ∧ sP xp = 0 ∧ sQ xq = 0 := by
  obtain ⟨xp, eX, sP, hxp, hxX, hxP, heX, hsP, hfX, hnP, hP0⟩ :=
    s4_q3_actual_cartesian_slice_point_chart P X C T i (q ≫ h) u r d z hP
  obtain ⟨xq, eW, sQ, hxq, hxW, hxQ, heW, hsQ, hfW, hnQ, hQ0⟩ :=
    s4_q3_actual_cartesian_slice_point_chart Q W D T j h v r d (Point.map f z) hQ
  have hg : Point.map g xp = xq := by
    let t := Point.map (j ≫ h) (Point.map f z)
    letI : IsClosedImmersion t.left := isClosedImmersion_of_comp_eq_id T.hom t.left (Over.w t)
    letI : IsClosedImmersion v.left :=
      MorphismProperty.of_isPullback (P := @IsClosedImmersion) hQ.flip inferInstance
    apply (ComplexPoint.isClosedEmbedding_map_of_closedImmersion v).injective
    rw [← Point.map_comp_apply, ← hslice, Point.map_comp_apply, hxp, ← Point.map_comp_apply,
      hsupport, Point.map_comp_apply, hxq]
  exact ⟨xp, xq, eX, eW, sP, sQ, hxp, hxq, hg, hxX, hxW, hxP, hxQ,
    heX, heW, hsP, hsQ, hfX, hfW, hnP, hnQ, hP0, hQ0⟩

end HodgeLean.Foundations.Program
