import HodgeLean.Foundations.Program.SchoenTransferQ3Generalizing
import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.PointwiseDimension

/-! Relative dimensions in the actual open finite comparison. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- An open quasi-finite map has the same smooth ambient dimension on
both sides, as detected at an actual complex source point. -/
theorem s4_q3_relativeDimensions_eq_of_open_quasiFinite
    {X W : Over (Spec ↧ℂ)} [IsIntegral X.left] [IsIntegral W.left]
    [Smooth X.hom] [Smooth W.hom] (d e : ℕ)
    [SmoothOfRelativeDimension d X.hom] [SmoothOfRelativeDimension e W.hom]
    [QuasiCompact X.hom] (q : X ⟶ W) [LocallyQuasiFinite q.left]
    (hq : IsOpenMap q.left) (x : ComplexPoint X) : d = e := by
  letI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  letI : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  letI : IsNoetherian X.left := {}
  have hx : IsClosed ({x.underlying} : Set X.left) :=
    ((pointEquivClosedPoint X.hom) ⟨x.left, Over.w x⟩).2
  have hy : IsClosed ({(Point.map q x).underlying} : Set W.left) :=
    ((pointEquivClosedPoint W.hom) ⟨(Point.map q x).left, Over.w (Point.map q x)⟩).2
  have hd := SmoothOfRelativeDimension.coheight_eq_dimension_of_isClosed
    (f := X.hom) (d := d) x.underlying hx
  have he := SmoothOfRelativeDimension.coheight_eq_dimension_of_isClosed
    (f := W.hom) (d := e) (Point.map q x).underlying hy
  have hco := s4_q3_coheight_eq_of_open_quasiFinite q.left hq x.underlying
  rw [hd, ← Point.underlying_map, he] at hco
  exact_mod_cast hco

end HodgeLean.Foundations.Program
