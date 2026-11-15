import HodgeLean.Foundations.Program.SchoenCycleGeometryDefs
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

theorem s2_surjective_of_point_surjective {Y W : Over (Spec ↧ℂ)}
    [LocallyOfFiniteType W.hom] (q : Y ⟶ W) [IsProper q.left]
    (hq : Function.Surjective (Point.map q)) : Function.Surjective q.left := by
  have : JacobsonSpace W.left := LocallyOfFiniteType.jacobsonSpace W.hom
  have hr : IsClosed (Set.range q.left) := q.left.isClosedMap.isClosed_range
  have hc : closedPoints W.left ⊆ Set.range q.left := by
    intro x hx
    let p : AlgebraicGeometry.ComplexPoint W :=
      Over.homMk (pointOfClosedPoint W.hom x hx) (pointOfClosedPoint_comp W.hom x hx)
    obtain ⟨y, hy⟩ := hq p
    refine ⟨y.left (IsLocalRing.closedPoint ℂ), ?_⟩
    have he := congrArg (fun z : AlgebraicGeometry.ComplexPoint W =>
      z.left (IsLocalRing.closedPoint ℂ)) hy
    change q.left (y.left (IsLocalRing.closedPoint ℂ)) =
      pointOfClosedPoint W.hom x hx (IsLocalRing.closedPoint ℂ) at he
    exact he.trans (pointOfClosedPoint_apply W.hom x hx _)
  have hh := closure_minimal hc hr
  rw [closure_closedPoints] at hh
  exact fun x => hh (Set.mem_univ x)

theorem s2_finite_of_finite_composite {V W B : Scheme}
    (q : V ⟶ W) (β : W ⟶ B) [IsFinite (q ≫ β)] [IsProper β]
    (hq : Function.Surjective q) : IsFinite β := by
  have : LocallyQuasiFinite β := LocallyQuasiFinite.of_finite_preimage_singleton β (by
    intro x
    have he : β ⁻¹' {x} = q '' ((q ≫ β) ⁻¹' {x}) := by
      ext w
      constructor
      · intro hw
        obtain ⟨v, rfl⟩ := hq w
        exact ⟨v, hw, rfl⟩
      · rintro ⟨v, hv, rfl⟩
        exact hv
    rw [he]
    exact ((q ≫ β).finite_preimage_singleton x).image q)
  exact IsFinite.of_isProper_of_locallyQuasiFinite β

end HodgeLean.Foundations.Program
