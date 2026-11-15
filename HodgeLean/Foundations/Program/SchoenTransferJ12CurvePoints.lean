import HodgeLean.Foundations.Program.SchoenSelectedGeometryComplexFibers
import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.Equidimensional

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Set Topology
namespace HodgeLean.Foundations.Program

/-- An integral complex curve has distinct actual complex points. -/
theorem s4_selected_curve_points_nontrivial
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hdim : TopologicalSpace.dim Y.left = 1) : Nontrivial (ComplexPoint Y) := by
  classical
  letI : PartialOrder Y.left := specializationOrder Y.left
  by_contra hn
  letI : Subsingleton (ComplexPoint Y) := not_nontrivial_iff_subsingleton.mp hn
  letI : JacobsonSpace Y.left := LocallyOfFiniteType.jacobsonSpace Y.hom
  obtain ⟨y₀, _, hy₀⟩ := nonempty_inter_closedPoints
    (Set.univ_nonempty (α := Y.left)) isClosed_univ.isLocallyClosed
  let p₀ : ComplexPoint Y := Over.homMk (pointOfClosedPoint Y.hom y₀ hy₀)
    (pointOfClosedPoint_comp Y.hom y₀ hy₀)
  have hp₀ : p₀.underlying = y₀ := pointOfClosedPoint_apply Y.hom y₀ hy₀ _
  have hc : closedPoints Y.left ⊆ ({y₀} : Set Y.left) := by
    intro y hy
    let p : ComplexPoint Y := Over.homMk (pointOfClosedPoint Y.hom y hy)
      (pointOfClosedPoint_comp Y.hom y hy)
    have hp : p.underlying = y := pointOfClosedPoint_apply Y.hom y hy _
    exact hp.symm.trans ((congrArg Point.underlying (Subsingleton.elim p p₀)).trans hp₀)
  have hall := closure_minimal hc hy₀
  rw [closure_closedPoints] at hall
  letI : Subsingleton Y.left := ⟨fun x y =>
    (Set.mem_singleton_iff.mp (hall (Set.mem_univ x))).trans
      (Set.mem_singleton_iff.mp (hall (Set.mem_univ y))).symm⟩
  have hz : TopologicalSpace.dim Y.left = 0 := by
    simp only [TopologicalSpace.dim_eq_krullDim, Order.krullDim_eq_zero]
    norm_num
  omega

#print axioms s4_selected_curve_points_nontrivial

end HodgeLean.Foundations.Program
