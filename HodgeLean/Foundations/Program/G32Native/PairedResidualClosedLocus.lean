import HodgeLean.Foundations.Program.SchoenCycleC11DegreeHelpers
import HodgeLean.Foundations.Program.SchoenCycleSliceHelpers

/-! # Closed scheme loci detected on the retained complex points -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- A closed locus containing all mapped complex points contains the entire scheme image. -/
theorem residual_range_in_closed_locus
    (X Y : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    (f : X ⟶ Y) (K : TopologicalSpace.Closeds Y.left)
    (h : ∀ p : ComplexPoint X, (Point.map f p).underlying ∈ K) :
    Set.range f.left ⊆ K := by
  haveI : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  rintro _ ⟨x, rfl⟩
  by_contra hx
  let U : Set X.left := f.left ⁻¹' (K : Set Y.left)ᶜ
  have hU : IsOpen U := K.isClosed.isOpen_compl.preimage f.left.continuous
  obtain ⟨z, hzU, hz⟩ := nonempty_inter_closedPoints (show U.Nonempty from ⟨x, hx⟩)
    hU.isLocallyClosed
  let p : ComplexPoint X := Over.homMk (pointOfClosedPoint X.hom z hz)
    (pointOfClosedPoint_comp X.hom z hz)
  have hp : p.underlying = z := pointOfClosedPoint_apply X.hom z hz _
  have hh := h p
  rw [Point.underlying_map, hp] at hh
  exact hzU hh

#print axioms residual_range_in_closed_locus

/-- A reduced source factors through the reduced closed locus containing its complex-point image. -/
theorem residual_factor_closed_locus
    (X Y : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom] [IsReduced X.left]
    (f : X ⟶ Y) (K : TopologicalSpace.Closeds Y.left)
    (h : ∀ p : ComplexPoint X, (Point.map f p).underlying ∈ K) :
    ∃ a : X ⟶ s2c_subscheme Y (Scheme.IdealSheafData.vanishingIdeal K),
      a ≫ s2c_subschemeι Y (Scheme.IdealSheafData.vanishingIdeal K) = f := by
  let I := Scheme.IdealSheafData.vanishingIdeal K
  have hk : I ≤ f.left.ker := by
    rw [s2e_reduced_image_ideal f.left]
    apply Scheme.IdealSheafData.vanishingIdeal_antimono
    change closure (Set.range f.left) ⊆ (K : Set Y.left)
    exact K.isClosed.closure_subset_iff.mpr (residual_range_in_closed_locus X Y f K h)
  let l := IsClosedImmersion.lift I.subschemeι f.left
    (by rw [Scheme.IdealSheafData.ker_subschemeι]; exact hk)
  have hl : l ≫ I.subschemeι = f.left := IsClosedImmersion.lift_fac _ _ _
  let a : X ⟶ s2c_subscheme Y I := Over.homMk l (by
    change l ≫ (I.subschemeι ≫ Y.hom) = X.hom
    rw [← Category.assoc, hl, Over.w f])
  exact ⟨a, Over.OverMorphism.ext hl⟩

#print axioms residual_factor_closed_locus

end HodgeLean.Foundations.Program.G32Native
