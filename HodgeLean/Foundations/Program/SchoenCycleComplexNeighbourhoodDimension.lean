import HodgeLean.Foundations.Program.SchoenCycleSectionStandardSmooth
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- Standard smooth neighbourhoods of the images of all complex points of a surjective source locally of finite type cover every scheme point and give the stated relative dimension.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
EGA IV, 17.3.3; Hartshorne, Algebraic Geometry, II.3. -/
theorem s2e_relativeDimension_of_complex_lift_neighbourhoods
    (X Y : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    (f : X ⟶ Y) [Surjective f.left] (n : ℕ)
    (h : ∀ x : ComplexPoint X,
      ∃ (W : Y.left.Opens) (_ : IsAffineOpen W) (_ : f.left x.underlying ∈ W),
        letI := s2e_step1_sectionAlgebra Y W
        Algebra.IsStandardSmoothOfRelativeDimension n ℂ Γ(Y.left, W)) :
    SmoothOfRelativeDimension n Y.hom := by
  letI : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  constructor
  intro y
  obtain ⟨z, hz⟩ := f.left.surjective y
  obtain ⟨z', hz', hclosed⟩ := nonempty_inter_closedPoints
    (Z := closure ({z} : Set X.left)) ⟨z, subset_closure (Set.mem_singleton z)⟩
    isClosed_closure.isLocallyClosed
  let xp : ComplexPoint X := Over.homMk (pointOfClosedPoint X.hom z' hclosed) (by simp)
  have hxp : xp.underlying = z' := pointOfClosedPoint_apply X.hom z' hclosed _
  obtain ⟨W, hW, hmem, hsm⟩ := h xp
  have hsp : z ⤳ z' := specializes_iff_mem_closure.mpr hz'
  have hyW : y ∈ W := by
    rw [← hz]
    apply (hsp.map f.left.continuous).mem_open W.isOpen
    simp only [hxp] at hmem
    exact hmem
  refine ⟨⊤, isAffineOpen_top _, W, hW, hyW, (by simp), ?_⟩
  exact s2e_section_standardSmooth_dimension Y W n hsm

#print axioms s2e_relativeDimension_of_complex_lift_neighbourhoods
end HodgeLean.Foundations.Program
