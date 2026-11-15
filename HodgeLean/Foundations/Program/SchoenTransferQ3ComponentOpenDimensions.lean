import HodgeLean.Adapters.NormalConeB4aClassSmoothComponent

/-! Exact dimension of an actual smooth open in a retained source component. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- A smooth nonempty open of the original codimension-k component has
relative dimension d-k, with the dimension detected at an actual complex point. -/
theorem s4_q3_smooth_component_open_relativeDimension
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (d k : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p : X.left) (hp : Order.coheight p = k)
    (S : (cycleComponent X.left p).Opens)
    (hS : Smooth (S.ι ≫ cycleComponentι X.left p ≫ X.hom))
    (z : ComplexPoint (Over.mk (S.ι ≫ cycleComponentι X.left p ≫ X.hom))) :
    SmoothOfRelativeDimension (d - k) (S.ι ≫ cycleComponentι X.left p ≫ X.hom) := by
  let C : Over (Spec ↧ℂ) := Over.mk (cycleComponentι X.left p ≫ X.hom)
  let Z : Over (Spec ↧ℂ) := Over.mk (S.ι ≫ cycleComponentι X.left p ≫ X.hom)
  let a : Z ⟶ C := Over.homMk S.ι rfl
  letI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  letI : IsIntegral C.left := inferInstanceAs (IsIntegral (cycleComponent X.left p))
  letI : LocallyOfFiniteType C.hom :=
    inferInstanceAs (LocallyOfFiniteType (cycleComponentι X.left p ≫ X.hom))
  letI : Nonempty S.toScheme := ⟨z.underlying⟩
  letI : IsIntegral S.toScheme := isIntegral_of_isOpenImmersion S.ι
  letI : Nonempty Z.left := ⟨z.underlying⟩
  letI : IsIntegral Z.left := inferInstanceAs (IsIntegral S.toScheme)
  letI : Smooth Z.hom := hS
  obtain ⟨m, hm⟩ := Smooth.exists_smoothOfRelativeDimension Z.hom
  letI : SmoothOfRelativeDimension m Z.hom := hm
  have hzZ : IsClosed ({z.underlying} : Set Z.left) :=
    ((pointEquivClosedPoint Z.hom) ⟨z.left, Over.w z⟩).2
  have hzC : IsClosed ({(Point.map a z).underlying} : Set C.left) :=
    ((pointEquivClosedPoint C.hom) ⟨(Point.map a z).left, Over.w (Point.map a z)⟩).2
  rw [Point.underlying_map] at hzC
  have hcomponent := a3b4a_classComponent_closedPoint_coheight_eq_sub
    X (d := d) p (S.ι z.underlying) hp hzC
  have hco := coheight_eq_of_isOpenImmersion (x := z.underlying) S.ι
  have hmco := SmoothOfRelativeDimension.coheight_eq_dimension_of_isClosed
    (f := Z.hom) (d := m) z.underlying hzZ
  have hmeq : m = d - k := by
    exact_mod_cast hmco.symm.trans (hco.symm.trans hcomponent)
  subst m
  exact hm

/-- The dimension comparison also holds for an actual composed open
immersion into the original retained component. -/
theorem s4_q3_open_component_relativeDimension_eq
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (d k : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p : X.left) (hp : Order.coheight p = k)
    {Z : Over (Spec ↧ℂ)} [IsIntegral Z.left] [Smooth Z.hom]
    (r : ℕ) [SmoothOfRelativeDimension r Z.hom]
    (b : Z ⟶ Over.mk (cycleComponentι X.left p ≫ X.hom)) [IsOpenImmersion b.left]
    (z : ComplexPoint Z) : r = d - k := by
  let C : Over (Spec ↧ℂ) := Over.mk (cycleComponentι X.left p ≫ X.hom)
  letI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  letI : LocallyOfFiniteType C.hom :=
    inferInstanceAs (LocallyOfFiniteType (cycleComponentι X.left p ≫ X.hom))
  have hzZ : IsClosed ({z.underlying} : Set Z.left) :=
    ((pointEquivClosedPoint Z.hom) ⟨z.left, Over.w z⟩).2
  have hzC : IsClosed ({(Point.map b z).underlying} : Set C.left) :=
    ((pointEquivClosedPoint C.hom) ⟨(Point.map b z).left, Over.w (Point.map b z)⟩).2
  rw [Point.underlying_map] at hzC
  have hcomponent := a3b4a_classComponent_closedPoint_coheight_eq_sub
    X (d := d) p (b.left z.underlying) hp hzC
  have hco := coheight_eq_of_isOpenImmersion (x := z.underlying) b.left
  have hrco := SmoothOfRelativeDimension.coheight_eq_dimension_of_isClosed
    (f := Z.hom) (d := r) z.underlying hzZ
  exact_mod_cast hrco.symm.trans (hco.symm.trans hcomponent)

end HodgeLean.Foundations.Program
