import HodgeLean.Foundations.Program.SchoenTransferQ3SupportOpenDiagram

/-! Actual complex support points in the retained cartesian ambient restrictions. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program

/-- Compatible actual complex points lift to the specified cartesian
support square, retaining both their ambient and component coordinates. -/
theorem s4_q3_cartesian_support_point_lift
    {C X C₀ X₀ : Over (Spec ↧ℂ)}
    (i : C ⟶ X) (b : C ⟶ C₀) (a : X ⟶ X₀) (i₀ : C₀ ⟶ X₀)
    (hsquare : IsPullback i.left b.left a.left i₀.left)
    (x : ComplexPoint X) (z : ComplexPoint C₀) (he : Point.map a x = Point.map i₀ z) :
    ∃ y : ComplexPoint C, Point.map i y = x ∧ Point.map b y = z := by
  have he' : x.left ≫ a.left = z.left ≫ i₀.left := congrArg Over.Hom.left he
  let l := hsquare.lift x.left z.left he'
  let y : ComplexPoint C := Over.homMk l (by
    rw [← Over.w i, ← Category.assoc]
    change hsquare.lift x.left z.left he' ≫ i.left ≫ X.hom = _
    rw [← Category.assoc, hsquare.lift_fst]
    exact Over.w x)
  refine ⟨y, ?_, ?_⟩
  · apply Over.OverMorphism.ext
    exact hsquare.lift_fst x.left z.left he'
  · apply Over.OverMorphism.ext
    exact hsquare.lift_snd x.left z.left he'

/-- The actual cartesian support square identifies its analytic support
range with the exact inverse image of the original support range. -/
theorem s4_q3_cartesian_support_complex_range
    {C X C₀ X₀ : Over (Spec ↧ℂ)}
    (i : C ⟶ X) (b : C ⟶ C₀) (a : X ⟶ X₀) (i₀ : C₀ ⟶ X₀)
    (hsquare : IsPullback i.left b.left a.left i₀.left) :
    Point.map a ⁻¹' Set.range (Point.map i₀) = Set.range (Point.map i) := by
  have hw : i ≫ a = b ≫ i₀ := Over.OverMorphism.ext hsquare.w
  ext x
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨y, hy, _⟩ := s4_q3_cartesian_support_point_lift i b a i₀ hsquare x z hz.symm
    exact ⟨y, hy⟩
  · rintro ⟨y, rfl⟩
    refine ⟨Point.map b y, ?_⟩
    rw [← Point.map_comp_apply b i₀, ← hw, Point.map_comp_apply]

end HodgeLean.Foundations.Program
