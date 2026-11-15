import HodgeLean.Foundations.QuotientDuality.ProperCycleGenericOpenFibreDegree
import HodgeLean.Foundations.Program.SchoenCycleC11Sub

/-! # Actual complex fibre equivalences under target open restriction -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual source open inclusion identifies its restricted complex fibre with the literal original complex fibre over the same target point.
Source: SGA 1, Expose XII, section 1, analytification of open immersions and fibres.
HC no distance; AV milestone no distance. -/
def properCycle_restricted_complex_fibre_equiv
    (X Y : Over (Spec ↧ℂ)) (f : X ⟶ Y) (U : Y.left.Opens)
    (y : ComplexPoint (openScheme Y U)) :
    ((Point.map (s2e_c11_restricted_over_morphism X Y f U)) ⁻¹' {y}) ≃
      ((Point.map f) ⁻¹' {Point.map (openInclusion Y U) y}) := by
  let fU := s2e_c11_restricted_over_morphism X Y f U
  let jX := openInclusion X (f.left ⁻¹ᵁ U)
  let jY := openInclusion Y U
  haveI : Mono jX := Over.mono_of_mono_left jX
  haveI : Mono jY := Over.mono_of_mono_left jY
  have hsquare : fU ≫ jY = jX ≫ f := s2e_c11_restricted_over_morphism_inclusion X Y f U
  let A := (Point.map fU) ⁻¹' {y}
  let B := (Point.map f) ⁻¹' {Point.map jY y}
  let φ : A → B := fun z => ⟨Point.map jX z.val, by
    change Point.map f (Point.map jX z.val) = Point.map jY y
    rw [← Point.map_comp_apply, ← hsquare, Point.map_comp_apply, z.property]⟩
  have hi : Function.Injective φ := by
    intro z w hzw
    apply Subtype.ext
    exact map_injective_of_mono jX (congrArg Subtype.val hzw)
  have he : Function.Surjective φ := by
    intro v
    have hy : Point.map jY y ∈ Point.overOpen U := (openHomeomorph Y U y).property
    have hv : v.val ∈ Point.overOpen (f.left ⁻¹ᵁ U) := by
      apply (Point.mem_overOpen_map_iff f v.val U).mp
      rw [v.property]
      exact hy
    let e := openHomeomorph X (f.left ⁻¹ᵁ U)
    let x := e.symm ⟨v.val, hv⟩
    have hx : Point.map jX x = v.val := congrArg Subtype.val (e.apply_symm_apply ⟨v.val, hv⟩)
    have hxy : Point.map fU x = y := by
      apply map_injective_of_mono jY
      rw [← Point.map_comp_apply, hsquare, Point.map_comp_apply, hx]
      exact v.property
    exact ⟨⟨x, hxy⟩, Subtype.ext hx⟩
  exact Equiv.ofBijective φ ⟨hi, he⟩

/-- The original complex fibre is finite when the original morphism is finite only over the actual target open containing that fibre.
Source: SGA 1, Expose I, finite morphisms and geometric fibres; Expose XII, analytification of open immersions.
HC no distance; AV milestone no distance. -/
lemma properCycle_complex_fibre_finite_of_finite_target_open
    (X Y : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (U : Y.left.Opens) [IsFinite (f.left ∣_ U)]
    (y : ComplexPoint (openScheme Y U)) :
    ((Point.map f) ⁻¹' {Point.map (openInclusion Y U) y}).Finite := by
  let XU := openScheme X (f.left ⁻¹ᵁ U)
  let YU := openScheme Y U
  let g := s2e_c11_restricted_over_morphism X Y f U
  letI : LocallyOfFiniteType XU.hom :=
    inferInstanceAs (LocallyOfFiniteType ((f.left ⁻¹ᵁ U).ι ≫ X.hom))
  letI : LocallyOfFiniteType YU.hom := inferInstanceAs (LocallyOfFiniteType (U.ι ≫ Y.hom))
  letI : IsFinite g.left := inferInstanceAs (IsFinite (f.left ∣_ U))
  have hfinite := s2e_c11_finite_point_fibres XU YU g y
  letI := hfinite.fintype
  letI : Finite ((Point.map f) ⁻¹' {Point.map (openInclusion Y U) y}) :=
    Finite.of_equiv ((Point.map g) ⁻¹' {y}) (properCycle_restricted_complex_fibre_equiv X Y f U y)
  exact Set.toFinite _

end HodgeLean.Foundations.QuotientDuality
