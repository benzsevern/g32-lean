import HodgeLean.Foundations.Program.SchoenCycleC11EtaleSmoothHelpers
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ClosedImmersion
import Mathlib.SetTheory.Cardinal.Finite

/-! # Fibre sizes under actual cover isomorphisms and restrictions -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program

/-- A commuting isomorphism square preserves the cardinality of the actual
complex fibres. -/
theorem s2e_c1_fibre_card_of_iso_square
    {X X' Y Y' : Over (Spec ↧ℂ)} (f : X ⟶ Y) (g : X' ⟶ Y')
    (eX : X ≅ X') (eY : Y ≅ Y') (h : eX.hom ≫ g = f ≫ eY.hom)
    (y : ComplexPoint Y) :
    Nat.card ((Point.map f) ⁻¹' {y}) =
      Nat.card ((Point.map g) ⁻¹' {Point.map eY.hom y}) := by
  apply Nat.card_congr
  apply (Point.isoMapHomeomorph eX).toEquiv.subtypeEquiv
  intro x
  change Point.map f x = y ↔ Point.map g (Point.map eX.hom x) = Point.map eY.hom y
  rw [← Point.map_comp_apply, h, Point.map_comp_apply]
  exact (map_injective_of_mono eY.hom).eq_iff.symm

/-- Restriction to a base open preserves the actual complex fibre over
every point of that open. -/
theorem s2e_c1_restricted_complex_fibre_card
    (X Y : Over (Spec ↧ℂ)) (f : X ⟶ Y) (U : Y.left.Opens)
    (y : ComplexPoint (openScheme Y U)) :
    Nat.card ((Point.map (s2e_c11_restricted_over_morphism X Y f U)) ⁻¹' {y}) =
      Nat.card ((Point.map f) ⁻¹' {Point.map (openInclusion Y U) y}) := by
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
  exact Nat.card_congr (Equiv.ofBijective φ ⟨hi, he⟩)

end HodgeLean.Foundations.Program
