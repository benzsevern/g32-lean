import HodgeLean.Foundations.Program.SchoenCycleC1DeckHelpers
import HodgeLean.Foundations.Program.SchoenCycleC11EtaleSmoothHelpers

/-! # The actual generator on a base-neighbourhood restriction -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program

/-- A generator over the base restricts to the actual preimage of a base
open and retains its projection and power relation. -/
theorem s2e_c1_restrict_deck_to_neighbourhood
    (W B : Over (Spec ↧ℂ)) (β : W ⟶ B) (d : W ⟶ W)
    (hd : d ≫ β = β) (m : ℕ) (horder : End.of d ^ m = 1) (U : B.left.Opens) :
    ∃ dU : openScheme W (β.left ⁻¹ᵁ U) ⟶ openScheme W (β.left ⁻¹ᵁ U),
      dU ≫ openInclusion W (β.left ⁻¹ᵁ U) = openInclusion W (β.left ⁻¹ᵁ U) ≫ d ∧
      dU ≫ s2e_c11_restricted_over_morphism W B β U =
        s2e_c11_restricted_over_morphism W B β U ∧ End.of dU ^ m = 1 := by
  let V := β.left ⁻¹ᵁ U
  let jX := openInclusion W V
  let jY := openInclusion B U
  let fU := s2e_c11_restricted_over_morphism W B β U
  haveI : Mono jX := Over.mono_of_mono_left jX
  haveI : Mono jY := Over.mono_of_mono_left jY
  have hV : V ≤ d.left ⁻¹ᵁ V := by
    intro w hw
    change β.left (d.left w) ∈ U
    have he := congrArg (fun f : W ⟶ B => f.left w) hd
    change β.left (d.left w) = β.left w at he
    rw [he]
    exact hw
  let dU : openScheme W V ⟶ openScheme W V := Over.homMk (d.left.resLE V V hV) (by
    change d.left.resLE V V hV ≫ (V.ι ≫ W.hom) = V.ι ≫ W.hom
    rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, Over.w d])
  have hdu : dU ≫ jX = jX ≫ d := by
    apply Over.OverMorphism.ext
    exact Scheme.Hom.resLE_comp_ι d.left hV
  have hsquare : fU ≫ jY = jX ≫ β := s2e_c11_restricted_over_morphism_inclusion W B β U
  have hdf : dU ≫ fU = fU := by
    rw [← cancel_mono jY, Category.assoc, hsquare, ← Category.assoc, hdu,
      Category.assoc, hd]
  have ho : End.of dU ^ m = 1 := by
    have hc := s2e_c1_equivariant_generator_power jX dU d hdu m
    rw [horder] at hc
    apply End.ext
    apply (cancel_mono jX).mp
    exact (hc.trans (Category.comp_id jX)).trans (Category.id_comp jX).symm
  exact ⟨dU, hdu, hdf, ho⟩

end HodgeLean.Foundations.Program
