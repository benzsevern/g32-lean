import HodgeLean.Foundations.Program.SchoenCycleC1FibreCardTransportHelpers
import HodgeLean.Foundations.Program.SchoenTowerComplexPointsExist

/-! # A measured fibre transported through the actual open cover comparison -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program

/-- A compatible isomorphism of nonempty open covers transports the measured
initial fibre size to a point in the prescribed final neighbourhood. -/
theorem s2e_c1_good_fibre_of_open_cover_iso
    (m : ℕ) (X Y X₀ Y₀ : Over (Spec ↧ℂ)) [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (g : X₀ ⟶ Y₀)
    (U U₁ : Y.left.Opens) [Nonempty U₁] (V₀ V₁ : Y₀.left.Opens)
    (hU : U₁ ≤ U) (hV : V₁ ≤ V₀)
    (eY : openScheme Y U₁ ≅ openScheme Y₀ V₁)
    (eX : openScheme X (f.left ⁻¹ᵁ U₁) ≅ openScheme X₀ (g.left ⁻¹ᵁ V₁))
    (he : eX.hom ≫ s2e_c11_restricted_over_morphism X₀ Y₀ g V₁ =
      s2e_c11_restricted_over_morphism X Y f U₁ ≫ eY.hom)
    (hcard : ∀ y : ComplexPoint Y₀, y.underlying ∈ V₀ → Nat.card ((Point.map g) ⁻¹' {y}) = m) :
    ∃ y : ComplexPoint Y, y.underlying ∈ U ∧ Nat.card ((Point.map f) ⁻¹' {y}) = m := by
  haveI : LocallyOfFiniteType (openScheme Y U₁).hom := by
    change LocallyOfFiniteType (U₁.ι ≫ Y.hom)
    infer_instance
  haveI : Nonempty (openScheme Y U₁).left := inferInstanceAs (Nonempty U₁.toScheme)
  obtain ⟨x⟩ := s2t_nonempty_complexPoints (openScheme Y U₁)
  let y := Point.map (openInclusion Y U₁) x
  let x₀ := Point.map eY.hom x
  let y₀ := Point.map (openInclusion Y₀ V₁) x₀
  have hy : y.underlying ∈ U := hU (openHomeomorph Y U₁ x).property
  have hy₀ : y₀.underlying ∈ V₀ := hV (openHomeomorph Y₀ V₁ x₀).property
  refine ⟨y, hy, ?_⟩
  calc
    Nat.card ((Point.map f) ⁻¹' {y}) =
        Nat.card ((Point.map (s2e_c11_restricted_over_morphism X Y f U₁)) ⁻¹' {x}) :=
      (s2e_c1_restricted_complex_fibre_card X Y f U₁ x).symm
    _ = Nat.card ((Point.map (s2e_c11_restricted_over_morphism X₀ Y₀ g V₁)) ⁻¹' {x₀}) :=
      s2e_c1_fibre_card_of_iso_square _ _ eX eY he x
    _ = Nat.card ((Point.map g) ⁻¹' {y₀}) := s2e_c1_restricted_complex_fibre_card X₀ Y₀ g V₁ x₀
    _ = m := hcard y₀ hy₀

end HodgeLean.Foundations.Program
