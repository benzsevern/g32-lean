import HodgeLean.Foundations.Program.SchoenTowerGeometryDefs

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

theorem s2e_strictTransform_contains_pullback {X Y : Scheme} (f : X ⟶ Y)
    (D K : Y.IdealSheafData) : D.comap f ≤ s2c_strictTransform f D K := by
  apply Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp
  change closure (f ⁻¹' ((D.support : Set Y) \ (K.support : Set Y))) ⊆ _
  rw [Scheme.IdealSheafData.support_comap]
  apply closure_minimal
  · exact fun _ hx => hx.1
  · exact D.support.isClosed.preimage f.continuous

theorem s2e_strictTransform_restriction_of_density {L X Y : Scheme}
    (f : X ⟶ Y) (ℓ : L ⟶ X) (D K : Y.IdealSheafData)
    (hred : ((D.comap f).comap ℓ).radical = (D.comap f).comap ℓ)
    (hdense : ((D.comap f).comap ℓ).support.carrier ⊆
      closure ((ℓ ≫ f) ⁻¹' ((D.support : Set Y) \ (K.support : Set Y)))) :
    (s2c_strictTransform f D K).comap ℓ = (D.comap f).comap ℓ := by
  have hle : (D.comap f).comap ℓ ≤ (s2c_strictTransform f D K).comap ℓ :=
    Scheme.IdealSheafData.comap_mono ℓ (s2e_strictTransform_contains_pullback f D K)
  apply le_antisymm _ hle
  rw [← hred, ← Scheme.IdealSheafData.vanishingIdeal_support]
  apply Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp
  intro x hx
  have hx' := hdense hx
  rw [Scheme.IdealSheafData.support_comap]
  change ℓ x ∈ ((s2c_strictTransform f D K).support : Set X)
  rw [s2c_strictTransform, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  exact ℓ.continuous.closure_preimage_subset
    (f ⁻¹' ((D.support : Set Y) \ (K.support : Set Y))) hx'

end HodgeLean.Foundations.Program
