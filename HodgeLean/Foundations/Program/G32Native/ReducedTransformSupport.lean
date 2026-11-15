import HodgeLean.Foundations.Program.SchoenTowerGeometryDefs

/-! Support calculations for the reduced transform, for arbitrary scheme maps. -/
noncomputable section
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The reduced transform is supported over the original subscheme. -/
theorem g32l4_reducedTransform_support_subset {X Y : Scheme} (f : X ⟶ Y)
    (D K : Y.IdealSheafData) :
    ((s2c_strictTransform f D K).support : Set X) ⊆ f ⁻¹' (D.support : Set Y) := by
  unfold s2c_strictTransform
  rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
  change closure (f ⁻¹' ((D.support : Set Y) \ (K.support : Set Y))) ⊆
    f ⁻¹' (D.support : Set Y)
  exact closure_minimal (fun _ hx => hx.1) (D.support.isClosed.preimage f.continuous)

/-- Away from the centre, taking the reduced transform preserves support membership. -/
theorem g32l4_reducedTransform_mem_off_centre {X Y : Scheme} (f : X ⟶ Y)
    (D K : Y.IdealSheafData) (x : X) (hx : f x ∉ K.support) :
    x ∈ (s2c_strictTransform f D K).support ↔ f x ∈ D.support := by
  constructor
  · exact fun h => g32l4_reducedTransform_support_subset f D K h
  · intro h
    change x ∈ ((Scheme.IdealSheafData.vanishingIdeal
      ⟨closure (f ⁻¹' ((D.support : Set Y) \ (K.support : Set Y))),
        isClosed_closure⟩).support : Set X)
    rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact subset_closure ⟨h, hx⟩

end HodgeLean.Foundations.Program
