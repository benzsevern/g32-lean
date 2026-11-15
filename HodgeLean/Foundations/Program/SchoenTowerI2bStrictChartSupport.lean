import HodgeLean.Foundations.Program.SchoenCycleSliceHelpers

/-! Transport of divisor density through charts of the retained blowup.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Density of the nonexceptional branch in a chart puts every branch point in the strict transform.
Source: continuity of the chart map and the support definition of reduced strict transform. -/
theorem s2v_i2b_dense_chart_strictTransform_support
    {Q X Y : Scheme} (b : Y ⟶ X) (g : Q ⟶ Y) (D K : X.IdealSheafData)
    (hdense : closure ((g ≫ b) ⁻¹' ((D.support : Set X) \ (K.support : Set X))) =
      (g ≫ b) ⁻¹' (D.support : Set X))
    (q : Q) (hq : (g ≫ b) q ∈ D.support) :
    g q ∈ (s2c_strictTransform b D K).support := by
  change g q ∈ ((s2c_strictTransform b D K).support : Set Y)
  rw [s2e_strictTransform_support_eq_removed_pullback,
    Scheme.IdealSheafData.support_comap, Scheme.IdealSheafData.support_comap]
  have hq' : q ∈ closure ((g ≫ b) ⁻¹' ((D.support : Set X) \ (K.support : Set X))) := by
    rwa [hdense]
  have h := image_closure_subset_closure_image g.continuous ⟨q, hq', rfl⟩
  apply closure_mono (s := g '' ((g ≫ b) ⁻¹'
    ((D.support : Set X) \ (K.support : Set X)))) ?_ h
  rintro _ ⟨z, hz, rfl⟩
  exact hz

end HodgeLean.Foundations.Program
