import HodgeLean.Foundations.Program.G32Native.PairedC3ChartClosure
import HodgeLean.Foundations.Program.SchoenTowerL1bStrictTransformChart
import HodgeLean.Foundations.Program.SchoenCycleC1AffineComapSections

/-! # The ideal identity on the two complementary chart regions -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- Away from the centre a radical total-transform ideal is already the
reduced strict-transform ideal.
Source: Hartshorne, Algebraic Geometry, II.7.13. -/
theorem paired_c3_strict_off_centre_sections
    {X Y : Scheme} (σ : X ⟶ Y) (D K : Y.IdealSheafData) (V : X.affineOpens)
    (hK : (K.comap σ).ideal V = ⊤) (hD : ((D.comap σ).ideal V).IsRadical) :
    (s2c_strictTransform σ D K).ideal V = (D.comap σ).ideal V := by
  rw [s2v_l1b_strictTransform_affine_formula, hK]
  simp only [Submodule.top_coe, PrimeSpectrum.zeroLocus_univ, Set.sdiff_empty,
    (PrimeSpectrum.isClosed_zeroLocus _).closure_eq,
    PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical, hD.radical]

#print axioms paired_c3_strict_off_centre_sections
/-- A chart missing the total slice has empty strict component, so the
intersection identity holds there with arbitrary centre ideal.
Source: Hartshorne, Algebraic Geometry, II.7.13. -/
theorem paired_c3_union_off_slice_sections
    {X Y : Scheme} (σ : X ⟶ Y) (D K : Y.IdealSheafData) (V : X.affineOpens)
    (hD : (D.comap σ).ideal V = ⊤) :
    (D.comap σ).ideal V = (s2c_strictTransform σ D K).ideal V ⊓
      ((K.comap σ).ideal V ⊔ (D.comap σ).ideal V) := by
  have hQ : (s2c_strictTransform σ D K).ideal V = ⊤ := by
    rw [s2v_l1b_strictTransform_affine_formula, hD]
    simp only [Submodule.top_coe, PrimeSpectrum.zeroLocus_univ, Set.empty_sdiff,
      closure_empty, PrimeSpectrum.vanishingIdeal_empty]
  rw [hD, hQ, sup_top_eq, inf_top_eq]

#print axioms paired_c3_union_off_slice_sections
end HodgeLean.Foundations.Program.G32Native
