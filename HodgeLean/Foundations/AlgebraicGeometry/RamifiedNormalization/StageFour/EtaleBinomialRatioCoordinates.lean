import HodgeLean.Foundations.Program.SchoenTowerL1bEtaleSectionBlowup
import HodgeLean.Foundations.AlgebraicGeometry.RegularPairChart
import HodgeLean.Foundations.AlgebraicGeometry.RegularPairChartTensor

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- The new etale coordinate on a regular-pair blowup chart is its literal ratio, with the denominator and all other coordinates retained. -/
theorem etale_binomial_ratio_coordinates
    {k R ι : Type} [CommRing k] [CommRing R] [DecidableEq ι]
    (c : k →+* R) (z : ι → R) (het : (MvPolynomial.eval₂Hom c z).Etale)
    (a b : ι) (hab : a ≠ b)
    (hv : IsRegular (z b)) (hu : IsRegular (Ideal.Quotient.mk (Ideal.span {z b}) (z a))) :
    ∃ w : ι → RegularPairChart.ring (z a) (z b),
      (MvPolynomial.eval₂Hom ((RegularPairChart.coeff (z a) (z b)).comp c) w).Etale ∧
      w a = RegularPairChart.ratio (z a) (z b) ∧
      w b = RegularPairChart.coeff (z a) (z b) (z b) ∧
      ∀ j, j ≠ a → w j = RegularPairChart.coeff (z a) (z b) (z j) := by
  obtain ⟨w, hw, hwe⟩ := HodgeLean.Foundations.Program.s2v_l1b_etale_section_binomial_chart c z het a b hab
  have hcoeff (j : ι) : RegularPairChart.coeff (z a) (z b) (z j) =
      if j = a then w a * w b else w j := hwe j
  have hwb : w b = RegularPairChart.coeff (z a) (z b) (z b) := by
    have hb := hcoeff b
    rw [if_neg hab.symm] at hb
    exact hb.symm
  have hwa : w a = RegularPairChart.ratio (z a) (z b) := by
    have hreg := RegularPairChart.denominator_regular (z a) (z b) hv hu
    apply hreg.right
    calc
      w a * RegularPairChart.coeff (z a) (z b) (z b) = w a * w b := by rw [hwb]
      _ = RegularPairChart.coeff (z a) (z b) (z a) := by
        have ha := hcoeff a
        rw [if_pos rfl] at ha
        exact ha.symm
      _ = RegularPairChart.ratio (z a) (z b) * RegularPairChart.coeff (z a) (z b) (z b) :=
        RegularPairChart.chart_relation (z a) (z b)
  refine ⟨w, hw, hwa, hwb, ?_⟩
  intro j hja
  have hj := hcoeff j
  rw [if_neg hja] at hj
  exact hj.symm

end AlgebraicGeometry.RamifiedNormalization.StageFour
