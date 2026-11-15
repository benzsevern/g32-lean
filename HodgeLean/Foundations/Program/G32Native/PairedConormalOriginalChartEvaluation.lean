import HodgeLean.Foundations.Program.G32Native.PairedConormalAffineFractionEvaluation
import HodgeLean.Foundations.Program.G32Native.PairedConormalOriginalRatios
import HodgeLean.Foundations.Program.SchoenCycleProjectiveCharts

/-! # Exact original ratio evaluation on normalized polynomial charts -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
open AlgebraicGeometry.ComplexProjectiveSpace
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual original regular ratio evaluates to the normalized affine
polynomial coordinate, with no sign or scalar ambiguity. -/
theorem conormal_original_ratio_chart_evaluation (k : ℕ) (i j : Fin (k + 1))
    (h : (⊤ : (Spec (CommRingCat.of
        (MvPolynomial {j : Fin (k + 1) // j ≠ i} ℂ))).Opens) ≤
      s2e_s2b_chart i ⁻¹ᵁ projectiveSpaceBasicOpen k (X i)) :
    (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial {j : Fin (k + 1) // j ≠ i} ℂ))).hom
      ((s2e_s2b_chart i).appLE (projectiveSpaceBasicOpen k (X i)) ⊤ h
        (conormalOriginalCoordinateRatio k i j)) =
      if hji : j = i then 1 else X ⟨j, hji⟩ := by
  let p := pullback.snd (terminal.from (Spec ↧ℂ)) (terminal.from (Proj (UniversalGrading k)))
  let t := Spec.map (CommRingCat.ofHom (s2e_s2b_chartHom i)) ≫
    Proj.awayι (UniversalGrading k) (X i) (isHomogeneous_X (ULift ℤ) i) zero_lt_one
  have hp : s2e_s2b_chart i ≫ p = t := by
    simp only [s2e_s2b_chart, p, pullback.lift_snd, t]
  have hs : (⊤ : (Spec (CommRingCat.of
      (MvPolynomial {j : Fin (k + 1) // j ≠ i} ℂ))).Opens) ≤
      t ⁻¹ᵁ Proj.basicOpen (UniversalGrading k) (X i) := by
    rw [← hp, Scheme.Hom.comp_preimage]
    exact h
  have hc := Scheme.Hom.appLE_comp_appLE (s2e_s2b_chart i) p
    (Proj.basicOpen (UniversalGrading k) (X i)) (projectiveSpaceBasicOpen k (X i)) ⊤ le_rfl h
  have he : p.appLE (Proj.basicOpen (UniversalGrading k) (X i))
      (projectiveSpaceBasicOpen k (X i)) le_rfl ≫
      (s2e_s2b_chart i).appLE (projectiveSpaceBasicOpen k (X i)) ⊤ h =
      t.appLE (Proj.basicOpen (UniversalGrading k) (X i)) ⊤ hs := by
    apply hc.trans
    congr 1
  have hh := (congrArg (fun u => Proj.awayToSection (UniversalGrading k) (X i) ≫ u ≫
    (Scheme.ΓSpecIso (CommRingCat.of
      (MvPolynomial {j : Fin (k + 1) // j ≠ i} ℂ))).hom) he).trans
        (conormal_affine_fraction_evaluation k i (s2e_s2b_chartHom i) hs)
  have hv := ConcreteCategory.congr_hom hh (chartCoordinate i j)
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
    CommRingCat.hom_ofHom, conormalOriginalCoordinateRatio, s2e_chartHom_coordinate, p] at hv
  convert! hv using 1 <;> rfl

end HodgeLean.Foundations.Program.G32Native
