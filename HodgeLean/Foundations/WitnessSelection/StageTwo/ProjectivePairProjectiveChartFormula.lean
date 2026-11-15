import HodgeLean.Foundations.WitnessSelection.StageTwo.ProjectivePairKernelImageFormula
import HodgeLean.Foundations.WitnessSelection.StageTwo.ProjectivePairAffineClosedFormula
import HodgeLean.Foundations.WitnessSelection.StageTwo.ProjectivePairProjectiveChartEvaluation
import HodgeLean.Foundations.WitnessSelection.StageTwo.ProjectivePairProjectiveRealMatrix

/-! Boolean images of algebraic loci in standard projective charts.

HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open scoped LinearAlgebra.Projectivization
open HodgeLean.Foundations.Program
namespace HodgeLean.WitnessSelection.StageTwo

/-- Each standard chart of a projective Zariski locus has a Boolean matrix image.
Source: Bochnak, Coste and Roy, Real Algebraic Geometry (1998), §§2.1–2.2;
Hartshorne, Algebraic Geometry, II.2 and II.7.
HC no distance; AV milestone no distance. -/
theorem s2e_pair_projective_chart_formula {n : ℕ}
    (C : Set (ProjectiveSpace (Fin (n + 1)) (Spec ↧ℂ))) (hC : IsClosed C)
    (i : Fin (n + 1)) :
    ∃ f : s2v_t11b_Formula (Fintype.card
      ((Fin (n + 1) × Fin (n + 1)) ⊕ (Fin (n + 1) × Fin (n + 1)))),
      ∀ z, z ∈ f.realize ↔ ∃ (v : Fin (n + 1) → ℂ) (hv : v ≠ 0),
        v i = 1 ∧ (ComplexProjectiveSpace.vectorToComplexPoint v hv).underlying ∈ C ∧
        z = s2e_pair_projectiveRealMatrix n (Projectivization.mk ℂ v hv) := by
  classical
  let d := n + 1
  let r : Fin d → MvPolynomial (Fin (d + d)) ℝ := fun j =>
    if j = i then 1 else MvPolynomial.X (Fin.castAdd d j)
  let s : Fin d → MvPolynomial (Fin (d + d)) ℝ := fun j =>
    if j = i then 0 else MvPolynomial.X (Fin.natAdd d j)
  let v := fun x : EuclideanSpace ℝ (Fin (d + d)) => fun j =>
    (MvPolynomial.eval (fun a => x a) (r j) : ℂ) +
      (MvPolynomial.eval (fun a => x a) (s j) : ℂ) * Complex.I
  have vi (x) : v x i = 1 := by simp [v, r, s]
  have vn (x) : v x ≠ 0 := by
    intro hz
    have := congrFun hz i
    rw [vi] at this
    exact one_ne_zero this
  let g := (AffineSpace.SpecIso (Fin d) ↧ℂ).inv ≫
    ComplexProjectiveSpace.chartAffineToProjectiveSpace i
  obtain ⟨b, hb⟩ := s2e_pair_affine_closed_formula (g ⁻¹' C)
    (hC.preimage g.continuous) r s
  obtain ⟨f, hf⟩ := s2e_pair_kernel_image_formula r s b
  refine ⟨f, ?_⟩
  intro z
  rw [hf]
  have hc (x) : x ∈ b.realize ↔
      (ComplexProjectiveSpace.vectorToComplexPoint (v x) (vn x)).underlying ∈ C := by
    rw [hb]
    have he := s2e_pair_projective_chart_evaluation (v x) (vn x) i (vi x)
    rw [show (⟨⊥, inferInstance⟩ : PrimeSpectrum ℂ) =
      IsLocalRing.closedPoint ℂ from Subsingleton.elim _ _]
    change (Spec.map (CommRingCat.ofHom (MvPolynomial.eval (v x))) ≫ g)
      (IsLocalRing.closedPoint (CommRingCat.of ℂ)) ∈ C ↔ _
    rw [show Spec.map (CommRingCat.ofHom (MvPolynomial.eval (v x))) ≫ g =
      (ComplexProjectiveSpace.vectorToComplexPoint (v x) (vn x)).left from he]
    rfl

  constructor
  · rintro ⟨x, hx, _, hz⟩
    exact ⟨v x, vn x, vi x, (hc x).mp hx, hz⟩
  · rintro ⟨w, hw, hi, hmem, hz⟩
    let x : EuclideanSpace ℝ (Fin (d + d)) :=
      WithLp.toLp 2 (Fin.append (fun j => (w j).re) (fun j => (w j).im))
    have hx : v x = w := by
      funext j
      by_cases hj : j = i
      · subst j
        rw [vi, hi]
      · simp only [v, r, s, if_neg hj, MvPolynomial.eval_X, x,
          Fin.append_left, Fin.append_right]
        exact Complex.re_add_im (w j)
    refine ⟨x, (hc x).mpr ?_, vn x, ?_⟩
    · simpa only [hx] using hmem
    · change z = s2e_pair_projectiveRealMatrix n (Projectivization.mk ℂ (v x) (vn x))
      simpa only [hx] using hz

end HodgeLean.WitnessSelection.StageTwo
