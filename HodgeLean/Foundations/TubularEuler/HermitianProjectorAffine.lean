import HodgeLean.Foundations.TubularEuler.HermitianProjectorCoordinates
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! # Affine coordinates and derivatives of the Hermitian projector

The nonzero leading coordinate gives a rational left inverse on the matrix image.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 200000
open scoped ContDiff
namespace HodgeLean.Foundations.TubularEuler

/-- The projector in the standard leading-coordinate affine chart.
Source: Griffiths–Harris, Principles of Algebraic Geometry, chapter 1, section 2.
HC no distance; AV milestone no distance. -/
def affineHermitianProjector {n : ℕ} (z : Fin n → ℂ) : Fin (n+1) → Fin (n+1) → ℂ :=
  hermitianProjector (Fin.cons 1 z)

example : affineHermitianProjector (fun _ : Fin 1 => Complex.I) 0 1 = -Complex.I / 2 := by
  norm_num [affineHermitianProjector, hermitianProjector, projectorLength,
    Fin.sum_univ_succ, Complex.star_def]

/-- Recover affine coordinates from the first column of a projector matrix.
Source: Griffiths–Harris, Principles of Algebraic Geometry, chapter 1, section 2.
HC no distance; AV milestone no distance. -/
def projectorAffineRecovery {n : ℕ} (P : Fin (n+1) → Fin (n+1) → ℂ) : Fin n → ℂ :=
  fun i => P i.succ 0 / P 0 0

example : projectorAffineRecovery (affineHermitianProjector (fun _ : Fin 1 => Complex.I)) 0 =
    Complex.I := by
  simpa [projectorAffineRecovery, affineHermitianProjector] using
    hermitianProjector_ratio (Fin.cons (1 : ℂ) (fun _ : Fin 1 => Complex.I)) 0
      (by simp) (Fin.succ 0)

/-- The recovery is a left inverse in every affine dimension.
Source: Griffiths–Harris, Principles of Algebraic Geometry, chapter 1, section 2.
HC no distance; AV milestone no distance. -/
theorem projectorAffineRecovery_leftInverse (n : ℕ) :
    Function.LeftInverse (projectorAffineRecovery (n := n)) affineHermitianProjector := by
  intro z
  funext i
  simpa [projectorAffineRecovery, affineHermitianProjector] using
    hermitianProjector_ratio (Fin.cons (1 : ℂ) z) 0 (by simp) i.succ

example : Function.Injective (affineHermitianProjector (n := 1)) :=
  (projectorAffineRecovery_leftInverse 1).injective

private theorem projectorLength_contDiff {n : ℕ} : ContDiff ℝ ω (projectorLength (n := n)) := by
  unfold projectorLength
  apply ContDiff.sum
  intro i _
  simp only [Complex.normSq_apply]
  exact ((Complex.reCLM.contDiff.comp (contDiff_apply ℝ ℂ i)).mul
    (Complex.reCLM.contDiff.comp (contDiff_apply ℝ ℂ i))).add
    ((Complex.imCLM.contDiff.comp (contDiff_apply ℝ ℂ i)).mul
      (Complex.imCLM.contDiff.comp (contDiff_apply ℝ ℂ i)))

private theorem hermitianProjector_contDiffAt {n : ℕ} (z : Fin n → ℂ) (hz : z ≠ 0) :
    ContDiffAt ℝ ω (fun w : Fin n → ℂ => fun i j => hermitianProjector w i j) z := by
  have hlen : (projectorLength z : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (projectorLength_pos hz))
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  simp only [hermitianProjector, div_eq_mul_inv]
  exact ((contDiff_apply ℝ ℂ i).contDiffAt.mul
    (Complex.conjCLE.contDiff.contDiffAt.comp z (contDiff_apply ℝ ℂ j).contDiffAt)).mul
    ((Complex.ofRealCLM.contDiff.contDiffAt.comp z
      projectorLength_contDiff.contDiffAt).inv hlen)

/-- Real analytic regularity of the normalized affine projector.
Source: Griffiths–Harris, Principles of Algebraic Geometry, chapter 1, section 2.
HC no distance; AV milestone no distance. -/
theorem affineHermitianProjector_contDiff (n : ℕ) :
    ContDiff ℝ ω (affineHermitianProjector (n := n)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  apply (hermitianProjector_contDiffAt (Fin.cons 1 z) ?_).comp z
  · apply contDiffAt_pi.mpr
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact contDiffAt_const
    · exact (contDiff_apply ℝ ℂ j).contDiffAt
  · intro h
    have := congrFun h 0
    simp at this

example : Differentiable ℝ (affineHermitianProjector (n := 1)) :=
  (affineHermitianProjector_contDiff 1).differentiable (by simp)

/-- Every affine projector differential is injective over the real numbers.
Source: Griffiths–Harris, Principles of Algebraic Geometry, chapter 1, section 2.
HC no distance; AV milestone no distance. -/
theorem affineHermitianProjector_fderiv_injective (n : ℕ) (z : Fin n → ℂ) :
    Function.Injective (fderiv ℝ affineHermitianProjector z) := by
  have hn : affineHermitianProjector z 0 0 ≠ 0 := by
    have hlen : (projectorLength (Fin.cons (1 : ℂ) z) : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (projectorLength_pos (by
        intro h; have := congrFun h 0; simp at this)))
    simpa [affineHermitianProjector, hermitianProjector] using inv_ne_zero hlen
  have hd (i j : Fin (n+1)) : DifferentiableAt ℝ
      (fun P : Fin (n+1) → Fin (n+1) → ℂ => P i j) (affineHermitianProjector z) :=
    (contDiff_apply_apply ℝ ℂ i j : ContDiff ℝ 1 _).differentiable_one _
  have hr : DifferentiableAt ℝ projectorAffineRecovery (affineHermitianProjector z) := by
    apply differentiableAt_pi.mpr
    intro i
    simp only [projectorAffineRecovery, div_eq_mul_inv]
    exact DifferentiableAt.mul (hd i.succ 0) (DifferentiableAt.inv (hd 0 0) hn)
  have hp := (affineHermitianProjector_contDiff n).differentiable (by simp)
  have he : fderiv ℝ (projectorAffineRecovery ∘ affineHermitianProjector) z =
      ContinuousLinearMap.id ℝ (Fin n → ℂ) := by
    have hfun : projectorAffineRecovery ∘ affineHermitianProjector =
        (id : (Fin n → ℂ) → Fin n → ℂ) :=
      funext (projectorAffineRecovery_leftInverse n)
    rw [hfun, fderiv_id]
  rw [fderiv_comp z hr (hp z)] at he
  intro u v huv
  have h := congrArg (fderiv ℝ projectorAffineRecovery (affineHermitianProjector z)) huv
  simpa only [← ContinuousLinearMap.comp_apply, he, ContinuousLinearMap.id_apply] using h

example : Function.Injective
    (fderiv ℝ affineHermitianProjector (fun _ : Fin 1 => Complex.I)) :=
  affineHermitianProjector_fderiv_injective 1 _

#print axioms projectorAffineRecovery_leftInverse
#print axioms affineHermitianProjector_fderiv_injective
#print axioms affineHermitianProjector_contDiff
end HodgeLean.Foundations.TubularEuler
