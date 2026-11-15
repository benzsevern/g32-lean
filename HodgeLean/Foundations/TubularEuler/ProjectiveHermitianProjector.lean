import HodgeLean.Foundations.TubularEuler.HermitianProjectorAffine
import HodgeLean.Foundations.Program.SchoenCycleProjectivePoints

/-! # The Hermitian projector on scheme projective points

The homogeneous matrix descends through the actual projective coordinate homeomorphism.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.TubularEuler

/-- The Hermitian projector on a homogeneous coordinate line.
Source: Griffiths–Harris, Principles of Algebraic Geometry, chapter 1, section 2.
HC no distance; AV milestone no distance. -/
def lineHermitianProjector {n : ℕ} (x : Projectivization ℂ (Fin (n+1) → ℂ)) :
    Fin (n+1) → Fin (n+1) → ℂ := hermitianProjector x.rep

/-- Evaluation is independent of the selected nonzero representative.
Source: Griffiths–Harris, Principles of Algebraic Geometry, chapter 1, section 2.
HC no distance; AV milestone no distance. -/
theorem lineHermitianProjector_mk {n : ℕ} (z : Fin (n+1) → ℂ) (hz : z ≠ 0) :
    lineHermitianProjector (Projectivization.mk ℂ z hz) = hermitianProjector z := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ z hz
  dsimp [lineHermitianProjector]
  rw [← ha]
  exact hermitianProjector_smul z (a : ℂ) a.ne_zero

example : lineHermitianProjector (Projectivization.mk ℂ (![1, Complex.I] : Fin 2 → ℂ)
    (by intro h; have := congrFun h 0; norm_num at this)) 0 1 = -Complex.I / 2 := by
  rw [lineHermitianProjector_mk]
  norm_num [hermitianProjector, projectorLength, Fin.sum_univ_succ, Complex.star_def]

/-- The projector on actual complex points of scheme projective space.
Source: Griffiths–Harris, Principles of Algebraic Geometry, chapter 1, section 2.
HC no distance; AV milestone no distance. -/
def projectiveHermitianProjector (n : ℕ)
    (x : ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (n+1)) (Spec ↧ℂ)))) :
    Fin (n+1) → Fin (n+1) → ℂ :=
  lineHermitianProjector ((s2e_projectivePointHomeomorph n).symm x)

/-- The scheme-point projector evaluates by the homogeneous formula.
Source: Griffiths–Harris, Principles of Algebraic Geometry, chapter 1, section 2.
HC no distance; AV milestone no distance. -/
theorem projectiveHermitianProjector_coordinates {n : ℕ} (z : Fin (n+1) → ℂ)
    (hz : z ≠ 0) :
    projectiveHermitianProjector n (ComplexProjectiveSpace.projectivizationToComplexPoint
      (Projectivization.mk ℂ z hz)) = hermitianProjector z := by
  change lineHermitianProjector ((s2e_projectivePointHomeomorph n).symm
    ((s2e_projectivePointHomeomorph n) (Projectivization.mk ℂ z hz))) = _
  rw [Homeomorph.symm_apply_apply, lineHermitianProjector_mk]

example : projectiveHermitianProjector 1
    (ComplexProjectiveSpace.projectivizationToComplexPoint
      (Projectivization.mk ℂ (![1, Complex.I] : Fin 2 → ℂ)
        (by intro h; have := congrFun h 0; norm_num at this))) 0 1 = -Complex.I / 2 := by
  rw [projectiveHermitianProjector_coordinates]
  norm_num [hermitianProjector, projectorLength, Fin.sum_univ_succ, Complex.star_def]

/-- Restriction of the actual projective Hermitian projector.
Source: Griffiths–Harris, Principles of Algebraic Geometry, chapter 1, section 2.
HC no distance; AV milestone no distance. -/
def quasiProjectiveProjector {X : Over (Spec ↧ℂ)} {N : ℕ}
    (e : X ⟶ Over.mk (ProjectiveSpace.toBase (Fin (N+1)) (Spec ↧ℂ))) :
    ComplexPoint X → (Fin (N+1) → Fin (N+1) → ℂ) :=
  projectiveHermitianProjector N ∘ Point.map e

example (x : ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin 2) (Spec ↧ℂ)))) :
    quasiProjectiveProjector (𝟙 _) x = projectiveHermitianProjector 1 x := by
  simp [quasiProjectiveProjector, Point.map]

#print axioms lineHermitianProjector_mk
#print axioms projectiveHermitianProjector_coordinates
end HodgeLean.Foundations.TubularEuler
