import HodgeLean.Papers.G34Compensation
import HodgeLean.Papers.G32TransferDefs
import HodgeLean.Adapters.GagaMapsProofs
import HodgeLean.Adapters.CycleClassPullbackSpan
import HodgeLean.Adapters.ChowCorrespondence

/-! # Compensation assembly data

Actual cross products and rational norm classes for G34 Proposition 10.2.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations.HermitianForm

namespace HodgeLean.Foundations.Program

/-- Integrality of the product over the algebraically closed base field.
Source: Stacks Project, Tag 05P3; gagam_product_isIntegral. -/
instance cq_product_integral (A Y : Over (Spec ↧ℂ)) [IsIntegral A.left]
    [IsIntegral Y.left] [LocallyOfFiniteType A.hom] [LocallyOfFiniteType Y.hom] :
    IsIntegral (A ⊗ Y).left := gagam_product_isIntegral A Y

example (A Y : Over (Spec ↧ℂ)) [IsIntegral A.left]
    [IsIntegral Y.left] [LocallyOfFiniteType A.hom] [LocallyOfFiniteType Y.hom] :
    IsIntegral (A ⊗ Y).left := inferInstance

/-- Smoothness of the product over the base field.
Source: EGA IV, 17.3.3; gagam_product_smooth. -/
instance cq_product_smooth (A Y : Over (Spec ↧ℂ)) [Smooth A.hom] [Smooth Y.hom] :
    Smooth (A ⊗ Y).hom := gagam_product_smooth A Y

/-- Projectivity of the product over the base field.
Source: EGA II, 5.5.5; gagam_product_projective. -/
instance cq_product_projective (A Y : Over (Spec ↧ℂ)) [IsProjective A.hom]
    [IsProjective Y.hom] : IsProjective (A ⊗ Y).hom := gagam_product_projective A Y

example (A Y : Over (Spec ↧ℂ)) [IsProjective A.hom] [IsProjective Y.hom] :
    IsProjective (A ⊗ Y).hom := inferInstance

example (A Y : Over (Spec ↧ℂ)) [Smooth A.hom] [Smooth Y.hom] :
    Smooth (A ⊗ Y).hom := inferInstance

/-- Cross product in a specified bidegree, using the constructed cup product.
Source: Hatcher, Algebraic Topology, §3.2 and Theorem 3.15. -/
def cq_cross (A Y : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (i j : ℕ) : HQ A i →ₗ[ℚ] HQ Y j →ₗ[ℚ] HQ (A ⊗ Y) (i + j) :=
  ((cupProductOf (A ⊗ Y)).cup rfl).compl₁₂
    (homPullback (fst A Y) i) (homPullback (snd A Y) j)

example (A Y : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (i j : ℕ) (b : HQ Y j) : cq_cross A Y i j 0 b = 0 := by
  rw [map_zero, LinearMap.zero_apply]

/-- Rational discriminant class modulo norms from the field of square root of minus three.
Source: van Geemen, An introduction to the Hodge conjecture for abelian varieties, §5. -/
def cq_ratClass (q : ℚ) (hq : q ≠ 0) :
    ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0) :=
  ((Units.mk0 q hq : ℚˣ) : ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0))

example : cq_ratClass (-2) (by norm_num) ≠ 1 := class_neg_two_ne_one

/-- The negative definite rational surface model on rational Weil coordinates.
Its complexification has isotropic conjugate lines; rational nonzero vectors are not isotropic.
Source: G34 v1.5, proof of Proposition 10.2; Hodge index theorem. -/
def cq_surfacePair (x y : Fin 2 → ℚ) : ℚ := -(x 0 * y 0 + 3 * x 1 * y 1)

example (x : Fin 2 → ℚ) (hx : x ≠ 0) : cq_surfacePair x x < 0 := by
  have hn : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
    by_contra h
    push Not at h
    apply hx
    ext i
    fin_cases i <;> simp only [Pi.zero_apply] <;> tauto
  rcases hn with h | h
  · have := sq_pos_of_ne_zero h
    have := sq_nonneg (x 1)
    dsimp [cq_surfacePair]
    nlinarith
  · have := sq_pos_of_ne_zero h
    have := sq_nonneg (x 0)
    dsimp [cq_surfacePair]
    nlinarith

example : Module.finrank ℚ (Fin 2 → ℚ) = 2 := by simp
example : cq_surfacePair ![1, 0] ![1, 0] = -1 := by norm_num [cq_surfacePair]
example : cq_surfacePair ![0, 1] ![0, 1] = -3 := by norm_num [cq_surfacePair]

/-- The surface endomorphism acting as one plus the CM rotation on the first factor.
Source: G34 v1.5, proof of Proposition 10.2, two independent classes. -/
def cq_surfaceEnd (E : Over (Spec ↧ℂ)) [GrpObj E] [IsCommMonObj E]
    (ρ : E ⟶ E) : E ⊗ E ⟶ E ⊗ E :=
  lift (fst E E * (fst E E ≫ ρ)) (snd E E)

example (E : Over (Spec ↧ℂ)) [GrpObj E] [IsCommMonObj E] (ρ : E ⟶ E) :
    cq_surfaceEnd E ρ ≫ snd E E = snd E E := by
  simp only [cq_surfaceEnd, lift_snd]

end HodgeLean.Foundations.Program
