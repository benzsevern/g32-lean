import HodgeLean.Adapters.LefschetzOneOneHodgeAbelian3Proofs

/-! # Riemann forms as Appell–Humbert Chern classes

This stage packages the already established Riemann-form/Hermitian-form correspondence and
semicharacter existence with the repository's Chern-form convention.  No positivity assumption
is used: positivity belongs to the algebraic half through ample Appell–Humbert line bundles.
HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.AppellHumbert
open HodgeLean.Foundations.AutomorphyChernClass

namespace HodgeLean.Adapters

variable (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
  [IsProjective X.hom]

/-- Every integral Riemann form gives Appell–Humbert data whose Chern-form lattice class is the
negative of the original lattice class.  The logarithm is the canonical `holLog`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Lemma 1.3.1 and Theorem 2.2.3;
`spec_exists_datumOfX_of_riemann`; `spec_chernClassHQ_datumOfX`. -/
theorem spec_exists_chernClassHQ_of_riemann
    (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (B : (Fin (dim X.left) → ℂ) →ₗ[ℝ]
      (Fin (dim X.left) → ℂ) →ₗ[ℝ] ℝ)
    (hB : ∀ l m : abelianPeriodLattice X, B l m = E l m)
    (hEalt : ∀ l : abelianPeriodLattice X, E l l = 0)
    (h11 : IsTypeOneOne (fun v w ↦ B v w)) :
    ∃ (H : HermitianForm (V := Fin (dim X.left) → ℂ))
      (hE : ∀ l m : abelianPeriodLattice X, (E l m : ℝ) = H.imaginary l m)
      (hHB : ∀ v w, H.imaginary v w = B v w)
      (hH : ∀ v w, H.toFun v w = (B v (Complex.I • w) : ℂ) + (B v w : ℂ) * Complex.I)
      (χ : abelianPeriodLattice X → Circle)
      (hχ : ∀ l m : abelianPeriodLattice X,
        χ (l + m) = χ l * χ m * Circle.exp (Real.pi * H.imaginary l m))
      (E' : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ),
      (∀ l m, E' l m = chernForm (holLog (datumOfX X H E hE χ hχ)) l m) ∧
        latticeClassHQ X E' = -latticeClassHQ X E :=
  bh3_exists_chernClassHQ_of_riemann X E B hB hEalt h11

/-- Scoped Lefschetz `(1,1)` is equivalent to algebraicity of the Chern-form lattice classes of
Appell–Humbert data obtained from every integral Riemann form.  This is the stage-two reduction
transported across the explicit negative Chern sign.
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 1 §2;
Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Theorem 2.2.3;
`spec_lefschetzOneOneFor_iff_riemann_latticeClassHQ`; `spec_chernClassHQ_datumOfX`. -/
theorem spec_lefschetzOneOneFor_iff_appellHumbert_chernClassHQ
    (hF : FiniteBetti X) (hBdR : BettiDeRhamIso X) :
    LefschetzOneOneFor X ↔
      ∀ (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
        (B : (Fin (dim X.left) → ℂ) →ₗ[ℝ]
          (Fin (dim X.left) → ℂ) →ₗ[ℝ] ℝ),
        (∀ l m : abelianPeriodLattice X, B l m = E l m) →
        (∀ l : abelianPeriodLattice X, E l l = 0) →
        IsTypeOneOne (fun v w ↦ B v w) →
        ∃ (H : HermitianForm (V := Fin (dim X.left) → ℂ))
          (hE : ∀ l m : abelianPeriodLattice X, (E l m : ℝ) = H.imaginary l m)
          (χ : abelianPeriodLattice X → Circle)
          (hχ : ∀ l m : abelianPeriodLattice X,
            χ (l + m) = χ l * χ m * Circle.exp (Real.pi * H.imaginary l m))
          (E' : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ),
          (∀ l m, E' l m = chernForm (holLog (datumOfX X H E hE χ hχ)) l m) ∧
            latticeClassHQ X E' = -latticeClassHQ X E ∧
            latticeClassHQ X E' ∈ algebraicCycleClassSpan X 1 :=
  bh3_lefschetzOneOneFor_iff_appellHumbert_chernClassHQ X hF hBdR

/-! ## Interface examples -/

example
    (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (B : (Fin (dim X.left) → ℂ) →ₗ[ℝ]
      (Fin (dim X.left) → ℂ) →ₗ[ℝ] ℝ)
    (hB : ∀ l m : abelianPeriodLattice X, B l m = E l m)
    (hEalt : ∀ l : abelianPeriodLattice X, E l l = 0)
    (h11 : IsTypeOneOne (fun v w ↦ B v w)) :
    ∃ (H : HermitianForm (V := Fin (dim X.left) → ℂ))
      (hE : ∀ l m : abelianPeriodLattice X, (E l m : ℝ) = H.imaginary l m)
      (hHB : ∀ v w, H.imaginary v w = B v w)
      (hH : ∀ v w, H.toFun v w = (B v (Complex.I • w) : ℂ) + (B v w : ℂ) * Complex.I)
      (χ : abelianPeriodLattice X → Circle)
      (hχ : ∀ l m : abelianPeriodLattice X,
        χ (l + m) = χ l * χ m * Circle.exp (Real.pi * H.imaginary l m))
      (E' : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ),
      (∀ l m, E' l m = chernForm (holLog (datumOfX X H E hE χ hχ)) l m) ∧
        latticeClassHQ X E' = -latticeClassHQ X E :=
  spec_exists_chernClassHQ_of_riemann X E B hB hEalt h11

example (hF : FiniteBetti X) (hBdR : BettiDeRhamIso X) (hL : LefschetzOneOneFor X)
    (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (B : (Fin (dim X.left) → ℂ) →ₗ[ℝ]
      (Fin (dim X.left) → ℂ) →ₗ[ℝ] ℝ)
    (hB : ∀ l m : abelianPeriodLattice X, B l m = E l m)
    (hEalt : ∀ l : abelianPeriodLattice X, E l l = 0)
    (h11 : IsTypeOneOne (fun v w ↦ B v w)) :
    ∃ (H : HermitianForm (V := Fin (dim X.left) → ℂ))
      (hE : ∀ l m : abelianPeriodLattice X, (E l m : ℝ) = H.imaginary l m)
      (χ : abelianPeriodLattice X → Circle)
      (hχ : ∀ l m : abelianPeriodLattice X,
        χ (l + m) = χ l * χ m * Circle.exp (Real.pi * H.imaginary l m))
      (E' : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ),
      (∀ l m, E' l m = chernForm (holLog (datumOfX X H E hE χ hχ)) l m) ∧
        latticeClassHQ X E' = -latticeClassHQ X E ∧
        latticeClassHQ X E' ∈ algebraicCycleClassSpan X 1 :=
  (spec_lefschetzOneOneFor_iff_appellHumbert_chernClassHQ X hF hBdR).mp hL
    E B hB hEalt h11

/-! ## Degenerate and convention checks -/

example : ∃ (H : HermitianForm (V := Fin (dim X.left) → ℂ))
    (hE : ∀ l m : abelianPeriodLattice X, ((0 : ℤ) : ℝ) = H.imaginary l m)
    (χ : abelianPeriodLattice X → Circle)
    (hχ : ∀ l m : abelianPeriodLattice X,
      χ (l + m) = χ l * χ m * Circle.exp (Real.pi * H.imaginary l m))
    (E' : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ),
    latticeClassHQ X E' = 0 := by
  refine ⟨HermitianForm.zero, fun _ _ ↦ by simp [HermitianForm.imaginary, HermitianForm.zero],
    fun _ ↦ 1, fun _ _ ↦ by simp [HermitianForm.imaginary, HermitianForm.zero], 0, ?_⟩
  simp [latticeClassHQ, latticeClass]

example (hg : dim X.left = 0) :
    LefschetzOneOneFor X ∧
      (LefschetzOneOneFor X ↔ LefschetzOneOneFor X) :=
  ⟨spec_lefschetzOneOneFor_dim_zero X hg, Iff.rfl⟩

example (H : HermitianForm (V := Fin (dim X.left) → ℂ))
    (E : abelianPeriodLattice X →+ abelianPeriodLattice X →+ ℤ)
    (hE : ∀ l m : abelianPeriodLattice X, (E l m : ℝ) = H.imaginary l m)
    (χ : abelianPeriodLattice X → Circle)
    (hχ : ∀ l m : abelianPeriodLattice X,
      χ (l + m) = χ l * χ m * Circle.exp (Real.pi * H.imaginary l m))
    (hg : dim X.left = 1) (l m : abelianPeriodLattice X) (hEm : E l m = 1) :
    chernForm (holLog (datumOfX X H E hE χ hχ)) l m = -1 := by
  have hsign := spec_chernForm_datumOfX X H E hE χ hχ _ (spec_holLog_isLog _).1
    (spec_holLog_isLog (datumOfX X H E hE χ hχ)).2 l m
  exact hsign.trans (by rw [hEm])

example : 2 * 1 = 2 := by norm_num
example : Circle.exp (Real.pi * (0 : ℝ)) = 1 := by simp

end HodgeLean.Adapters
