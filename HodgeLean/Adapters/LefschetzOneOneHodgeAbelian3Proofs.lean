import HodgeLean.Adapters.LefschetzOneOneHodgeAbelian2
import HodgeLean.Adapters.RiemannFormHermitian

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.AppellHumbert
open HodgeLean.Foundations.AutomorphyChernClass

namespace HodgeLean.Adapters

variable (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
  [IsProjective X.hom]

theorem bh3_exists_chernClassHQ_of_riemann
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
        latticeClassHQ X E' = -latticeClassHQ X E := by
  obtain ⟨H, hE, hHB, χ, hχ, -⟩ :=
    spec_exists_datumOfX_of_riemann X E hEalt B hB h11
  obtain ⟨E', hE', hclass⟩ := spec_chernClassHQ_datumOfX X H E hE χ hχ _
    (spec_holLog_isLog _).1 (spec_holLog_isLog (datumOfX X H E hE χ hχ)).2
  refine ⟨H, hE, hHB, ?_, χ, hχ, E', hE', hclass⟩
  intro v w
  rw [spec_hermitian_toFun_eq_imaginary H v w, hHB, hHB]

theorem bh3_lefschetzOneOneFor_iff_appellHumbert_chernClassHQ
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
            latticeClassHQ X E' ∈ algebraicCycleClassSpan X 1 := by
  rw [spec_lefschetzOneOneFor_iff_riemann_latticeClassHQ X hF hBdR]
  constructor
  · intro h E B hB hEalt h11
    obtain ⟨H, hE, -, -, χ, hχ, E', hE', hclass⟩ :=
      bh3_exists_chernClassHQ_of_riemann X E B hB hEalt h11
    refine ⟨H, hE, χ, hχ, E', hE', hclass, ?_⟩
    rw [hclass]
    exact Submodule.neg_mem _ (h E B hB hEalt h11)
  · intro h E B hB hEalt h11
    obtain ⟨H, hE, χ, hχ, E', -, hclass, hmem⟩ := h E B hB hEalt h11
    rw [← neg_neg (latticeClassHQ X E), ← hclass]
    exact Submodule.neg_mem _ hmem

end HodgeLean.Adapters
