import HodgeLean.Foundations.AbelianQuotient.Surjectivity

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Adapters
open scoped CategoryTheory.MonObj
namespace HodgeLean.Foundations.AbelianQuotient

/-- A scaled algebraic idempotent induces the same scaled identity on its period image. -/
theorem lattice_square_of_hom_square (A : Variety) (f : Hom A A)
    (φ : abelianPeriodLattice A.X →+ abelianPeriodLattice A.X)
    (hφ : ∀ x l, abelianPeriod A.X (homPullback f.hom 1 x) l =
      abelianPeriod A.X x (φ l))
    (N : ℕ) (hsq : f.hom ≫ f.hom = f.hom ^ (N : ℤ)) :
    ∀ l, φ (φ l) = N • φ l := by
  have hcoh : (homPullback f.hom 1).comp (homPullback f.hom 1) =
      (N : ℚ) • homPullback f.hom 1 := by
    rw [← spec_homPullback_comp, hsq, spec_homPullback_zpow, Int.cast_natCast]
  intro l
  apply lattice_eq_of_period A
  intro x
  obtain ⟨e, he⟩ := spec_abelianPeriod_equiv A.X
  calc
    abelianPeriod A.X x (φ (φ l)) =
        abelianPeriod A.X (homPullback f.hom 1 x) (φ l) := (hφ x (φ l)).symm
    _ = abelianPeriod A.X (homPullback f.hom 1 (homPullback f.hom 1 x)) l :=
      (hφ (homPullback f.hom 1 x) l).symm
    _ = abelianPeriod A.X ((N : ℚ) • homPullback f.hom 1 x) l := by
      change abelianPeriod A.X (((homPullback f.hom 1).comp (homPullback f.hom 1)) x) l =
        abelianPeriod A.X (((N : ℚ) • homPullback f.hom 1) x) l
      rw [hcoh]
    _ = (N : ℚ) * abelianPeriod A.X x (φ l) := by
      rw [map_smul, Pi.smul_apply, hφ]
      rfl
    _ = abelianPeriod A.X x (N • φ l) := by
      simp only [← he, map_nsmul, nsmul_eq_mul]

end HodgeLean.Foundations.AbelianQuotient
