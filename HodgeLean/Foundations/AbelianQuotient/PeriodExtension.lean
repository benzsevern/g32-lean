import HodgeLean.Foundations.AbelianQuotient.QuotientTangent

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Adapters
open scoped CategoryTheory.MonObj
namespace HodgeLean.Foundations.AbelianQuotient

/-- A rational lattice character extends to a real linear tangent functional. -/
theorem exists_real_period_extension (X : Variety) (χ : abelianPeriodLattice X.X →+ ℚ) :
    ∃ F : (Fin (dim X.X.left) → ℂ) →ₗ[ℝ] ℝ,
      ∀ l : abelianPeriodLattice X.X, F l = (χ l : ℝ) := by
  letI := isZLattice_complexExponentialLattice X.X (dim X.X.left)
  letI := discrete_complexExponentialLattice X.X (dim X.X.left)
  let b := abelianLatticeBasis X.X
  let bR := b.ofZLatticeBasis ℝ (abelianPeriodLattice X.X)
  refine ⟨bR.constr ℝ (fun i => (χ (b i) : ℝ)), ?_⟩
  intro l
  simp only [Module.Basis.constr_apply_fintype, Module.Basis.equivFun_apply, smul_eq_mul]
  simp only [bR, Module.Basis.ofZLatticeBasis_repr_apply]
  conv_rhs => rw [← b.sum_repr l]
  simp only [map_sum, map_zsmul, zsmul_eq_mul, Rat.cast_sum, Rat.cast_mul, Rat.cast_intCast]

/-- A class with zero pullback has a tangent functional vanishing on the analytic image. -/
theorem period_extension_comp_zero {P Q : Variety} (f : Hom P Q)
    (I : (Fin (dim P.X.left) → ℂ) →ₗ[ℂ] (Fin (dim Q.X.left) → ℂ))
    (hI : ∀ v, Additive.toMul (complexExponential Q.X (dim Q.X.left) (I v)) =
      Point.map f.hom (Additive.toMul (complexExponential P.X (dim P.X.left) v)))
    (x : HQ Q.X 1) (hx : homPullback f.hom 1 x = 0)
    (χ : abelianPeriodLattice Q.X →+ ℚ) (hχ : ∀ l, χ l = abelianPeriod Q.X x l)
    (F : (Fin (dim Q.X.left) → ℂ) →ₗ[ℝ] ℝ)
    (hF : ∀ l : abelianPeriodLattice Q.X, F l = (χ l : ℝ)) :
    F.comp (I.restrictScalars ℝ) = 0 := by
  letI := isZLattice_complexExponentialLattice P.X (dim P.X.left)
  letI := discrete_complexExponentialLattice P.X (dim P.X.left)
  let bR := (abelianLatticeBasis P.X).ofZLatticeBasis ℝ (abelianPeriodLattice P.X)
  apply bR.ext
  intro i
  rw [LinearMap.comp_apply, LinearMap.zero_apply]
  rw [show bR i = (abelianLatticeBasis P.X i : Fin (dim P.X.left) → ℂ)
    from Module.Basis.ofZLatticeBasis_apply ℝ _ _ i]
  let l := abelianLatticeBasis P.X i
  have hl := homPullback_analyticRepresentation_mem_lattice f.hom I hI l
  have ht := abelianPeriod_homPullback_analyticRepresentation f.hom I hI x l
  rw [hx, map_zero, Pi.zero_apply] at ht
  change F (I l) = 0
  rw [hF (⟨I l, hl⟩ : abelianPeriodLattice Q.X), hχ, ← ht, Rat.cast_zero]

end HodgeLean.Foundations.AbelianQuotient
