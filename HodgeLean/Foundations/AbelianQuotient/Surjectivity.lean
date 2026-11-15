import HodgeLean.Foundations.AbelianQuotient.PeriodTranspose

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Adapters
open scoped CategoryTheory.MonObj
namespace HodgeLean.Foundations.AbelianQuotient
section
variable {X Y : Over (Spec ↧ℂ)} [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
  [IsProjective X.hom] [GrpObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
theorem homPullback_analyticRepresentation_mem_lattice (f : Y ⟶ X)
    (A : (Fin (dim Y.left) → ℂ) →ₗ[ℂ] (Fin (dim X.left) → ℂ))
    (hA : ∀ v, Additive.toMul (complexExponential X (dim X.left) (A v)) =
      Point.map f (Additive.toMul (complexExponential Y (dim Y.left) v)))
    (l : abelianPeriodLattice Y) : A l ∈ abelianPeriodLattice X := by
  have hl : complexExponential Y (dim Y.left) (l : Fin (dim Y.left) → ℂ) = 0 := l.2
  have h0 := hA 0
  rw [map_zero, complexExponential_zero, complexExponential_zero] at h0
  change complexExponential X (dim X.left) (A l) = 0
  apply Additive.toMul.injective
  rw [hA, hl, ← h0]

theorem homPullback_analyticRepresentation_loop (f : Y ⟶ X)
    (A : (Fin (dim Y.left) → ℂ) →ₗ[ℂ] (Fin (dim X.left) → ℂ))
    (hA : ∀ v, Additive.toMul (complexExponential X (dim X.left) (A v)) =
      Point.map f (Additive.toMul (complexExponential Y (dim Y.left) v)))
    (l : abelianPeriodLattice Y) :
    (Point.continuousMap f).comp (abelianLatticeLoop Y l) =
      abelianLatticeLoop X ⟨A l, homPullback_analyticRepresentation_mem_lattice f A hA l⟩ := by
  refine ContinuousMap.ext fun z => ?_
  induction z using QuotientAddGroup.induction_on with
  | H t =>
    change Point.map f (Additive.toMul (oneParameterSubgroup Y (dim Y.left)
        (l : Fin (dim Y.left) → ℂ) t)) =
      Additive.toMul (oneParameterSubgroup X (dim X.left) (A l) t)
    rw [← complexExponential_smul, ← complexExponential_smul, ← hA,
      LinearMap.map_smul_of_tower]

theorem abelianPeriod_homPullback_analyticRepresentation (f : Y ⟶ X)
    (A : (Fin (dim Y.left) → ℂ) →ₗ[ℂ] (Fin (dim X.left) → ℂ))
    (hA : ∀ v, Additive.toMul (complexExponential X (dim X.left) (A v)) =
      Point.map f (Additive.toMul (complexExponential Y (dim Y.left) v)))
    (x : HQ X 1) (l : abelianPeriodLattice Y) :
    abelianPeriod Y (homPullback f 1 x) l =
      abelianPeriod X x ⟨A l, homPullback_analyticRepresentation_mem_lattice f A hA l⟩ := by
  have hc : cupComparison Y 1 (homPullback f 1 x) =
      cohomologyMap ℚ 1 (TopCat.ofHom (Point.continuousMap f)) (cupComparison X 1 x) := by
    simp [homPullback]
  change loopPeriod (abelianLatticeLoop Y l) (cupComparison Y 1 (homPullback f 1 x)) =
    loopPeriod (abelianLatticeLoop X _) (cupComparison X 1 x)
  rw [hc, ← loopPeriod_comp, homPullback_analyticRepresentation_loop f A hA]

end

theorem lattice_eq_of_period (X : Variety) {a b : abelianPeriodLattice X.X}
    (h : ∀ x, abelianPeriod X.X x a = abelianPeriod X.X x b) : a = b := by
  obtain ⟨e, he⟩ := spec_abelianPeriod_equiv X.X
  refine (abelianLatticeBasis X.X).ext_elem fun i => ?_
  let χ : abelianPeriodLattice X.X →+ ℚ :=
    (Int.castAddHom ℚ).comp ((abelianLatticeBasis X.X).coord i).toAddMonoidHom
  have hχ : χ a = χ b := by
    simpa only [← he, e.apply_symm_apply] using h (e.symm χ)
  have h2 : ((abelianLatticeBasis X.X).repr a i : ℚ) =
      (abelianLatticeBasis X.X).repr b i := hχ
  exact_mod_cast h2

theorem analytic_surjective_of_injective_pullback {P Q : Variety} (f : Hom P Q)
    (hi : Function.Injective (homPullback f.hom 1))
    (A : (Fin (dim P.X.left) → ℂ) →ₗ[ℂ] (Fin (dim Q.X.left) → ℂ))
    (hA : ∀ v, Additive.toMul (complexExponential Q.X (dim Q.X.left) (A v)) =
      Point.map f.hom (Additive.toMul (complexExponential P.X (dim P.X.left) v))) :
    Function.Surjective A := by
  let T := (homPullback f.hom 1).leftInverse
  have hT : ∀ x, T (homPullback f.hom 1 x) = x :=
    LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr hi)
  obtain ⟨N, hN, ψ, hψ⟩ := period_transpose P Q T
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hlat : ∀ l : abelianPeriodLattice Q.X, A (ψ l) = N • (l : Fin (dim Q.X.left) → ℂ) := by
    intro l
    have h := lattice_eq_of_period Q (a :=
      ⟨A (ψ l), homPullback_analyticRepresentation_mem_lattice f.hom A hA (ψ l)⟩)
      (b := N • l) ?_
    · exact congrArg Subtype.val h
    intro x
    rw [← abelianPeriod_homPullback_analyticRepresentation f.hom A hA x (ψ l),
      ← hψ, hT, map_smul, Pi.smul_apply]
    change (N : ℚ) * abelianPeriod Q.X x l = _
    obtain ⟨e, he⟩ := spec_abelianPeriod_equiv Q.X
    simp only [← he, map_nsmul, nsmul_eq_mul]
  letI := isZLattice_complexExponentialLattice Q.X (dim Q.X.left)
  letI := discrete_complexExponentialLattice Q.X (dim Q.X.left)
  let b := (abelianLatticeBasis Q.X).ofZLatticeBasis ℝ (abelianPeriodLattice Q.X)
  have hb : ∀ i, b i ∈ LinearMap.range (A.restrictScalars ℝ) := by
    intro i
    refine ⟨(N : ℂ)⁻¹ • (ψ (abelianLatticeBasis Q.X i) : Fin (dim P.X.left) → ℂ), ?_⟩
    change A (_ • _) = b i
    rw [map_smul, hlat, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
      inv_mul_cancel₀ hN0, one_smul]
    exact (Module.Basis.ofZLatticeBasis_apply ℝ _ _ i).symm
  have hr : LinearMap.range (A.restrictScalars ℝ) = ⊤ := by
    apply top_unique
    rw [← b.span_eq]
    exact Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hb i)
  exact (LinearMap.range_eq_top (f := A.restrictScalars ℝ)).mp hr

end HodgeLean.Foundations.AbelianQuotient
