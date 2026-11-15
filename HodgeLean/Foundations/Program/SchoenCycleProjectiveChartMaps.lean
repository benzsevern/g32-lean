import HodgeLean.Foundations.Program.SchoenCycleProjectiveQuotientCharts

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ComplexProjectiveSpace MvPolynomial HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program

/-- The base change of the integral standard chart inclusion.
Source: Schoen (1988), Lemma 2.4 proof, printed p. 15. -/
def s2e_baseChartι {k : ℕ} (i : Fin (k + 1)) :
    pullback (terminal.from (Spec ↧ℂ))
      (terminal.from (Spec ↧(Away (UniversalGrading k) (X i)))) ⟶
        ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ) :=
  pullback.lift (pullback.fst _ _)
    (pullback.snd _ _ ≫ Proj.awayι _ _ (isHomogeneous_X _ i) zero_lt_one)
    (Subsingleton.elim _ _)

/-- The affine base-change chart is the pullback of the integral chart.
Source: Schoen (1988), Lemma 2.4 proof, printed p. 15. -/
theorem s2e_baseChart_isPullback {k : ℕ} (i : Fin (k + 1)) :
    IsPullback (pullback.snd _ _) (s2e_baseChartι i)
      (Proj.awayι (UniversalGrading k) (X i) (isHomogeneous_X _ i) zero_lt_one)
      (pullback.snd (terminal.from (Spec ↧ℂ)) (terminal.from (Proj (UniversalGrading k)))) := by
  have hw : pullback.snd _ _ ≫ Proj.awayι _ _ (isHomogeneous_X _ i) zero_lt_one =
      s2e_baseChartι i ≫ pullback.snd _ _ := by
    simp only [s2e_baseChartι, pullback.lift_snd]
  refine ⟨⟨hw⟩, ⟨PullbackCone.IsLimit.mk hw
    (fun s => pullback.lift (s.snd ≫ pullback.fst _ _) s.fst (Subsingleton.elim _ _))
    (fun s => by simp only [pullback.lift_snd]) ?_ ?_⟩⟩
  · intro s
    apply pullback.hom_ext
    · simp only [s2e_baseChartι, Category.assoc, pullback.lift_fst]
    · simp only [s2e_baseChartι, Category.assoc, pullback.lift_snd_assoc, pullback.lift_snd]
      exact s.condition
  · intro s m hm₁ hm₂
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
      have h := congrArg (fun f => f ≫ pullback.fst _ _) hm₂
      simpa only [s2e_baseChartι, Category.assoc, pullback.lift_fst] using h
    · rw [pullback.lift_snd]
      exact hm₁

instance {k : ℕ} (i : Fin (k + 1)) : IsOpenImmersion (s2e_baseChartι i) :=
  MorphismProperty.of_isPullback (s2e_baseChart_isPullback i) inferInstance

/-- The specified normalized chart is the affine base-change chart in normalized coordinates.
Source: Schoen (1988), Lemma 2.4 proof, printed p. 15. -/
theorem s2e_chart_factorization {k : ℕ} (i : Fin (k + 1)) :
    s2e_s2b_chart i = (s2e_projectiveChartIso i).hom ≫ s2e_baseChartι i := by
  apply pullback.hom_ext
  · simp only [s2e_s2b_chart, s2e_baseChartι, Category.assoc, pullback.lift_fst,
      s2e_projectiveChartIso_fst]
  · simp only [s2e_s2b_chart, s2e_baseChartι, Category.assoc, pullback.lift_snd]
    rw [← Category.assoc, s2e_projectiveChartIso_snd]

instance {k : ℕ} (i : Fin (k + 1)) : IsOpenImmersion (s2e_s2b_chart i) := by
  rw [s2e_chart_factorization]
  infer_instance

/-- The normalized chart has exactly the standard homogeneous basic-open image.
Source: Schoen (1988), Lemma 2.4 proof, printed p. 15. -/
theorem s2e_chart_range {k : ℕ} (i : Fin (k + 1)) :
    Set.range (s2e_s2b_chart i) = projectiveSpaceBasicOpen k (X i) := by
  rw [s2e_chart_factorization, Scheme.Hom.comp_base, TopCat.coe_comp,
    Set.range_comp, (s2e_projectiveChartIso i).hom.surjective.range_eq, Set.image_univ]
  have h := Scheme.image_preimage_eq_of_isPullback (s2e_baseChart_isPullback i) Set.univ
  simp only [Set.preimage_univ, Set.image_univ, ← Scheme.Hom.coe_opensRange,
    Proj.opensRange_awayι, projectiveSpaceBasicOpen, Scheme.Hom.coe_preimage] at h ⊢
  convert! h using 1

/-- The normalized affine chart is isomorphic to the specified open subscheme.
Source: Schoen (1988), Lemma 2.4 proof, printed p. 15. -/
def s2e_chartOpenIso {k : ℕ} (i : Fin (k + 1)) :
    Spec ↧(MvPolynomial {j : Fin (k + 1) // j ≠ i} ℂ) ≅
      (projectiveSpaceBasicOpen k (X i)).toScheme :=
  IsOpenImmersion.isoOfRangeEq (s2e_s2b_chart i) (projectiveSpaceBasicOpen k (X i)).ι
    ((s2e_chart_range i).trans (Scheme.Opens.range_ι _).symm)

end HodgeLean.Foundations.Program
