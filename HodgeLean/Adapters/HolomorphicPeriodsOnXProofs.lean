import HodgeLean.Adapters.HolomorphicPeriodsOnXDefs

/-! # Proof obligations for integrals of holomorphic `1`-forms along paths in `X(ℂ)`

One obligation per statement of `HodgeLean.Adapters.HolomorphicPeriodsOnX`. All nine are proved, by two parallel provers. -/

noncomputable section
open CategoryTheory AlgebraicGeometry ComplexPoint TopologicalSpace Opposite
open HodgeLean.RealDefs HodgeLean.Foundations
open scoped TensorProduct

namespace HodgeLean.Adapters

theorem spec_isCoveringMap_complexExponential_aux (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X]
    [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom] [IsIntegral X.left]
    [IsProjective X.hom] :
    IsCoveringMap (fun v : Fin d → ℂ ↦ (complexExponential X d v).toMul) := by
  open scoped CategoryTheory.MonObj in
    have hq : Topology.IsQuotientMap (complexExponentialHom X d) :=
      (isOpenMap_complexExponential X d).isQuotientMap (continuous_complexExponential X d)
        (surjective_complexExponential X d)
    have hdisc : IsDiscrete ((complexExponentialHom X d).ker : Set (Fin d → ℂ)) :=
      isDiscrete_iff_discreteTopology.mpr (discrete_complexExponentialLattice X d)
    exact (hq.isAddQuotientCoveringMap_of_isDiscrete_ker_addMonoidHom hdisc).isCoveringMap

theorem spec_isExpLift_sub_eq_aux (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X] [IsCommMonObj X]
    [SmoothOfRelativeDimension d X.hom] (γ : C(unitInterval, ComplexPoint X))
    (Γ Γ' : C(unitInterval, Fin d → ℂ)) (h : IsExpLift X d γ Γ) (h' : IsExpLift X d γ Γ') :
    Γ 1 - Γ 0 = Γ' 1 - Γ' 0 := by
  open scoped CategoryTheory.MonObj in
    have hmem : ∀ t, Γ t - Γ' t ∈ complexExponentialLattice X d := fun t ↦ by
      change complexExponentialHom X d (Γ t - Γ' t) = 0
      rw [map_sub, sub_eq_zero]
      exact Additive.toMul.injective ((h t).trans (h' t).symm)
    let f : unitInterval → complexExponentialLattice X d := fun t ↦ ⟨Γ t - Γ' t, hmem t⟩
    have hf : Continuous f := (Γ.continuous.sub Γ'.continuous).subtype_mk _
    have h10 := congrArg Subtype.val (PreconnectedSpace.constant inferInstance hf (x := 1) (y := 0))
    simp only [f] at h10
    rw [sub_eq_sub_iff_sub_eq_sub, h10]

theorem spec_expLiftDisplacement_eq_aux (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X]
    [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom] (γ : C(unitInterval, ComplexPoint X))
    (Γ : C(unitInterval, Fin d → ℂ)) (h : IsExpLift X d γ Γ) :
    expLiftDisplacement X d γ = Γ 1 - Γ 0 := by
  have hex : ∃ Γ, IsExpLift X d γ Γ := ⟨Γ, h⟩
  simp only [expLiftDisplacement, hex, ↓reduceDIte]
  exact spec_isExpLift_sub_eq_aux X d γ _ Γ hex.choose_spec h

theorem spec_holomorphicPathIntegral_expPath_segment_aux (X : Over (Spec ↧ℂ)) (d : ℕ)
    [GrpObj X] [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom] [IsIntegral X.left]
    [IsProjective X.hom] (θ : (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤))
    (a b : Fin d → ℂ) :
    holomorphicPathIntegral X d θ (expPath X d (Path.segment a b).toContinuousMap) =
      ∫ᶜ x in Path.segment a b, expPullback X d θ x := by
  rw [holomorphicPathIntegral, spec_expLiftDisplacement_eq_aux X d _ _ (fun _ ↦ rfl),
    spec_curveIntegral_segment_expPullback_aux X d θ a b]
  simp

/-- A lift along the covering `exp` of a path of `X(ℂ)` is an `exp`-lift. -/
theorem isExpLift_liftPath_aux (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X]
    [SmoothOfRelativeDimension d X.hom]
    (cov : IsCoveringMap (fun v : Fin d → ℂ ↦ (complexExponential X d v).toMul))
    (γ : C(unitInterval, ComplexPoint X)) (e : Fin d → ℂ)
    (h : γ 0 = (complexExponential X d e).toMul) :
    IsExpLift X d γ (cov.liftPath γ e h) :=
  fun t ↦ congrFun (cov.liftPath_lifts γ e h) t

/-- Every point of `X(ℂ)` is `exp` of a vector, for abelian `X`. -/
theorem exists_complexExponential_eq_aux (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X]
    [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom] [IsIntegral X.left]
    [IsProjective X.hom] (x : ComplexPoint X) :
    ∃ e : Fin d → ℂ, x = (complexExponential X d e).toMul := by
  obtain ⟨e, he⟩ := surjective_complexExponential X d (Additive.ofMul x)
  exact ⟨e, by rw [he]; rfl⟩

theorem spec_holomorphicPathIntegral_trans_aux (X : Over (Spec ↧ℂ)) (d : ℕ) [GrpObj X]
    [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom] [IsIntegral X.left]
    [IsProjective X.hom] (θ : (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤))
    {x y z : ComplexPoint X} (γ : Path x y) (γ' : Path y z) :
    holomorphicPathIntegral X d θ (γ.trans γ').toContinuousMap =
      holomorphicPathIntegral X d θ γ.toContinuousMap +
        holomorphicPathIntegral X d θ γ'.toContinuousMap := by
  have cov := spec_isCoveringMap_complexExponential_aux X d
  obtain ⟨e, hpe⟩ := exists_complexExponential_eq_aux X d x
  have hΓ := isExpLift_liftPath_aux X d cov γ.toContinuousMap e (γ.source.trans hpe)
  set Γ := cov.liftPath γ.toContinuousMap e (γ.source.trans hpe)
  have h1 : γ'.toContinuousMap 0 = (complexExponential X d (Γ 1)).toMul := by
    simpa using (hΓ 1).symm
  have hΓ' := isExpLift_liftPath_aux X d cov γ'.toContinuousMap (Γ 1) h1
  have hT := isExpLift_liftPath_aux X d cov (γ.trans γ').toContinuousMap e (by simpa)
  have htr := cov.liftPath_trans hpe γ γ'
  simp only [holomorphicPathIntegral]
  rw [spec_expLiftDisplacement_eq_aux X d _ _ hT, spec_expLiftDisplacement_eq_aux X d _ _ hΓ,
    spec_expLiftDisplacement_eq_aux X d _ _ hΓ', ← map_add]
  erw [htr]
  congr 1
  have h0 : Γ 0 = e := cov.liftPath_zero ..
  have h0' : cov.liftPath γ'.toContinuousMap (Γ 1) h1 0 = Γ 1 := cov.liftPath_zero ..
  rw [h0', h0]
  simp only [ContinuousMap.coe_coe, Path.trans_apply]
  norm_num
  abel

theorem spec_holomorphicPathIntegral_eq_of_homotopic_aux (X : Over (Spec ↧ℂ)) (d : ℕ)
    [GrpObj X] [IsCommMonObj X] [SmoothOfRelativeDimension d X.hom] [IsIntegral X.left]
    [IsProjective X.hom] (θ : (holomorphicDeRhamSheaf X d 1).presheaf.obj (op ⊤))
    {x y : ComplexPoint X} (γ₀ γ₁ : Path x y) (h : γ₀.Homotopic γ₁) :
    holomorphicPathIntegral X d θ γ₀.toContinuousMap =
      holomorphicPathIntegral X d θ γ₁.toContinuousMap := by
  have cov := spec_isCoveringMap_complexExponential_aux X d
  obtain ⟨e, hpe⟩ := exists_complexExponential_eq_aux X d x
  have h₀ : γ₀.toContinuousMap 0 = (complexExponential X d e).toMul := γ₀.source.trans hpe
  have h₁ : γ₁.toContinuousMap 0 = (complexExponential X d e).toMul := γ₁.source.trans hpe
  simp only [holomorphicPathIntegral]
  rw [spec_expLiftDisplacement_eq_aux X d _ _ (isExpLift_liftPath_aux X d cov _ e h₀),
    spec_expLiftDisplacement_eq_aux X d _ _ (isExpLift_liftPath_aux X d cov _ e h₁),
    cov.liftPath_apply_one_eq_of_homotopicRel h e h₀ h₁, cov.liftPath_zero, cov.liftPath_zero]

theorem spec_expLiftDisplacement_abelianLatticePath_aux (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (l : abelianPeriodLattice X) :
    expLiftDisplacement X (dim X.left) (abelianLatticePath X l) = l := by
  let : IsCommMonObj X := isCommMonObj_of_complexSelfProductIntegral X
    (complexSelfProductIntegral_of_isIntegral X)
  have h : IsExpLift X (dim X.left) (abelianLatticePath X l)
      (Path.segment (0 : Fin (dim X.left) → ℂ) (l : Fin (dim X.left) → ℂ)).toContinuousMap :=
    fun t ↦ (spec_abelianLatticeLoop_eq_complexExponential_segment X l t).symm
  rw [spec_expLiftDisplacement_eq_aux X (dim X.left) _ _ h]
  simp

theorem spec_holomorphicPathIntegral_abelianLatticePath_aux (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (θ : (holomorphicDeRhamSheaf X (dim X.left) 1).presheaf.obj (op ⊤))
    (l : abelianPeriodLattice X) :
    holomorphicPathIntegral X (dim X.left) θ (abelianLatticePath X l) =
      ∫ᶜ x in Path.segment 0 (l : Fin (dim X.left) → ℂ), expPullback X (dim X.left) θ x := by
  let : IsCommMonObj X := isCommMonObj_of_complexSelfProductIntegral X
    (complexSelfProductIntegral_of_isIntegral X)
  rw [spec_curveIntegral_segment_expPullback, sub_zero, holomorphicPathIntegral,
    spec_expLiftDisplacement_abelianLatticePath_aux]

theorem spec_periods_of_holomorphicPathIntegral_aux (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (c : ℂ)
    (hloop : ∀ (z : (filteredGlobalSections X).cycles ((1 : ℕ) : ℤ)) (ω : ℂ ⊗[ℚ] HQ X 1),
      bettiDeRhamHQ X 1 ω = cycleDeRhamClass X z → ∀ l : abelianPeriodLattice X,
        complexAbelianPeriod X ω l =
          c * holomorphicPathIntegral X (dim X.left) (cycleOneForm X z) (abelianLatticePath X l)) :
    ∀ (z : (filteredGlobalSections X).cycles ((1 : ℕ) : ℤ)) (ω : ℂ ⊗[ℚ] HQ X 1),
      bettiDeRhamHQ X 1 ω = cycleDeRhamClass X z → ∀ l : abelianPeriodLattice X,
        complexAbelianPeriod X ω l = c * ∫ᶜ x in Path.segment 0 (l : Fin (dim X.left) → ℂ),
          expPullback X (dim X.left) (cycleOneForm X z) x := by
  intro z ω h l
  rw [hloop z ω h l]
  exact congrArg (c * ·) (spec_holomorphicPathIntegral_abelianLatticePath_aux X (cycleOneForm X z) l)

end HodgeLean.Adapters
