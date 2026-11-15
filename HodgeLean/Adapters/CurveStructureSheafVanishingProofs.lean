import HodgeLean.Adapters.CycleClassHodgeCurve
import HodgeLean.RealDefs.HodgeStructure

/-! # Proof obligations for `H^2(X, 𝒪_X) = 0` on curves and the unconditional-route assemblies -/

noncomputable section
open CategoryTheory TopologicalSpace AlgebraicGeometry ComplexPoint
open HodgeLean.RealDefs

namespace HodgeLean.Adapters

attribute [local instance] analyticHasDerivedCategory in
/-- A morphism `ℤ[0] ⟶ K₁[n]` in the derived category that dies in `K₂[n]` is zero when
`ℍ^{n-1}(X; K₃) = 0`: exactness of the long exact sequence at `ℍ^n(X; K₁)`. -/
theorem derivedShiftedHom_eq_zero_of_shortExact (X : Over (Spec ↧ℂ))
    {S : ShortComplex (CochainComplex (AnalyticAdditiveSheaf X) ℤ)} (hS : S.ShortExact) (n : ℤ)
    (h₃ : Subsingleton ℍ^(n - 1)(X; S.X₃))
    (φ : DerivedCategory.Q.obj (constantIntegerSheafComplexInt X) ⟶
      (DerivedCategory.Q.obj S.X₁)⟦n⟧)
    (hφ : φ ≫ (DerivedCategory.Q.map S.f)⟦n⟧' = 0) :
    φ = 0 := by
  obtain ⟨g, hg⟩ := coyoneda_exact₂_shift _
    (Pretriangulated.inv_rot_of_distTriang _ (DerivedCategory.triangleOfSES_distinguished hS)) n
    φ hφ
  have hsub : Subsingleton (DerivedCategory.Q.obj (constantIntegerSheafComplexInt X) ⟶
      (DerivedCategory.Q.obj S.X₃)⟦n - 1⟧) :=
    @Equiv.subsingleton _ _ (Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X)
      DerivedCategory.Q).symm h₃
  let e := (shiftFunctorAdd' (DerivedCategory (AnalyticAdditiveSheaf X)) (-1) n (n - 1)
    (by lia)).app (DerivedCategory.Q.obj S.X₃)
  have h0 : ∀ h : DerivedCategory.Q.obj (constantIntegerSheafComplexInt X) ⟶
      ((DerivedCategory.Q.obj S.X₃)⟦-1⟧)⟦n⟧, h = 0 := fun h => by
    rw [← cancel_mono e.inv, Limits.zero_comp]
    exact Subsingleton.elim _ _
  rw [hg, h0 g]
  exact Limits.zero_comp

theorem spec_hypercohomology_subsingleton_of_shortExact_aux (X : Over (Spec ↧ℂ))
    {S : ShortComplex (CochainComplex (AnalyticAdditiveSheaf X) ℤ)} (hS : S.ShortExact) (n : ℤ)
    (h₂ : Subsingleton ℍ^n(X; S.X₂)) (h₃ : Subsingleton ℍ^(n - 1)(X; S.X₃)) :
    Subsingleton ℍ^n(X; S.X₁) := by
  let := analyticHasDerivedCategory X
  suffices h : ∀ x : ℍ^n(X; S.X₁), x = 0 from ⟨fun α β => (h α).trans (h β).symm⟩
  intro x
  have key : Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q
        (hypercohomologyMap X S.f n x) =
      Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q x ≫
        (DerivedCategory.Q.map S.f)⟦n⟧' := by
    simp only [hypercohomologyMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      Localization.SmallShiftedHom.equiv_comp, Localization.SmallShiftedHom.equiv_mk₀,
      ShiftedHom.comp_mk₀]
  apply (Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X)
    DerivedCategory.Q).injective
  rw [hypercohomologyEquiv_zero]
  refine derivedShiftedHom_eq_zero_of_shortExact X hS n h₃ _ ?_
  rw [← key, Subsingleton.elim (hypercohomologyMap X S.f n x) 0, hypercohomologyEquiv_zero]

theorem spec_subsingleton_hypercohomology_two_of_shortExact_aux (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] {A B : AnalyticAdditiveSheaf X} (f : Ω•(X).X 0 ⟶ A)
    (g : A ⟶ B) (w : f ≫ g = 0) (hS : (ShortComplex.mk f g w).ShortExact)
    (hA : Subsingleton
      ℍ^2(X; (HomologicalComplex.single (AnalyticAdditiveSheaf X) (ComplexShape.up ℤ) 0).obj A))
    (hB : Subsingleton
      ℍ^1(X; (HomologicalComplex.single (AnalyticAdditiveSheaf X) (ComplexShape.up ℤ) 0).obj B)) :
    Subsingleton ℍ^2(X; holomorphicFormsShifted X 0) :=
  spec_hypercohomology_subsingleton_of_shortExact_aux X
    (hS.map_of_exact (HomologicalComplex.single (AnalyticAdditiveSheaf X) (ComplexShape.up ℤ) 0))
    2 hA hB

theorem spec_cycleClassIsHodge_of_curve_of_shortExact_aux (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom]
    {A B : AnalyticAdditiveSheaf X} (f : Ω•(X).X 0 ⟶ A)
    (g : A ⟶ B) (w : f ≫ g = 0) (hS : (ShortComplex.mk f g w).ShortExact)
    (hA : Subsingleton
      ℍ^2(X; (HomologicalComplex.single (AnalyticAdditiveSheaf X) (ComplexShape.up ℤ) 0).obj A))
    (hB : Subsingleton
      ℍ^1(X; (HomologicalComplex.single (AnalyticAdditiveSheaf X) (ComplexShape.up ℤ) 0).obj B)) :
    CycleClassIsHodge X :=
  spec_cycleClassIsHodge_of_curve X
    (spec_subsingleton_hypercohomology_two_of_shortExact_aux X f g w hS hA hB)

theorem spec_hodgeFiltration_eq_bot_of_dim_lt_aux (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] {p : ℤ} (hp : (dim X.left : ℤ) < p) (n : ℤ) :
    F^p H_dR^n(X) = ⊥ := by
  have hz : ∀ i : ℤ, Limits.IsZero ((F^p Ω•(X)).X i) := fun i => by
    by_cases hi : i < p
    · exact (F^p Ω•(X)).isZero_of_isStrictlyGE p i hi
    · have := isIso_hodgeFilteredDeRhamInclusion_f X (p := p) (i := i) (by lia)
      exact (holomorphicDeRhamComplexInt_isZero_X_of_lt X i (by lia)).of_iso
        (asIso ((hodgeFilteredDeRhamInclusion X p).f i))
  have : (F^p Ω•(X)).IsStrictlyGE (n + 1) :=
    ((F^p Ω•(X)).isStrictlyGE_iff (n + 1)).mpr fun i _ => hz i
  have := hypercohomology_subsingleton_of_isStrictlyGE X (F^p Ω•(X)) (lt_add_one n)
  refine eq_bot_iff.mpr ?_
  rintro _ ⟨β, rfl⟩
  rw [Subsingleton.elim β 0, map_zero]
  exact Submodule.zero_mem _

/-- If `F^q H_dR^n(X) = ⊥`, the conjugate filtration `conj F^q` is `⊥` too. -/
theorem conjHodgeFiltrationComplexSubmodule_eq_bot_of_aux (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] {q n : ℤ} (h : F^q H_dR^n(X) = ⊥) :
    conjHodgeFiltrationComplexSubmodule X q n = ⊥ := by
  refine eq_bot_iff.mpr fun α hα => ?_
  have h0 : deRhamConj X n α = 0 := by
    have : deRhamConj X n α ∈ F^q H_dR^n(X) := (mem_conjHodgeFiltrationComplexSubmodule X α).mp hα
    rw [h] at this
    exact (Submodule.mem_bot ℂ).mp this
  rw [Submodule.mem_bot, ← deRhamConj_deRhamConj X n α, h0, map_zero]

theorem spec_hodgeFiltration_dim_eq_top_of_hodgeDecomposition_aux (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (hD : HodgeDecomposition X) :
    F^((dim X.left : ℕ) : ℤ) H_dR^((2 * dim X.left : ℕ) : ℤ)(X) = ⊤ := by
  set d := dim X.left with hd
  have htop := (hD.isInternal (2 * d)).submodule_iSup_eq_top
  refine eq_top_iff.mpr (htop ▸ iSup_le fun pq => ?_)
  obtain ⟨p, q⟩ := pq
  unfold deRhamHodgePiece
  split_ifs with h
  · simp only at h
    rcases lt_trichotomy p (d : ℤ) with hp | rfl | hp
    · have hq : (dim X.left : ℤ) < q := by push_cast at h; lia
      rw [hodgePiece, conjHodgeFiltrationComplexSubmodule_eq_bot_of_aux X
        (spec_hodgeFiltration_eq_bot_of_dim_lt_aux X hq _), inf_bot_eq]
      exact bot_le
    · exact inf_le_left
    · rw [hodgePiece, spec_hodgeFiltration_eq_bot_of_dim_lt_aux X hp, bot_inf_eq]
      exact bot_le
  · exact bot_le

/-- On a curve, `F^1 H_dR^2(X) = ⊤` under `HodgeDecomposition X` (statement 5 at `d = 1`). -/
theorem hodgeFiltration_one_two_eq_top_of_curve_aux (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom]
    (hD : HodgeDecomposition X) :
    F^((1 : ℕ) : ℤ) H_dR^((2 * 1 : ℕ) : ℤ)(X) = ⊤ := by
  have h := spec_hodgeFiltration_dim_eq_top_of_hodgeDecomposition_aux X hD
  rwa [SmoothOfRelativeDimension.dim_eq X.hom 1] at h

theorem spec_cycleClassIsHodge_of_curve_of_hodgeDecomposition_aux (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom]
    (hD : HodgeDecomposition X) :
    CycleClassIsHodge X := by
  refine ⟨fun p => ?_⟩
  rcases Nat.lt_or_ge p 2 with hp | hp
  · interval_cases p
    · rw [spec_hodgeClasses_zero_eq_top X]; exact le_top
    · rw [spec_hodgeClasses_eq_top_of_hodgeFiltration X 1
        (hodgeFiltration_one_two_eq_top_of_curve_aux X hD)]
      exact le_top
  · exact spec_algebraicCycleClassSpan_le_hodgeClasses_of_subsingleton X p
      (j5d_subsingleton_HQ_of_lt X 1 (by omega))

theorem spec_not_subsingleton_hypercohomology_of_hodgePiece_ne_bot_aux (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (hD : HodgeDecomposition X) (n : ℕ)
    (h : hodgePiece X 0 (n : ℤ) (n : ℤ) ≠ ⊥) :
    ¬ Subsingleton ℍ^(n : ℤ)(X; holomorphicFormsShifted X 0) := by
  intro hs
  have hF1 : F^1 H_dR^(n : ℤ)(X) = ⊤ := by
    have := spec_hodgeFiltration_succ_eq_of_subsingleton X 0 n hs
    rw [zero_add] at this
    rw [this, hodgeFiltration_eq_top_of_nonpos X le_rfl]
  have hle : hodgePiece X 0 (n : ℤ) (n : ℤ) ≤ hodgePiece X 1 ((n : ℤ) - 1) (n : ℤ) := by
    intro α hα
    refine ⟨hF1 ▸ Submodule.mem_top, ?_⟩
    exact (mem_conjHodgeFiltrationComplexSubmodule X α).mpr
      (hodgeFiltration_le_of_le X (by lia) _
        ((mem_conjHodgeFiltrationComplexSubmodule X α).mp hα.2))
  have hdisj := ((hD.isInternal n).submodule_iSupIndep).pairwiseDisjoint
    (show ((0 : ℤ), (n : ℤ)) ≠ ((1 : ℤ), (n : ℤ) - 1) by simp)
  have e0 : deRhamHodgePiece X n ((0 : ℤ), (n : ℤ)) = hodgePiece X 0 n n := by
    unfold deRhamHodgePiece; exact ite_eq_left_of_eq_true _ _ (eq_true (by simp))
  have e1 : deRhamHodgePiece X n ((1 : ℤ), (n : ℤ) - 1) = hodgePiece X 1 ((n : ℤ) - 1) n := by
    unfold deRhamHodgePiece; exact ite_eq_left_of_eq_true _ _ (eq_true (by simp))
  have hdisj : Disjoint (hodgePiece X 0 n n) (hodgePiece X 1 ((n : ℤ) - 1) n) := by
    rw [← e0, ← e1]; exact hdisj
  exact h (le_bot_iff.mp (hdisj le_rfl hle))

theorem spec_hodgeFiltration_one_two_ne_bot_of_curve_aux (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom]
    (hB : BettiDeRhamIso X) (hD : HodgeDecomposition X) :
    F^1 H_dR^2(X) ≠ ⊥ := by
  intro hbot
  have htop := hodgeFiltration_one_two_eq_top_of_curve_aux X hD
  have hrank := j5d_finrank_HQ_two HodgeLean.Adapters.complexPointsPreconnected X
  have : Nontrivial (HQ X 2) := Module.nontrivial_of_finrank_eq_succ hrank
  obtain ⟨v, hv⟩ := exists_ne (0 : HQ X 2)
  have hu : (1 : ℂ) ⊗ₜ[ℚ] v ≠ 0 := by
    rw [Ne, Module.FaithfullyFlat.one_tmul_eq_zero_iff]
    exact hv
  have h0 : bettiDeRhamHQ X 2 ((1 : ℂ) ⊗ₜ[ℚ] v) = 0 := by
    have hmem : bettiDeRhamHQ X 2 ((1 : ℂ) ⊗ₜ[ℚ] v) ∈ F^((1 : ℕ) : ℤ) H_dR^((2 * 1 : ℕ) : ℤ)(X) := by
      rw [htop]; trivial
    have hbot' : F^((1 : ℕ) : ℤ) H_dR^((2 * 1 : ℕ) : ℤ)(X) = ⊥ := hbot
    rw [hbot'] at hmem
    exact (Submodule.mem_bot ℂ).mp hmem
  exact hu ((hB.bijective 2).1 (h0.trans (map_zero _).symm))

end HodgeLean.Adapters
