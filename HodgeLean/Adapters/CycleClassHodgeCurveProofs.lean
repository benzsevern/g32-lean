import HodgeLean.Adapters.CycleClassHodgeCurveDefs
import HodgeLean.RealDefs.CupFiltered
import HodgeLean.RealDefs.TopDegreeRank
import HodgeLean.RealDefs.FundamentalClassUnit

/-! # Proof obligations for `CycleClassIsHodge` on curves -/

noncomputable section
open CategoryTheory AlgebraicGeometry ComplexPoint
open scoped TensorProduct
open HodgeLean.RealDefs

namespace HodgeLean.Adapters

attribute [local instance] analyticHasDerivedCategory

set_option linter.auxLemma false in
attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1
  TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5

/-- Exactness of `Hom(A, T₁[n]) → Hom(A, T₂[n]) → Hom(A, T₃[n])` for a distinguished triangle
`T`. -/
theorem coyoneda_exact₂_shift {C : Type*} [Category C] [Preadditive C] [Limits.HasZeroObject C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (T : Pretriangulated.Triangle C) (hT : T ∈ distTriang C) (n : ℤ) {A : C}
    (f : A ⟶ T.obj₂⟦n⟧) (hf : f ≫ T.mor₂⟦n⟧' = 0) :
    ∃ g : A ⟶ T.obj₁⟦n⟧, f = g ≫ T.mor₁⟦n⟧' := by
  have hT' : Pretriangulated.Triangle.mk (n.negOnePow • T.mor₁⟦n⟧') (n.negOnePow • T.mor₂⟦n⟧')
      (n.negOnePow • T.mor₃⟦n⟧' ≫ (shiftFunctorComm C 1 n).hom.app T.obj₁) ∈ distTriang C :=
    Pretriangulated.Triangle.shift_distinguished T hT n
  obtain ⟨g, hg⟩ := Pretriangulated.Triangle.coyoneda_exact₂ _ hT' f (by
    rw [Pretriangulated.Triangle.mk_mor₂, Linear.comp_units_smul, hf, smul_zero])
  refine ⟨n.negOnePow • g, ?_⟩
  rw [hg, Pretriangulated.Triangle.mk_mor₁, Linear.comp_units_smul, Linear.units_smul_comp]

/-- For a short exact sequence `0 → K₁ → K₂ → K₃ → 0` of complexes with `ℍ^n(X; K₃) = 0`, the map
`ℍ^n(X; K₁) → ℍ^n(X; K₂)` is onto: exactness of the long exact sequence at `ℍ^n(X; K₂)`. -/
theorem hypercohomologyMap_surjective_of_shortExact (X : Over (Spec ↧ℂ))
    {S : ShortComplex (CochainComplex (AnalyticAdditiveSheaf X) ℤ)} (hS : S.ShortExact) (n : ℤ)
    [Subsingleton ℍ^n(X; S.X₃)] :
    Function.Surjective (hypercohomologyMap X S.f n) := by
  intro β
  have key : ∀ {K L : CochainComplex (AnalyticAdditiveSheaf X) ℤ} (φ : K ⟶ L) (γ : ℍ^n(X; K)),
      Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q
          (hypercohomologyMap X φ n γ) =
        Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q γ ≫
          (DerivedCategory.Q.map φ)⟦n⟧' := by
    intro K L φ γ
    simp only [hypercohomologyMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      Localization.SmallShiftedHom.equiv_comp, Localization.SmallShiftedHom.equiv_mk₀,
      ShiftedHom.comp_mk₀]
  have h0 : Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q β ≫
      (DerivedCategory.Q.map S.g)⟦n⟧' = 0 := by
    rw [← key, Subsingleton.elim (hypercohomologyMap X S.g n β) 0, hypercohomologyEquiv_zero]
  obtain ⟨g, hg⟩ := coyoneda_exact₂_shift _ (DerivedCategory.triangleOfSES_distinguished hS) n
    (Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X) DerivedCategory.Q β) h0
  obtain ⟨γ, hγ⟩ := (Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X)
    DerivedCategory.Q).surjective g
  refine ⟨γ, (Localization.SmallShiftedHom.equiv (analyticQuasiIsomorphisms X)
    DerivedCategory.Q).injective ?_⟩
  rw [key, hγ, hg]
  rfl

/-- `F^p Ω•(X) → Ω•(X)` is an isomorphism in every degree `i ≥ p`. -/
theorem isIso_hodgeFilteredDeRhamInclusion_f (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] {p i : ℤ} (h : p ≤ i) : IsIso ((hodgeFilteredDeRhamInclusion X p).f i) := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, i = p + k := ⟨(i - p).toNat, by lia⟩
  rw [show (hodgeFilteredDeRhamInclusion X p).f (p + k) = _ from
    HomologicalComplex.stupidTruncInclusion_f Ω•(X) (ComplexShape.embeddingUpIntGE p) (i := k) rfl]
  exact Iso.isIso_hom _

/-- The inclusion `σ_{≥q+1} Ω• → σ_{≥q} Ω•`. -/
def hodgeFilteredSuccMap (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] (q : ℤ) :
    F^(q + 1) Ω•(X) ⟶ F^q Ω•(X) :=
  have : (F^(q + 1) Ω•(X)).IsStrictlyGE q := (F^(q + 1) Ω•(X)).isStrictlyGE_of_ge q (q + 1) (by lia)
  inv (HomologicalComplex.stupidTruncInclusion (F^(q + 1) Ω•(X))
      (ComplexShape.embeddingUpIntGE q)) ≫
    HomologicalComplex.stupidTruncMap (hodgeFilteredDeRhamInclusion X (q + 1))
      (ComplexShape.embeddingUpIntGE q)

theorem hodgeFilteredSuccMap_comp (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    (q : ℤ) :
    hodgeFilteredSuccMap X q ≫ hodgeFilteredDeRhamInclusion X q =
      hodgeFilteredDeRhamInclusion X (q + 1) := by
  have : (F^(q + 1) Ω•(X)).IsStrictlyGE q := (F^(q + 1) Ω•(X)).isStrictlyGE_of_ge q (q + 1) (by lia)
  have hc : HomologicalComplex.stupidTruncMap (hodgeFilteredDeRhamInclusion X (q + 1))
      (ComplexShape.embeddingUpIntGE q) ≫ hodgeFilteredDeRhamInclusion X q =
    HomologicalComplex.stupidTruncInclusion (F^(q + 1) Ω•(X)) (ComplexShape.embeddingUpIntGE q) ≫
      hodgeFilteredDeRhamInclusion X (q + 1) :=
    HomologicalComplex.stupidTruncMap_comp_stupidTruncInclusion _ _
  exact (Category.assoc _ _ _).trans
    ((congrArg (inv (HomologicalComplex.stupidTruncInclusion (F^(q + 1) Ω•(X))
      (ComplexShape.embeddingUpIntGE q)) ≫ ·) hc).trans (IsIso.inv_hom_id_assoc _ _))

/-- The projection `σ_{≥q} Ω• → Ω^q[-q]` onto the degree-`q` term. -/
def hodgeFilteredToFormsShifted (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    (q : ℤ) : F^q Ω•(X) ⟶ holomorphicFormsShifted X q :=
  HomologicalComplex.mkHomToSingle ((hodgeFilteredDeRhamInclusion X q).f q) fun i hi =>
    ((F^q Ω•(X)).isZero_of_isStrictlyGE q i (by
      simp only [ComplexShape.up_Rel] at hi; lia)).eq_of_src _ _

/-- The short complex `σ_{≥q+1} Ω• → σ_{≥q} Ω• → Ω^q[-q]`. -/
abbrev hodgeFilteredShortComplex (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    (q : ℤ) : ShortComplex (CochainComplex (AnalyticAdditiveSheaf X) ℤ) :=
  ShortComplex.mk (hodgeFilteredSuccMap X q) (hodgeFilteredToFormsShifted X q) (by
    ext i
    by_cases hi : i < q + 1
    · exact ((F^(q + 1) Ω•(X)).isZero_of_isStrictlyGE (q + 1) i hi).eq_of_src _ _
    · exact (HomologicalComplex.isZero_single_obj_X _ q _ i (by lia)).eq_of_tgt _ _)

theorem hodgeFilteredShortComplex_shortExact (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] (q : ℤ) : (hodgeFilteredShortComplex X q).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i => ?_
  by_cases hi : i < q + 1
  · have h1 : Limits.IsZero ((F^(q + 1) Ω•(X)).X i) :=
      (F^(q + 1) Ω•(X)).isZero_of_isStrictlyGE (q + 1) i hi
    have : Mono ((hodgeFilteredShortComplex X q).map (HomologicalComplex.eval _ _ i)).f :=
      ⟨fun _ _ _ => h1.eq_of_tgt _ _⟩
    by_cases hq : i = q
    · subst i
      have : IsIso ((hodgeFilteredShortComplex X q).map (HomologicalComplex.eval _ _ q)).g := by
        change IsIso ((hodgeFilteredToFormsShifted X q).f q)
        rw [hodgeFilteredToFormsShifted, HomologicalComplex.mkHomToSingle_f]
        exact @IsIso.comp_isIso _ _ _ _ _ _ _ (isIso_hodgeFilteredDeRhamInclusion_f X (le_refl q))
          (Iso.isIso_inv _)
      exact { exact := (ShortComplex.exact_iff_mono _ (h1.eq_of_src _ _)).mpr inferInstance }
    · have h3 : Limits.IsZero ((holomorphicFormsShifted X q).X i) :=
        HomologicalComplex.isZero_single_obj_X _ q _ i hq
      have : Epi ((hodgeFilteredShortComplex X q).map (HomologicalComplex.eval _ _ i)).g :=
        ⟨fun _ _ _ => h3.eq_of_src _ _⟩
      exact { exact := (ShortComplex.exact_of_isZero_X₂ _
        ((F^q Ω•(X)).isZero_of_isStrictlyGE q i (by lia))) }
  · have h3 : Limits.IsZero ((holomorphicFormsShifted X q).X i) :=
      HomologicalComplex.isZero_single_obj_X _ q _ i (by lia)
    have : Epi ((hodgeFilteredShortComplex X q).map (HomologicalComplex.eval _ _ i)).g :=
      ⟨fun _ _ _ => h3.eq_of_src _ _⟩
    have : IsIso ((hodgeFilteredShortComplex X q).map (HomologicalComplex.eval _ _ i)).f := by
      change IsIso ((hodgeFilteredSuccMap X q).f i)
      have h₁ := isIso_hodgeFilteredDeRhamInclusion_f X (p := q) (i := i) (by lia)
      have h₂ := isIso_hodgeFilteredDeRhamInclusion_f X (p := q + 1) (i := i) (by lia)
      have hc : (hodgeFilteredSuccMap X q).f i ≫ (hodgeFilteredDeRhamInclusion X q).f i =
          (hodgeFilteredDeRhamInclusion X (q + 1)).f i := by
        rw [← HomologicalComplex.comp_f, hodgeFilteredSuccMap_comp]
      rw [← hc] at h₂
      exact IsIso.of_isIso_comp_right _ ((hodgeFilteredDeRhamInclusion X q).f i)
    exact { exact := (ShortComplex.exact_iff_epi _ (h3.eq_of_tgt _ _)).mpr inferInstance }

theorem spec_hodgeFiltration_succ_eq_of_subsingleton_aux (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] (q n : ℤ) (h : Subsingleton ℍ^n(X; holomorphicFormsShifted X q)) :
    F^(q + 1) H_dR^n(X) = F^q H_dR^n(X) := by
  refine le_antisymm (hodgeFiltration_succ_le X q n) ?_
  rintro _ ⟨β, rfl⟩
  have : Subsingleton ℍ^n(X; (hodgeFilteredShortComplex X q).X₃) := h
  obtain ⟨γ, rfl⟩ := hypercohomologyMap_surjective_of_shortExact X
    (hodgeFilteredShortComplex_shortExact X q) n β
  refine ⟨γ, ?_⟩
  exact (congrArg (fun φ => hypercohomologyMap X φ n γ) (hodgeFilteredSuccMap_comp X q).symm).trans
    (hypercohomologyMap_comp_apply X _ _ n γ)

theorem spec_hodgeFiltration_eq_top_of_subsingleton_aux (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] (p : ℕ) (n : ℤ)
    (h : ∀ q : ℕ, q < p → Subsingleton ℍ^n(X; holomorphicFormsShifted X q)) :
    F^(p : ℤ) H_dR^n(X) = ⊤ := by
  induction p with
  | zero => exact hodgeFiltration_eq_top_of_nonpos X le_rfl n
  | succ p ih =>
    have := spec_hodgeFiltration_succ_eq_of_subsingleton_aux X p n (h p (Nat.lt_succ_self p))
    push_cast
    rw [this, ih fun q hq => h q (Nat.lt_succ_of_lt hq)]

theorem spec_hodgeClasses_eq_top_of_hodgeFiltration_aux (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] (p : ℕ) (h : F^(p : ℤ) H_dR^((2 * p : ℕ) : ℤ)(X) = ⊤) :
    Hdg^p(X; ℚ) = ⊤ := by
  have hc : conjHodgeFiltrationComplexSubmodule X (p : ℤ) ((2 * p : ℕ) : ℤ) = ⊤ := by
    rw [conjHodgeFiltrationComplexSubmodule, h, Submodule.comap_top]
  have hp : hodgePiece X p p ((2 * p : ℕ) : ℤ) = ⊤ := by
    rw [hodgePiece, h, hc, top_inf_eq]
  rw [eq_top_iff]
  intro a _
  show _ ∈ ((hodgePiece X p p ((2 * p : ℕ) : ℤ)).restrictScalars ℚ).comap _
  rw [hp]
  trivial

theorem spec_hodgeClasses_zero_eq_top_aux (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] :
    Hdg^0(X; ℚ) = ⊤ :=
  spec_hodgeClasses_eq_top_of_hodgeFiltration_aux X 0
    (hodgeFiltration_eq_top_of_nonpos X (by simp) _)

theorem spec_algebraicCycleClassSpan_le_hodgeClasses_of_subsingleton_aux (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (p : ℕ)
    (h : Subsingleton (HQ X (2 * p))) :
    algebraicCycleClassSpan X p ≤ Hdg^p(X; ℚ) := by
  intro a _
  have : a = 0 := @Subsingleton.elim _ h a 0
  rw [this]
  exact zero_mem _

theorem spec_pointClass_mem_cohomologyHodgePiece_aux (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom]
    (h𝒪 : Subsingleton ℍ^2(X; holomorphicFormsShifted X 0))
    (x : X.left) (hx : Order.coheight x = 1) :
    (1 : ℂ) ⊗ₜ[ℚ] (cycleComponentSheafClass X x hx : HQ X 2) ∈
      cohomologyHodgePiece X 2 ((1 : ℤ), (1 : ℤ)) := by
  have hF : F^((1 : ℕ) : ℤ) H_dR^((2 * 1 : ℕ) : ℤ)(X) = ⊤ :=
    spec_hodgeFiltration_eq_top_of_subsingleton_aux X 1 _ fun q hq => by
      obtain rfl : q = 0 := by omega
      exact h𝒪
  have := spec_hodgeClasses_eq_top_of_hodgeFiltration_aux X 1 hF
  have hmem : (cycleComponentSheafClass X x hx : H^(2 * 1)(X; ℚ)) ∈ Hdg^1(X; ℚ) := by
    rw [this]; trivial
  exact (mem_hodgeClasses_iff_tmul_mem 1 _).mp hmem

theorem spec_cycleClassIsHodge_of_curve_aux (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom]
    (h𝒪 : Subsingleton ℍ^2(X; holomorphicFormsShifted X 0)) :
    CycleClassIsHodge X := by
  refine ⟨fun p => ?_⟩
  rcases Nat.lt_or_ge p 2 with hp | hp
  · interval_cases p
    · rw [spec_hodgeClasses_zero_eq_top_aux X]; exact le_top
    · rw [spec_hodgeClasses_eq_top_of_hodgeFiltration_aux X 1
        (spec_hodgeFiltration_eq_top_of_subsingleton_aux X 1 _ fun q hq => by
          obtain rfl : q = 0 := by omega
          exact h𝒪)]
      exact le_top
  · exact spec_algebraicCycleClassSpan_le_hodgeClasses_of_subsingleton_aux X p
      (j5d_subsingleton_HQ_of_lt X 1 (by omega))

theorem spec_hodgeFiltration_one_zero_ne_top_aux (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (hB : BettiDeRhamIso X) :
    F^1 H_dR^((0 : ℕ) : ℤ)(X) ≠ ⊤ := by
  rw [hodgeFiltration_eq_bot_of_lt X (by norm_num)]
  intro htop
  have hu : (1 : ℂ) ⊗ₜ[ℚ] (unitClass X : HQ X 0) ≠ 0 := by
    rw [Ne, Module.FaithfullyFlat.one_tmul_eq_zero_iff]
    exact unitClass_ne_zero' X
  have h0 : bettiDeRhamHQ X 0 ((1 : ℂ) ⊗ₜ[ℚ] (unitClass X : HQ X 0)) = 0 := by
    have : bettiDeRhamHQ X 0 ((1 : ℂ) ⊗ₜ[ℚ] (unitClass X : HQ X 0)) ∈
        (⊥ : Submodule ℂ H_dR^((0 : ℕ) : ℤ)(X)) := by
      rw [htop]; trivial
    exact (Submodule.mem_bot ℂ).mp this
  exact hu ((hB.bijective 0).1 (h0.trans (map_zero _).symm))

theorem spec_not_subsingleton_hypercohomology_zero_aux (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] (hB : BettiDeRhamIso X) :
    ¬ Subsingleton ℍ^((0 : ℕ) : ℤ)(X; holomorphicFormsShifted X 0) := by
  intro h
  apply spec_hodgeFiltration_one_zero_ne_top_aux X hB
  exact spec_hodgeFiltration_eq_top_of_subsingleton_aux X 1 _ fun q hq => by
    obtain rfl : q = 0 := by omega
    exact h

end HodgeLean.Adapters
