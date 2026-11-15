import HodgeLean.Adapters.IntersectionProductMovingLineCharts
import HodgeLean.Adapters.IntersectionProductMovingGlue

/-! # The projective line as a pointed curve

The projective line `ℙ¹_ℤ = Proj ℤ[s₀, s₁]` is integral, its generic point is the generic point
of the chart `D₊(s₀)`, and the rational function `t = s₁/(s₁ - s₀)` lies in the maximal ideal of
every point of `{t₁ = 0}` (`t₁ = s₁/s₀`) and is a unit off `{t₁ = 0} ∪ {t₁ = 1}`.

Source: Hartshorne, *Algebraic Geometry*, II, Proposition 2.5 and Exercise 3.1 (integrality from
an affine cover by domains); Fulton, *Intersection Theory*, second edition, §1.6.
HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial HomogeneousLocalization
open AlgebraicGeometry.ComplexProjectiveSpace HodgeLean.Foundations

namespace HodgeLean.Adapters

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The chart ring `ℤ[s₀, s₁]_(s_i), degree 0`. -/
abbrev a3m_A1 (i : Fin (1 + 1)) : Type := Away (UniversalGrading 1) (X i : UniversalRing 1)

instance a3m_away_isDomain (i : Fin (1 + 1)) : IsDomain (a3m_A1 i) := by
  have : IsDomain (ULift.{0} ℤ) :=
    Function.Injective.isDomain (ULift.ringEquiv (R := ℤ)).toRingHom ULift.ringEquiv.injective
  have hL : IsDomain (Localization.Away (X i : UniversalRing.{0} 1)) :=
    IsLocalization.isDomain_localization
      (powers_le_nonZeroDivisors_of_noZeroDivisors (X_ne_zero (R := ULift.{0} ℤ) i))
  exact Function.Injective.isDomain
    (algebraMap (a3m_A1 i) (Localization.Away (X i : UniversalRing.{0} 1)))
    (fun a b h => HomogeneousLocalization.val_injective _ (by simpa using h))

theorem a3m_chartCoordinate_ne_zero (i j : Fin (1 + 1)) : (chartCoordinate i j : a3m_A1 i) ≠ 0 := by
  have : IsDomain (ULift.{0} ℤ) :=
    Function.Injective.isDomain (ULift.ringEquiv (R := ℤ)).toRingHom ULift.ringEquiv.injective
  intro h
  have h2 := congrArg HomogeneousLocalization.val h
  rw [chartCoordinate] at h2
  erw [Away.val_mk] at h2
  rw [HomogeneousLocalization.val_zero, Localization.mk_eq_mk',
    IsLocalization.mk'_eq_zero_iff] at h2
  obtain ⟨⟨c, n, rfl⟩, hc⟩ := h2
  simp only at hc
  exact pow_ne_zero n (X_ne_zero (R := ULift.{0} ℤ) i)
    ((mul_eq_zero.1 hc).resolve_right (X_ne_zero (R := ULift.{0} ℤ) j))

/-- The generic point of a chart. -/
def a3m_botChart (i : Fin (1 + 1)) : Spec (.of (a3m_A1 i)) :=
  ⟨⊥, Ideal.isPrime_bot⟩

theorem a3m_botChart_specializes (i : Fin (1 + 1)) (q : Spec (.of (a3m_A1 i))) : a3m_botChart i ⤳ q := by
  exact (PrimeSpectrum.le_iff_specializes _ _).1 (bot_le (a := q.asIdeal))

/-- The generic point of `ℙ¹_ℤ`. -/
def a3m_η1 : g3c_P 1 := g3c_chartι 1 0 a3m_bot1

theorem a3m_η1_specializes (c : g3c_P 1) : a3m_η1 ⤳ c := by
  have h0 : ∀ q, a3m_η1 ⤳ g3c_chartι 1 0 q := fun q =>
    (a3m_botChart_specializes 0 q).map (g3c_chartι 1 0).continuous
  obtain ⟨i, q, rfl⟩ := g3c_chartι_covers 1 c
  fin_cases i
  · exact h0 q
  · have hb : g3c_chartι 1 1 (a3m_botChart 1) ∈ Set.range (g3c_chartι 1 0) := by
      change a3m_botChart 1 ∈ (g3c_chartι 1 1 ⁻¹ᵁ (g3c_chartι 1 0).opensRange : Set _)
      rw [g3c_chartι_preimage_opensRange, basicOpen_eq_of_affine]
      change chartCoordinate 1 0 ∉ (⊥ : Ideal _)
      rw [Ideal.mem_bot]
      exact a3m_chartCoordinate_ne_zero 1 0
    obtain ⟨q', hq'⟩ := hb
    exact (h0 q').trans (hq' ▸ (a3m_botChart_specializes 1 q).map (g3c_chartι 1 1).continuous)

instance a3m_P1_irreducible : IrreducibleSpace (g3c_P 1) := by
  rw [irreducibleSpace_def]
  have : closure ({a3m_η1} : Set (g3c_P 1)) = Set.univ :=
    Set.eq_univ_of_forall fun c => specializes_iff_mem_closure.1 (a3m_η1_specializes c)
  change IsIrreducible Set.univ
  rw [← this]
  exact isIrreducible_singleton.closure

/-- The cover of `ℙ¹_ℤ` by its two standard charts. -/
def a3m_P1Cover : (g3c_P 1).OpenCover :=
  Scheme.Cover.mkOfCovers (Fin (1 + 1)) (fun i => Spec (.of (a3m_A1 i))) (g3c_chartι 1)
    (fun x => by
      obtain ⟨i, q, hq⟩ := g3c_chartι_covers 1 x
      exact ⟨i, q, hq⟩)

instance a3m_P1_isReduced : IsReduced (g3c_P 1) := by
  have : ∀ i, IsReduced (a3m_P1Cover.X i) := fun i => by
    change IsReduced (Spec (.of (a3m_A1 i)))
    have := a3m_away_isDomain i
    have : _root_.IsReduced (a3m_A1 i) := isReduced_of_noZeroDivisors
    infer_instance
  exact IsReduced.of_openCover (g3c_P 1) a3m_P1Cover

instance a3m_P1_isIntegral : IsIntegral (g3c_P 1) :=
  isIntegral_of_irreducibleSpace_of_isReduced _

theorem a3m_η1_isGenericPoint : IsGenericPoint a3m_η1 (⊤ : Set (g3c_P 1)) := by
  rw [isGenericPoint_def]
  exact Set.eq_univ_of_forall fun c => specializes_iff_mem_closure.1 (a3m_η1_specializes c)

theorem a3m_genericPoint_P1 : genericPoint (g3c_P 1) = a3m_η1 :=
  (genericPoint_spec (g3c_P 1)).eq a3m_η1_isGenericPoint

/-! ## The coordinate `t = s₁/(s₁ - s₀)` -/

theorem a3m_g_mem : (X 1 - X 0 : UniversalRing.{0} 1) ∈ UniversalGrading.{0} 1 1 :=
  Submodule.sub_mem _ (isHomogeneous_X _ 1) (isHomogeneous_X _ 0)

/-- `s₁/(s₁ - s₀)` in the chart ring of `D₊(s₁ - s₀)`. -/
def a3m_tz : Away (UniversalGrading.{0} 1) (X 1 - X 0 : UniversalRing.{0} 1) :=
  Away.mk _ a3m_g_mem 1 (X 1) (by simpa using isHomogeneous_X (ULift.{0} ℤ) (1 : Fin (1 + 1)))

/-- The section `s₁/(s₁ - s₀)` of `ℙ¹_ℤ` over `D₊(s₁ - s₀)`. -/
def a3m_T0 : Γ(g3c_P 1, Proj.basicOpen (UniversalGrading.{0} 1) (X 1 - X 0)) :=
  (Proj.basicOpenIsoAway _ (X 1 - X 0) a3m_g_mem one_pos).hom a3m_tz

theorem a3m_germ_T0 (x : g3c_P 1) (hx : x ∈ Proj.basicOpen (UniversalGrading.{0} 1) (X 1 - X 0)) :
    Proj.stalkIso' _ x ((g3c_P 1).presheaf.germ _ x hx a3m_T0) =
      mapId _ (Submonoid.powers_le.mpr hx) a3m_tz := by
  exact Proj.stalkIso'_germ (𝒜 := UniversalGrading.{0} 1) _ x hx a3m_T0

theorem a3m_isUnit_germ_T0 (x : g3c_P 1)
    (hx : x ∈ Proj.basicOpen (UniversalGrading.{0} 1) (X 1 - X 0)) :
    IsUnit ((g3c_P 1).presheaf.germ _ x hx a3m_T0) ↔
      (X 1 : UniversalRing.{0} 1) ∉ x.asHomogeneousIdeal := by
  refine (MulEquiv.isUnit_map (Proj.stalkIso' (UniversalGrading.{0} 1) x).toMulEquiv).symm.trans ?_
  change IsUnit (Proj.stalkIso' _ x _) ↔ _
  rw [a3m_germ_T0, ← HomogeneousLocalization.isUnit_iff_isUnit_val]
  rw [a3m_tz, Away.mk]
  erw [HomogeneousLocalization.map_mk, HomogeneousLocalization.val_mk]
  rw [Localization.mk_eq_mk']
  erw [IsLocalization.AtPrime.isUnit_mk'_iff]
  rfl

theorem a3m_X_mem (i : Fin (1 + 1)) : (X i : UniversalRing.{0} 1) ∈ UniversalGrading.{0} 1 1 :=
  isHomogeneous_X _ i

theorem a3m_chartι_eq (i : Fin (1 + 1)) :
    g3c_chartι 1 i = Proj.awayι (UniversalGrading.{0} 1) (X i) (a3m_X_mem i) zero_lt_one := rfl

theorem a3m_mem_range_chart (i : Fin (1 + 1)) (c : g3c_P 1) :
    c ∈ Set.range (g3c_chartι 1 i) ↔ (X i : UniversalRing.{0} 1) ∉ c.asHomogeneousIdeal := by
  rw [a3m_chartι_eq]
  change c ∈ (Proj.awayι (UniversalGrading.{0} 1) (X i) (a3m_X_mem i) zero_lt_one).opensRange ↔ _
  rw [Proj.opensRange_awayι]
  rfl

theorem a3m_chart0_mem_basicOpen (q : Spec (.of a3m_Away1)) (g : UniversalRing.{0} 1)
    (hg : g ∈ UniversalGrading.{0} 1 1) :
    g3c_chartι 1 0 q ∈ Proj.basicOpen (UniversalGrading.{0} 1) g ↔
      Away.isLocalizationElem (a3m_X_mem 0) hg ∉ q.asIdeal := by
  change q ∈ (g3c_chartι 1 0 ⁻¹ᵁ Proj.basicOpen (UniversalGrading.{0} 1) g : Set _) ↔ _
  rw [a3m_chartι_eq, Proj.awayι_preimage_basicOpen _ _ _ hg one_pos]
  rfl

theorem a3m_elem_X1 : Away.isLocalizationElem (a3m_X_mem 0)
    (a3m_X_mem 1) = a3m_t₁ := by
  apply HomogeneousLocalization.val_injective
  rw [a3m_t₁, chartCoordinate]
  erw [Away.val_mk, Away.val_mk]
  simp only [pow_one]

theorem a3m_elem_g : Away.isLocalizationElem (a3m_X_mem 0)
    a3m_g_mem = a3m_t₁ - 1 := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_sub, HomogeneousLocalization.val_one, eq_sub_iff_add_eq,
    a3m_t₁, chartCoordinate]
  erw [Away.val_mk, Away.val_mk]
  rw [← Localization.mk_self (⟨X 0 ^ 1, 1, rfl⟩ : Submonoid.powers (X 0 : UniversalRing.{0} 1)),
    Localization.add_mk_self]
  simp only [pow_one, sub_add_cancel]

theorem a3m_t₁_sub_one_ne_zero : a3m_t₁ - 1 ≠ 0 := by
  rw [← a3m_elem_g]
  have : IsDomain (ULift.{0} ℤ) :=
    Function.Injective.isDomain (ULift.ringEquiv (R := ℤ)).toRingHom ULift.ringEquiv.injective
  intro h
  have h2 := congrArg HomogeneousLocalization.val h
  erw [Away.val_mk] at h2
  rw [HomogeneousLocalization.val_zero, Localization.mk_eq_mk',
    IsLocalization.mk'_eq_zero_iff] at h2
  obtain ⟨⟨c, n, rfl⟩, hc⟩ := h2
  simp only [pow_one] at hc
  refine pow_ne_zero n (X_ne_zero (R := ULift.{0} ℤ) (0 : Fin (1 + 1)))
    ((mul_eq_zero.1 hc).resolve_right ?_)
  rw [← Ne, sub_ne_zero]
  exact (X_injective (σ := Fin (1 + 1)) (R := ULift.{0} ℤ)).ne (by decide)

theorem a3m_η1_mem : a3m_η1 ∈ Proj.basicOpen (UniversalGrading.{0} 1) (X 1 - X 0) := by
  rw [a3m_η1, a3m_chart0_mem_basicOpen _ _ a3m_g_mem, a3m_elem_g]
  change a3m_t₁ - 1 ∉ (⊥ : Ideal a3m_Away1)
  rw [Ideal.mem_bot]
  exact a3m_t₁_sub_one_ne_zero

theorem a3m_X1_not_mem_η1 : (X 1 : UniversalRing.{0} 1) ∉ a3m_η1.asHomogeneousIdeal := by
  have h := (a3m_chart0_mem_basicOpen a3m_bot1 (X 1) (a3m_X_mem 1)).2
  rw [a3m_elem_X1] at h
  refine h ?_
  change a3m_t₁ ∉ (⊥ : Ideal a3m_Away1)
  rw [Ideal.mem_bot]
  exact a3m_chartCoordinate_ne_zero 0 1

theorem a3m_genericPoint_mem :
    genericPoint (g3c_P 1) ∈ Proj.basicOpen (UniversalGrading.{0} 1) (X 1 - X 0) := by
  rw [a3m_genericPoint_P1]
  exact a3m_η1_mem

/-- The coordinate `t = s₁/(s₁ - s₀)` as a rational function on `ℙ¹_ℤ`. -/
def a3m_t1 : (g3c_P 1).functionField :=
  (g3c_P 1).presheaf.germ _ (genericPoint (g3c_P 1)) a3m_genericPoint_mem a3m_T0

theorem a3m_X1_mem_or (c : g3c_P 1) :
    (X 0 : UniversalRing.{0} 1) ∉ c.asHomogeneousIdeal ∨
      (X 1 : UniversalRing.{0} 1) ∉ c.asHomogeneousIdeal := by
  obtain ⟨i, hi⟩ := g3c_chartι_covers 1 c
  rw [a3m_mem_range_chart] at hi
  fin_cases i
  · exact Or.inl hi
  · exact Or.inr hi

theorem a3m_mem_Z0 (c : g3c_P 1) (hc : c ∈ a3m_Z0) :
    (X 1 : UniversalRing.{0} 1) ∈ c.asHomogeneousIdeal ∧
      c ∈ Proj.basicOpen (UniversalGrading.{0} 1) (X 1 - X 0) := by
  obtain ⟨q, rfl, hq⟩ := hc
  have h1 : (X 1 : UniversalRing.{0} 1) ∈ (g3c_chartι 1 0 q).asHomogeneousIdeal := by
    by_contra h
    have := (a3m_chart0_mem_basicOpen q (X 1) (a3m_X_mem 1)).1 h
    rw [a3m_elem_X1] at this
    exact this hq
  have h0 : (X 0 : UniversalRing.{0} 1) ∉ (g3c_chartι 1 0 q).asHomogeneousIdeal :=
    (a3m_mem_range_chart 0 _).1 ⟨q, rfl⟩
  refine ⟨h1, fun hg => h0 ?_⟩
  have := (g3c_chartι 1 0 q).asHomogeneousIdeal.toIdeal.sub_mem h1 hg
  rwa [sub_sub_cancel] at this

theorem a3m_not_mem_Z0_Zinf (c : g3c_P 1) (h0 : c ∉ a3m_Z0) (hinf : c ∉ a3m_Zinf) :
    (X 1 : UniversalRing.{0} 1) ∉ c.asHomogeneousIdeal ∧
      c ∈ Proj.basicOpen (UniversalGrading.{0} 1) (X 1 - X 0) := by
  by_cases hc : c ∈ Set.range (g3c_chartι 1 0)
  · obtain ⟨q, rfl⟩ := hc
    constructor
    · have := (a3m_chart0_mem_basicOpen q (X 1) (a3m_X_mem 1)).2
      rw [a3m_elem_X1] at this
      exact this fun hq => h0 ⟨q, rfl, hq⟩
    · rw [a3m_chart0_mem_basicOpen q _ a3m_g_mem, a3m_elem_g]
      exact fun hq => hinf ⟨q, rfl, hq⟩
  · rw [a3m_mem_range_chart, not_not] at hc
    have h1 := (a3m_X1_mem_or c).resolve_left (not_not.2 hc)
    refine ⟨h1, fun hg => h1 ?_⟩
    have := c.asHomogeneousIdeal.toIdeal.add_mem hg hc
    rwa [sub_add_cancel] at this

theorem a3m_germ_specializes (c : g3c_P 1)
    (hc : c ∈ Proj.basicOpen (UniversalGrading.{0} 1) (X 1 - X 0)) :
    (g3c_P 1).presheaf.stalkSpecializes (genericPoint_specializes c)
      ((g3c_P 1).presheaf.germ _ c hc a3m_T0) = a3m_t1 := by
  have := congrArg (fun f => f.hom a3m_T0)
    (TopCat.Presheaf.germ_stalkSpecializes (g3c_P 1).presheaf hc (genericPoint_specializes c))
  simp only [CommRingCat.comp_apply] at this
  exact this

/-- The projective line with the coordinate `t = s₁/(s₁ - s₀)`, zeros `{t₁ = 0}` and further
non-unit locus `{t₁ = 1}`. -/
def a3m_P1curve : a3m_PointedCurve where
  C := g3c_P 1
  Z0 := a3m_Z0
  Zinf := a3m_Zinf
  t := a3m_t1
  t_ne_zero := by
    have h := a3m_X1_not_mem_η1
    rw [← a3m_genericPoint_P1] at h
    exact ((a3m_isUnit_germ_T0 _ a3m_genericPoint_mem).2 h).ne_zero
  unit c h0 hinf := by
    obtain ⟨h1, hg⟩ := a3m_not_mem_Z0_Zinf c h0 hinf
    exact ⟨_, (a3m_isUnit_germ_T0 c hg).2 h1, a3m_germ_specializes c hg⟩
  zero c hc := by
    obtain ⟨h1, hg⟩ := a3m_mem_Z0 c hc
    refine ⟨_, ?_, a3m_germ_specializes c hg⟩
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, a3m_isUnit_germ_T0 c hg, not_not]
    exact h1

end HodgeLean.Adapters
