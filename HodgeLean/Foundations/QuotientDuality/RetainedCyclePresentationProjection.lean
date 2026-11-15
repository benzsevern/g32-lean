import HodgeLean.Foundations.QuotientDuality.RetainedCyclePresentationNoether
import HodgeLean.Adapters.IntersectionProductBlochProjection

/-! Algebraic projective projections in a specified ambient embedding. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial HomogeneousLocalization
open AlgebraicGeometry.ComplexProjectiveSpace HodgeLean.Foundations HodgeLean.Adapters
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.QuotientDuality

section Glue

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
  (D : ProjectiveSpace.Presentation X.hom) {n : ℕ}
  (ℓ : Matrix (Fin (n + 1)) (Fin (D.ambientDimension + 1)) ℂ)

/-- The sections `ℓ_k / x_j` on the chart `X ∩ D₊(x_j)`, as a ring map from the homogeneous
coordinate ring of `ℙⁿ_ℤ`.
Source: Hartshorne, *Algebraic Geometry*, Theorem II.7.1. -/
def retained_presentation_sect (j : Fin (D.ambientDimension + 1)) : UniversalRing n →+* Γ(Spec ((retained_presentation_charts X D).T j), ⊤) :=
  (Scheme.ΓSpecIso ((retained_presentation_charts X D).T j)).inv.hom.comp (((retained_presentation_charts X D).θ j).comp (a3h_sub ℓ))

variable {ℓ} (hfin : ((Ideal.Quotient.mk (retained_presentation_cone_ideal X D)).comp (a3r_lin ℓ).toRingHom).Finite)
include hfin

/-- On each chart the sections `ℓ_k / x_j` generate the unit ideal. -/
theorem retained_presentation_sect_irrelevant (j : Fin (D.ambientDimension + 1)) :
    (HomogeneousIdeal.irrelevant (UniversalGrading n)).toIdeal.map (retained_presentation_sect X D ℓ j) = ⊤ := by
  have hspan : Ideal.span (Set.range fun k : Fin (n + 1) =>
      (retained_presentation_charts X D).θ j (a3r_lin ℓ (MvPolynomial.X k))) = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    let p : Spec ((retained_presentation_charts X D).T j) := ⟨M, hM.isPrime⟩
    obtain ⟨k, hk⟩ := retained_presentation_exists_notMem X D ℓ hfin ((retained_presentation_charts X D).κ j p)
    apply hk
    rw [(retained_presentation_charts X D).mem_prime_iff_of_isHomogeneous _ j p rfl _ 1 (a3r_lin_X_isHomogeneous ℓ k)]
    exact hle (Ideal.subset_span ⟨k, rfl⟩)
  rw [eq_top_iff, ← Ideal.map_top (Scheme.ΓSpecIso ((retained_presentation_charts X D).T j)).inv.hom, ← hspan,
    Ideal.map_span, Ideal.span_le]
  rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
  have hk := Ideal.mem_map_of_mem (retained_presentation_sect X D ℓ j)
    (HomogeneousIdeal.mem_irrelevant_of_mem (UniversalGrading n) zero_lt_one
      (isHomogeneous_X (ULift.{0} ℤ) k))
  simpa [retained_presentation_sect, a3h_sub_X] using hk

/-- The projection on the chart `X ∩ D₊(x_j)`. -/
def retained_presentation_chartMap (j : Fin (D.ambientDimension + 1)) : Spec ((retained_presentation_charts X D).T j) ⟶ g3c_P n :=
  Proj.fromOfGlobalSections (UniversalGrading n) (retained_presentation_sect X D ℓ j) (retained_presentation_sect_irrelevant X D hfin j)

omit hfin in
/-- The open cover of `X` by the charts `X ∩ D₊(x_j)`. -/
def retained_presentation_cover : X.left.OpenCover :=
  Scheme.Cover.mkOfCovers (Fin (D.ambientDimension + 1)) (fun j => Spec ((retained_presentation_charts X D).T j)) (retained_presentation_charts X D).κ
    (fun x => let ⟨j, y, hy⟩ := (retained_presentation_charts X D).cover x; ⟨j, y, hy⟩)

omit [IsIntegral X.left] hfin in
theorem retained_presentation_hov (a b : Fin (D.ambientDimension + 1)) (F : MvPolynomial (Fin (D.ambientDimension + 1)) ℂ) (e : ℕ)
    (hF : F.IsHomogeneous e) :
    (pullback.snd ((retained_presentation_charts X D).κ a) ((retained_presentation_charts X D).κ b)).appTop
        ((Scheme.ΓSpecIso _).inv ((retained_presentation_charts X D).θ b F)) =
      (pullback.snd ((retained_presentation_charts X D).κ a) ((retained_presentation_charts X D).κ b)).appTop
          ((Scheme.ΓSpecIso _).inv ((retained_presentation_charts X D).θ b (MvPolynomial.X a))) ^ e *
        (pullback.fst ((retained_presentation_charts X D).κ a) ((retained_presentation_charts X D).κ b)).appTop
          ((Scheme.ΓSpecIso _).inv ((retained_presentation_charts X D).θ a F)) := by
  letI : IsClosedImmersion D.immersion := D.isClosedImmersion
  exact a3m_restrict_hov (a3m_projCharts (D.ambientDimension)) (D.immersion) (a3m_Pn_hov (D.ambientDimension)) a b F e hF

/-- The chart morphisms agree on overlaps: the sections differ by the unit `x_a / x_b`. -/
theorem retained_presentation_chartMap_compat (a b : Fin (D.ambientDimension + 1)) :
    pullback.fst ((retained_presentation_charts X D).κ a) ((retained_presentation_charts X D).κ b) ≫ retained_presentation_chartMap X D hfin a =
      pullback.snd ((retained_presentation_charts X D).κ a) ((retained_presentation_charts X D).κ b) ≫ retained_presentation_chartMap X D hfin b := by
  set p₁ := pullback.fst ((retained_presentation_charts X D).κ a) ((retained_presentation_charts X D).κ b)
  set p₂ := pullback.snd ((retained_presentation_charts X D).κ a) ((retained_presentation_charts X D).κ b)
  have h₁ : (HomogeneousIdeal.irrelevant (UniversalGrading n)).toIdeal.map
      (p₁.appTop.hom.comp (retained_presentation_sect X D ℓ a)) = ⊤ := by
    rw [← Ideal.map_map, retained_presentation_sect_irrelevant X D hfin a, Ideal.map_top]
  have h₂ : (HomogeneousIdeal.irrelevant (UniversalGrading n)).toIdeal.map
      (p₂.appTop.hom.comp (retained_presentation_sect X D ℓ b)) = ⊤ := by
    rw [← Ideal.map_map, retained_presentation_sect_irrelevant X D hfin b, Ideal.map_top]
  rw [retained_presentation_chartMap, retained_presentation_chartMap, spec_g3c_comp_fromOfGlobalSections_aux _ p₁ _ _ h₁,
    spec_g3c_comp_fromOfGlobalSections_aux _ p₂ _ _ h₂]
  set u := p₂.appTop ((Scheme.ΓSpecIso _).inv ((retained_presentation_charts X D).θ b (MvPolynomial.X a)))
  set w := p₁.appTop ((Scheme.ΓSpecIso _).inv ((retained_presentation_charts X D).θ a (MvPolynomial.X b)))
  have huw : u * w = 1 := by
    have h := retained_presentation_hov X D a b (MvPolynomial.X b) 1 (isHomogeneous_X ℂ b)
    rw [(retained_presentation_charts X D).θ_X_self, map_one, map_one, pow_one] at h
    exact h.symm
  refine spec_g3c_fromOfGlobalSections_unit_twist_aux _ _ _ h₁ h₂ (Units.mkOfMulEqOne u w huw)
    fun d r hr => ?_
  rw [mem_homogeneousSubmodule] at hr
  exact retained_presentation_hov X D a b _ d (a3h_sub_isHomogeneous ℓ hr)

/-- The projection `X → ℙⁿ_ℤ`, glued from the chart morphisms. -/
def retained_presentation_π₀ : X.left ⟶ g3c_P n :=
  (retained_presentation_cover X D).glueMorphisms (retained_presentation_chartMap X D hfin) fun a b => retained_presentation_chartMap_compat X D hfin a b

theorem retained_presentation_κ_π₀ (j : Fin (D.ambientDimension + 1)) :
    (retained_presentation_charts X D).κ j ≫ retained_presentation_π₀ X D hfin = retained_presentation_chartMap X D hfin j :=
  (retained_presentation_cover X D).ι_glueMorphisms _ _ j

/-- **The linear projection `π_ℓ : X → ℙⁿ_ℂ`.**
Source: Shafarevich, *Basic Algebraic Geometry 1*, I.5.3, Theorem 1.15; Hartshorne, *Algebraic
Geometry*, Theorem II.7.1. -/
def retained_presentation_π : X.left ⟶ a3m_Pn n :=
  pullback.lift X.hom (retained_presentation_π₀ X D hfin) (terminal.hom_ext _ _)

theorem retained_presentation_π_fst : retained_presentation_π X D hfin ≫ pullback.fst _ _ = X.hom := pullback.lift_fst _ _ _

theorem retained_presentation_π_snd : retained_presentation_π X D hfin ≫ pullback.snd _ _ = retained_presentation_π₀ X D hfin := pullback.lift_snd _ _ _

end Glue

/-! ## The projection on a chart -/

section ChartFormula

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
  (D : ProjectiveSpace.Presentation X.hom) {n : ℕ}
  {ℓ : Matrix (Fin (n + 1)) (Fin (D.ambientDimension + 1)) ℂ}
  (hfin : ((Ideal.Quotient.mk (retained_presentation_cone_ideal X D)).comp (a3r_lin ℓ).toRingHom).Finite)
  (j : Fin (D.ambientDimension + 1)) (i : Fin (n + 1))

omit [IsIntegral X.left] in
/-- The structure map of `X` on the chart `X ∩ D₊(x_j)` is `Spec` of `ℂ → T_j`. -/
theorem retained_presentation_κ_hom : (retained_presentation_charts X D).κ j ≫ X.hom =
    Spec.map (CommRingCat.ofHom (((retained_presentation_charts X D).θ j).comp MvPolynomial.C)) := by
  letI : IsClosedImmersion D.immersion := D.isClosedImmersion
  have h1 : X.hom = D.immersion ≫ pullback.fst (terminal.from (Spec ↧ℂ))
      (terminal.from (g3c_P (D.ambientDimension))) :=
    (D).immersion_toBase.symm
  have h2 : (retained_presentation_charts X D).κ j ≫ D.immersion =
      @CategoryStruct.comp _ _ (Spec ((retained_presentation_charts X D).T j)) _ _
        (Spec.map (a3m_restrictHom (a3m_projCharts (D.ambientDimension)) (D.immersion) j))
        ((a3m_projCharts (D.ambientDimension)).κ j) :=
    a3m_restrict_κ_comp _ _ j
  have h3 : (a3m_projCharts (D.ambientDimension)).κ j ≫ pullback.fst (terminal.from (Spec ↧ℂ))
      (terminal.from (g3c_P (D.ambientDimension))) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := ℂ)
        (B := HomogeneousLocalization.Away (UniversalGrading (D.ambientDimension))
          (MvPolynomial.X j : UniversalRing (D.ambientDimension))))) :=
    (a3m_prodChart_fst _ _).trans (Category.comp_id _)
  have h4 := congrArg (fun f => (retained_presentation_charts X D).κ j ≫ f) h1
  rw [← Category.assoc, h2, Category.assoc, h3] at h4
  refine h4.trans ?_
  erw [← Spec.map_comp]
  congr 1
  ext c
  change (a3m_restrictHom (a3m_projCharts (D.ambientDimension)) (D.immersion) j).hom
      (Algebra.TensorProduct.includeLeftRingHom c) =
    (a3m_restrictHom (a3m_projCharts (D.ambientDimension)) (D.immersion) j).hom (a3m_Pnθ (D.ambientDimension) j (C c))
  rw [a3m_Pnθ, coe_eval₂Hom, eval₂_C]

variable (ℓ) in
/-- The value `s = ℓ_i / x_j` on the chart `j`. -/
abbrev retained_presentation_s : (retained_presentation_charts X D).T j := (retained_presentation_charts X D).θ j (a3r_lin ℓ (MvPolynomial.X i))

variable (ℓ) in
/-- The chart ring localized at `s = ℓ_i / x_j`. -/
abbrev retained_presentation_Rs : CommRingCat.{0} := .of (Localization.Away (retained_presentation_s X D ℓ j i))

variable (ℓ) in
/-- The open `D(ℓ_i / x_j)` of the chart `j`. -/
def retained_presentation_ιs : Spec (retained_presentation_Rs X D ℓ j i) ⟶ Spec ((retained_presentation_charts X D).T j) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap ((retained_presentation_charts X D).T j) (Localization.Away (retained_presentation_s X D ℓ j i))))

variable (ℓ) in
/-- The sections `ℓ_k / x_j` on `D(ℓ_i / x_j)`. -/
def retained_presentation_g : UniversalRing n →+* Γ(Spec (retained_presentation_Rs X D ℓ j i), ⊤) :=
  (retained_presentation_ιs X D ℓ j i).appTop.hom.comp (retained_presentation_sect X D ℓ j)

omit [IsIntegral X.left] in
theorem retained_presentation_g_apply (r : UniversalRing n) :
    retained_presentation_g X D ℓ j i r = (Scheme.ΓSpecIso (retained_presentation_Rs X D ℓ j i)).inv.hom
      (algebraMap ((retained_presentation_charts X D).T j) (Localization.Away (retained_presentation_s X D ℓ j i))
        ((retained_presentation_charts X D).θ j (a3h_sub ℓ r))) := by
  rw [retained_presentation_g, RingHom.comp_apply, retained_presentation_sect, RingHom.comp_apply, retained_presentation_ιs]
  erw [g3c_SpecMap_appTop_ΓSpecIso_inv]
  rfl

omit [IsIntegral X.left] in
theorem retained_presentation_g_isUnit : IsUnit (retained_presentation_g X D ℓ j i (MvPolynomial.X i)) := by
  rw [retained_presentation_g_apply, a3h_sub_X]
  exact (IsLocalization.Away.algebraMap_isUnit _).map _

variable (ℓ) in
/-- The ring map `ℤ[y / y_i] → T_j[1/s]`, `y_k / y_i ↦ ℓ_k / ℓ_i`. -/
def retained_presentation_β : HomogeneousLocalization.Away (UniversalGrading n) (MvPolynomial.X i) →+*
    Localization.Away (retained_presentation_s X D ℓ j i) :=
  (Scheme.ΓSpecIso (retained_presentation_Rs X D ℓ j i)).hom.hom.comp
    (a3h_awayLift (UniversalGrading n) (retained_presentation_g X D ℓ j i) (retained_presentation_g_isUnit X D j i))

theorem retained_presentation_ιs_chartMap : retained_presentation_ιs X D ℓ j i ≫ retained_presentation_chartMap X D hfin j =
    Spec.map (CommRingCat.ofHom (retained_presentation_β X D ℓ j i)) ≫ g3c_chartι n i := by
  have h' : (HomogeneousIdeal.irrelevant (UniversalGrading n)).toIdeal.map
      ((retained_presentation_ιs X D ℓ j i).appTop.hom.comp (retained_presentation_sect X D ℓ j)) = ⊤ := by
    rw [← Ideal.map_map, retained_presentation_sect_irrelevant X D hfin j, Ideal.map_top]
  rw [retained_presentation_chartMap, spec_g3c_comp_fromOfGlobalSections_aux _ _ _ _ h']
  rw [a3h_fromOf_eq (UniversalGrading n) _ h' zero_lt_one (isHomogeneous_X (ULift.{0} ℤ) i)
    (retained_presentation_g_isUnit X D j i), ← SpecMap_ΓSpecIso_hom, ← Category.assoc, ← Spec.map_comp]
  rfl

variable (ℓ) in
/-- The ring map `ℂ ⊗ ℤ[y / y_i] → T_j[1/s]` of the projection on `D(ℓ_i / x_j)`. -/
def retained_presentation_ψ : a3m_PnT n i →+* Localization.Away (retained_presentation_s X D ℓ j i) :=
  letI : Algebra ℤ (Localization.Away (retained_presentation_s X D ℓ j i)) := Ring.toIntAlgebra _
  (Algebra.TensorProduct.productMap
    ((algebraMap ((retained_presentation_charts X D).T j) (Localization.Away (retained_presentation_s X D ℓ j i))).comp
      (((retained_presentation_charts X D).θ j).comp MvPolynomial.C)).toIntAlgHom
    (retained_presentation_β X D ℓ j i).toIntAlgHom).toRingHom

/-- **The projection on a chart**: on `D(ℓ_i / x_j) ⊆ X ∩ D₊(x_j)`, `π_ℓ` is `Spec` of `retained_presentation_ψ`
followed by the chart `D₊(y_i)` of `ℙⁿ_ℂ`. -/
theorem retained_presentation_chart : Spec.map (CommRingCat.ofHom (retained_presentation_ψ X D ℓ j i)) ≫ a3m_Pnκ n i =
    retained_presentation_ιs X D ℓ j i ≫ (retained_presentation_charts X D).κ j ≫ retained_presentation_π X D hfin := by
  apply pullback.hom_ext
  · simp only [Category.assoc]
    rw [retained_presentation_π_fst, retained_presentation_κ_hom, a3m_Pnκ, a3m_prodChart_fst,
      Category.comp_id, retained_presentation_ιs]
    erw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext c
    simp [retained_presentation_ψ, Algebra.TensorProduct.productMap_apply_tmul]
  · simp only [Category.assoc]
    rw [retained_presentation_π_snd, retained_presentation_κ_π₀ X D hfin j, retained_presentation_ιs_chartMap, a3m_Pnκ,
      a3m_prodChart_snd, ← Category.assoc, ← Spec.map_comp]
    congr 2
    ext b
    simp [retained_presentation_ψ, Algebra.TensorProduct.productMap_apply_tmul]

omit [IsIntegral X.left] in
/-- On `D(ℓ_i / x_j)`, `ψ` sends the dehomogenization `G(y / y_i)` of a form `G` of degree `e` to
`G(ℓ) / ℓ_i^e`. -/
theorem retained_presentation_ψ_θ (G : MvPolynomial (Fin (n + 1)) ℂ) (e : ℕ) (hG : G.IsHomogeneous e) :
    algebraMap ((retained_presentation_charts X D).T j) (Localization.Away (retained_presentation_s X D ℓ j i))
        ((retained_presentation_charts X D).θ j (a3r_lin ℓ G)) =
      algebraMap ((retained_presentation_charts X D).T j) (Localization.Away (retained_presentation_s X D ℓ j i)) (retained_presentation_s X D ℓ j i) ^ e *
        retained_presentation_ψ X D ℓ j i (a3m_Pnθ n i G) := by
  let φ₁ : MvPolynomial (Fin (n + 1)) ℂ →+* Localization.Away (retained_presentation_s X D ℓ j i) :=
    (algebraMap ((retained_presentation_charts X D).T j) _).comp (((retained_presentation_charts X D).θ j).comp (a3r_lin ℓ).toRingHom)
  let φ₂ : MvPolynomial (Fin (n + 1)) ℂ →+* Localization.Away (retained_presentation_s X D ℓ j i) :=
    (retained_presentation_ψ X D ℓ j i).comp (a3m_Pnθ n i)
  have hC : ∀ c, φ₁ (C c) = φ₂ (C c) := by
    intro c
    simp [φ₁, φ₂, a3m_Pnθ, retained_presentation_ψ, Algebra.TensorProduct.productMap_apply_tmul]
  have hΓ : ∀ r, (Scheme.ΓSpecIso (retained_presentation_Rs X D ℓ j i)).hom.hom (retained_presentation_g X D ℓ j i r) =
      algebraMap ((retained_presentation_charts X D).T j) (Localization.Away (retained_presentation_s X D ℓ j i))
        ((retained_presentation_charts X D).θ j (a3h_sub ℓ r)) := by
    intro r
    rw [retained_presentation_g_apply]
    exact Iso.inv_hom_id_apply (Scheme.ΓSpecIso (retained_presentation_Rs X D ℓ j i)) _
  have hX : ∀ k, φ₁ (MvPolynomial.X k) =
      algebraMap ((retained_presentation_charts X D).T j) _ (retained_presentation_s X D ℓ j i) * φ₂ (MvPolynomial.X k) := by
    intro k
    have h := a3h_awayLift_mk (UniversalGrading n) (retained_presentation_g X D ℓ j i) (retained_presentation_g_isUnit X D j i)
      (isHomogeneous_X (ULift.{0} ℤ) i) 1 (MvPolynomial.X k)
      (by simpa using isHomogeneous_X (ULift.{0} ℤ) k)
    have h' := congrArg (Scheme.ΓSpecIso (retained_presentation_Rs X D ℓ j i)).hom.hom h
    rw [map_mul, map_pow, pow_one, hΓ, hΓ, a3h_sub_X, a3h_sub_X] at h'
    simp only [φ₁, φ₂, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, a3m_Pnθ,
      coe_eval₂Hom, eval₂_X]
    rw [← h']
    simp [retained_presentation_ψ, retained_presentation_β, Algebra.TensorProduct.productMap_apply_tmul, chartCoordinate]
  exact a3m_twist φ₁ φ₂ _ hC hX G e hG

/-- **The point formula**: the homogeneous prime of `π_ℓ(x)` is the pull-back of that of `x` along
`y ↦ ℓ`. -/
theorem retained_presentation_prime_π (x : X.left) :
    (a3m_projCharts n).prime (retained_presentation_π X D hfin x) = ((retained_presentation_charts X D).prime x).comap (a3r_lin ℓ) := by
  obtain ⟨j, p, hp⟩ := (retained_presentation_charts X D).cover x
  obtain ⟨i, hi⟩ := retained_presentation_exists_notMem X D ℓ hfin x
  have hs : retained_presentation_s X D ℓ j i ∉ p.asIdeal := by
    rwa [← (retained_presentation_charts X D).mem_prime_iff_of_isHomogeneous x j p hp _ 1
      (a3r_lin_X_isHomogeneous ℓ i)]
  obtain ⟨p', hp'⟩ : ∃ p' : Spec (retained_presentation_Rs X D ℓ j i),
      PrimeSpectrum.comap (algebraMap ((retained_presentation_charts X D).T j) (Localization.Away (retained_presentation_s X D ℓ j i))) p' =
        p :=
    (PrimeSpectrum.localization_away_comap_range (Localization.Away (retained_presentation_s X D ℓ j i))
      (retained_presentation_s X D ℓ j i)).ge ((PrimeSpectrum.mem_basicOpen _ _).2 hs)
  have hq : a3m_Pnκ n i (Spec.map (CommRingCat.ofHom (retained_presentation_ψ X D ℓ j i)) p') = retained_presentation_π X D hfin x := by
    rw [← Scheme.Hom.comp_apply, retained_presentation_chart X D hfin j i, Scheme.Hom.comp_apply,
      Scheme.Hom.comp_apply, ← hp, ← hp']
    rfl
  ext G
  rw [(a3m_projCharts n).mem_prime_iff _ i _ hq, Ideal.mem_comap,
    (retained_presentation_charts X D).mem_prime_iff x j p hp]
  refine forall_congr' fun e => ?_
  rw [a3h_lin_homogeneousComponent]
  have key := retained_presentation_ψ_θ X D (ℓ := ℓ) j i (homogeneousComponent e G) e (homogeneousComponent_isHomogeneous e G)
  have hu : IsUnit (algebraMap ((retained_presentation_charts X D).T j) (Localization.Away (retained_presentation_s X D ℓ j i))
      (retained_presentation_s X D ℓ j i) ^ e) := (IsLocalization.Away.algebraMap_isUnit _).pow e
  change retained_presentation_ψ X D ℓ j i (a3m_Pnθ n i (homogeneousComponent e G)) ∈ p'.asIdeal ↔
    (retained_presentation_charts X D).θ j (a3r_lin ℓ (homogeneousComponent e G)) ∈ p.asIdeal
  rw [← hp']
  change _ ↔ algebraMap ((retained_presentation_charts X D).T j) (Localization.Away (retained_presentation_s X D ℓ j i))
    ((retained_presentation_charts X D).θ j (a3r_lin ℓ (homogeneousComponent e G))) ∈ p'.asIdeal
  rw [key, mul_comm, Ideal.mul_unit_mem_iff_mem _ hu]

end ChartFormula

/-! ## The projection is finite and surjective -/

section FiniteSurjective

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
  (D : ProjectiveSpace.Presentation X.hom) {n : ℕ}
  {ℓ : Matrix (Fin (n + 1)) (Fin (D.ambientDimension + 1)) ℂ}
  (hfin : ((Ideal.Quotient.mk (retained_presentation_cone_ideal X D)).comp (a3r_lin ℓ).toRingHom).Finite)

instance retained_presentation_π_isProper : IsProper (retained_presentation_π X D hfin) := by
  have : IsProper (retained_presentation_π X D hfin ≫ pullback.fst (terminal.from (Spec ↧ℂ))
      (terminal.from (g3c_P n))) := by
    rw [retained_presentation_π_fst]; infer_instance
  have : IsSeparated (pullback.fst (terminal.from (Spec ↧ℂ)) (terminal.from (g3c_P n))) :=
    (ProjectiveSpace.toBaseProper (Fin (n + 1)) (Spec ↧ℂ)).toIsSeparated
  exact IsProper.of_comp _ (pullback.fst (terminal.from (Spec ↧ℂ)) (terminal.from (g3c_P n)))

/-- The point of `Spec (ℂ[x]/I_X)` of a point of `X`. -/
def retained_presentation_ptS (x : X.left) : PrimeSpectrum (MvPolynomial (Fin (D.ambientDimension + 1)) ℂ ⧸ retained_presentation_cone_ideal X D) :=
  ⟨((retained_presentation_charts X D).prime x).map (Ideal.Quotient.mk (retained_presentation_cone_ideal X D)),
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by
      rw [Ideal.mk_ker]; exact (fun x => (retained_presentation_charts X D).prime_mono (genericPoint_specializes x)) x)⟩

omit [IsProjective X.hom] in
theorem retained_presentation_comap_ptS [IsProjective X.hom] (x : X.left) :
    ((retained_presentation_ptS X D x).asIdeal).comap (Ideal.Quotient.mk (retained_presentation_cone_ideal X D)) = (retained_presentation_charts X D).prime x := by
  rw [retained_presentation_ptS, Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker,
    sup_eq_left.2 ((fun x => (retained_presentation_charts X D).prime_mono (genericPoint_specializes x)) x)]

/-- The fibres of `π_ℓ` are finite: the points over `y` give distinct primes of the finite
`ℂ[y]`-algebra `ℂ[x]/I_X` over the prime of `y`.
Source: Atiyah–Macdonald, *Introduction to Commutative Algebra*, Corollary 5.9 (primes over a
prime in an integral extension are incomparable); Mathlib,
`Algebra.QuasiFinite.finite_comap_preimage_singleton`. -/
theorem retained_presentation_finite_fibre (y : a3m_Pn n) : (retained_presentation_π X D hfin ⁻¹' {y}).Finite := by
  let alg : Algebra (MvPolynomial (Fin (n + 1)) ℂ)
      (MvPolynomial (Fin (D.ambientDimension + 1)) ℂ ⧸ retained_presentation_cone_ideal X D) :=
    ((Ideal.Quotient.mk (retained_presentation_cone_ideal X D)).comp (a3r_lin ℓ).toRingHom).toAlgebra
  have hmod : @Module.Finite (MvPolynomial (Fin (n + 1)) ℂ)
      (MvPolynomial (Fin (D.ambientDimension + 1)) ℂ ⧸ retained_presentation_cone_ideal X D) _ _ alg.toModule := hfin
  have hqf : @Algebra.QuasiFinite (MvPolynomial (Fin (n + 1)) ℂ)
      (MvPolynomial (Fin (D.ambientDimension + 1)) ℂ ⧸ retained_presentation_cone_ideal X D) _ _ alg :=
    @Algebra.QuasiFinite.instOfFinite _ _ _ _ alg hmod
  let P₀ : PrimeSpectrum (MvPolynomial (Fin (n + 1)) ℂ) := ⟨(a3m_projCharts n).prime y, inferInstance⟩
  have hF := @Algebra.QuasiFinite.finite_comap_preimage_singleton
    (MvPolynomial (Fin (n + 1)) ℂ) (MvPolynomial (Fin (D.ambientDimension + 1)) ℂ ⧸ retained_presentation_cone_ideal X D) _ _ alg hqf P₀
  refine Set.Finite.of_finite_image (f := retained_presentation_ptS X D) (hF.subset ?_) fun x _ x' _ hxx' => ?_
  · rintro _ ⟨x, hx, rfl⟩
    rw [Set.mem_preimage, Set.mem_singleton_iff]
    ext1
    change Ideal.comap (((Ideal.Quotient.mk (retained_presentation_cone_ideal X D)).comp (a3r_lin ℓ).toRingHom))
      (retained_presentation_ptS X D x).asIdeal = (a3m_projCharts n).prime y
    rw [← Ideal.comap_comap, retained_presentation_comap_ptS]
    have h := retained_presentation_prime_π X D hfin x
    rw [Set.mem_singleton_iff.1 hx] at h
    exact h.symm
  · have h := congrArg (fun P : PrimeSpectrum _ => P.asIdeal.comap (Ideal.Quotient.mk (retained_presentation_cone_ideal X D)))
      hxx'
    simp only [retained_presentation_comap_ptS] at h
    exact (retained_presentation_charts X D).prime_injective h

instance retained_presentation_π_locallyQuasiFinite : LocallyQuasiFinite (retained_presentation_π X D hfin) :=
  (locallyQuasiFinite_iff_finite_preimage_singleton).2 (retained_presentation_finite_fibre X D hfin)

/-- **The projection is finite.**
Source: Stacks Project, Tag 02LS (proper and quasi-finite morphisms are finite); Shafarevich,
*Basic Algebraic Geometry 1*, I.5.3, Theorem 1.15. -/
instance retained_presentation_π_isFinite : IsFinite (retained_presentation_π X D hfin) :=
  IsFinite.of_isProper_of_locallyQuasiFinite _

include hfin in
/-- The forms `ℓ_0, …, ℓ_n` are algebraically independent modulo `I_X`: the kernel of
`ℂ[y] → ℂ[x]/I_X` is zero, by the dimension count. -/
theorem retained_presentation_comap_IX (hdim : ringKrullDim (MvPolynomial (Fin (D.ambientDimension + 1)) ℂ ⧸ retained_presentation_cone_ideal X D) =
    (n + 1 : ℕ)) : (retained_presentation_cone_ideal X D).comap (a3r_lin ℓ) = ⊥ := by
  by_contra hne
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hd := a3r_dim_eq_of_finite (retained_presentation_cone_ideal X D) ℓ hfin (retained_presentation_cone_ideal X D) le_rfl
  have hR : ringKrullDim (MvPolynomial (Fin (n + 1)) ℂ) = (n + 1 : ℕ) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
      ENat.card_eq_coe_fintype_card]
    simp
  have h1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (R := MvPolynomial (Fin (n + 1)) ℂ)
    (mem_nonZeroDivisors_of_ne_zero hr0)
  have h2 : ringKrullDim (MvPolynomial (Fin (n + 1)) ℂ ⧸ (retained_presentation_cone_ideal X D).comap (a3r_lin ℓ)) ≤
      ringKrullDim (MvPolynomial (Fin (n + 1)) ℂ ⧸ Ideal.span {r}) :=
    ringKrullDim_le_of_surjective (Ideal.Quotient.factor (Ideal.span_le.2
      (Set.singleton_subset_iff.2 hr))) (Ideal.Quotient.factor_surjective _)
  have h3 : ringKrullDim (MvPolynomial (Fin (n + 1)) ℂ ⧸ (retained_presentation_cone_ideal X D).comap (a3r_lin ℓ)) + 1 ≤
      ringKrullDim (MvPolynomial (Fin (n + 1)) ℂ) := le_trans (by gcongr) h1
  rw [← hd, hdim, hR] at h3
  exact absurd h3 (by norm_cast; omega)

/-- **The projection is surjective**: a relevant homogeneous prime `Q` of `ℂ[y]` has a prime of
`ℂ[x]/I_X` over it (lying over, `ℂ[y] ⊆ ℂ[x]/I_X` being integral), whose homogeneous core is a
relevant homogeneous prime over `Q`, the prime of a point of `X`.
Source: Atiyah–Macdonald, *Introduction to Commutative Algebra*, Theorem 5.10 (lying over);
Shafarevich, *Basic Algebraic Geometry 1*, I.5.3, Theorem 1.15. -/
theorem retained_presentation_π_surjective (hdim : ringKrullDim (MvPolynomial (Fin (D.ambientDimension + 1)) ℂ ⧸ retained_presentation_cone_ideal X D) =
    (n + 1 : ℕ)) : Function.Surjective (retained_presentation_π X D hfin) := by
  intro y
  set Q := (a3m_projCharts n).prime y
  let _ : Algebra (MvPolynomial (Fin (n + 1)) ℂ) (MvPolynomial (Fin (D.ambientDimension + 1)) ℂ ⧸ retained_presentation_cone_ideal X D) :=
    ((Ideal.Quotient.mk (retained_presentation_cone_ideal X D)).comp (a3r_lin ℓ).toRingHom).toAlgebra
  have : Algebra.IsIntegral (MvPolynomial (Fin (n + 1)) ℂ)
      (MvPolynomial (Fin (D.ambientDimension + 1)) ℂ ⧸ retained_presentation_cone_ideal X D) := ⟨hfin.to_isIntegral⟩
  obtain ⟨P', -, hP', hP'Q⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S :=
    MvPolynomial (Fin (D.ambientDimension + 1)) ℂ ⧸ retained_presentation_cone_ideal X D) Q ⊥ (by
      intro r hr
      have : r ∈ (retained_presentation_cone_ideal X D).comap (a3r_lin ℓ) := by
        change (Ideal.Quotient.mk (retained_presentation_cone_ideal X D)) (a3r_lin ℓ r) ∈ (⊥ : Ideal _) at hr
        rw [Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at hr
        exact hr
      rw [retained_presentation_comap_IX X D hfin hdim, Ideal.mem_bot] at this
      rw [this]; exact zero_mem _)
  set P := P'.comap (Ideal.Quotient.mk (retained_presentation_cone_ideal X D))
  have hPprime : P.IsPrime := Ideal.comap_isPrime _ _
  have hIXP : retained_presentation_cone_ideal X D ≤ P := fun F hF => by
    change Ideal.Quotient.mk _ F ∈ P'
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hF]; exact zero_mem _
  have hPQ : P.comap (a3r_lin ℓ) = Q := hP'Q
  set P₀ := (P.homogeneousCore (homogeneousSubmodule (Fin (D.ambientDimension + 1)) ℂ)).toIdeal
  have hP₀prime : P₀.IsPrime := hPprime.homogeneousCore
  have hP₀h : P₀.IsHomogeneous (homogeneousSubmodule (Fin (D.ambientDimension + 1)) ℂ) :=
    (P.homogeneousCore _).isHomogeneous
  have hP₀le : P₀ ≤ P := Ideal.toIdeal_homogeneousCore_le _ _
  have hIXP₀ : retained_presentation_cone_ideal X D ≤ P₀ := fun F hF => by
    rw [← sum_homogeneousComponent F]
    exact Ideal.sum_mem _ fun e _ => Ideal.mem_homogeneousCore_of_homogeneous_of_mem
      ⟨e, (mem_homogeneousSubmodule _ _).2 (homogeneousComponent_isHomogeneous e F)⟩
      (hIXP (homogeneousComponent_mem_of_mem (retained_presentation_cone_homogeneous X D) hF e))
  have hQh : Q.IsHomogeneous (homogeneousSubmodule (Fin (n + 1)) ℂ) :=
    (a3m_projCharts n).isHomogeneous_prime y
  have hcomap : P₀.comap (a3r_lin ℓ) = Q := by
    refine le_antisymm (hPQ ▸ Ideal.comap_mono hP₀le) fun G hG => ?_
    rw [Ideal.mem_comap, ← sum_homogeneousComponent G, map_sum]
    refine Ideal.sum_mem _ fun e _ => Ideal.mem_homogeneousCore_of_homogeneous_of_mem
      ⟨e, (mem_homogeneousSubmodule _ _).2
        (a3h_lin_isHomogeneous ℓ (homogeneousComponent_isHomogeneous e G))⟩ ?_
    rw [← Ideal.mem_comap, hPQ]
    exact homogeneousComponent_mem_of_mem hQh hG e
  obtain ⟨i, hi⟩ := (a3m_projCharts n).cover y
  obtain ⟨k, hk⟩ : ∃ k, MvPolynomial.X k ∉ P₀ := by
    by_contra hall
    push Not at hall
    apply ((a3m_projCharts n).X_mem_prime_iff y i).1 _ hi
    have h : MvPolynomial.X i ∈ P₀.comap (a3r_lin ℓ) := by
      rw [Ideal.mem_comap, a3r_lin_X]
      exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (hall k)
    rw [hcomap] at h
    exact h
  obtain ⟨x, hx⟩ := (retained_presentation_charts X D).exists_prime_eq P₀ hP₀h k hk hIXP₀
  refine ⟨x, (a3m_projCharts n).prime_injective ?_⟩
  rw [retained_presentation_prime_π X D hfin x, hx, hcomap]

end FiniteSurjective

end HodgeLean.Foundations.QuotientDuality
