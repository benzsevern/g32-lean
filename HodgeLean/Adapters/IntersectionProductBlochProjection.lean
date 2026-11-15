import HodgeLean.Adapters.IntersectionProductMovingRobertsScheme
import HodgeLean.Foundations.SegreProjectiveProofs

/-! # A general linear projection `X → ℙⁿ`: projective Noether normalization

Stage A3.3, the first input of Bloch's homotopy. For an integral projective `X ⊂ ℙᴺ` over `ℂ`
whose affine cone has dimension `n + 1`, and a linear map `ℓ : ℂ^{N+1} → ℂ^{n+1}` for which
`ℂ[x]/I_X` is finite over `ℂ[ℓ_0, …, ℓ_n]` (a generic `ℓ`, `a3r_generic_finite`), the forms
`ℓ_0, …, ℓ_n` have no common zero on `X` (`a3h_exists_notMem`). On the chart `X ∩ D₊(x_j)` the
sections `ℓ_k / x_j` generate the unit ideal, so they define a morphism to `ℙⁿ_ℤ`
(`Proj.fromOfGlobalSections`); on overlaps the two systems of sections differ by the unit
`x_j / x_l`, so the chart morphisms glue (`spec_g3c_comp_fromOfGlobalSections`,
`spec_g3c_fromOfGlobalSections_unit_twist`) to the projection `π_ℓ : X → ℙⁿ_ℂ` (`a3h_π`).

Source: Shafarevich, *Basic Algebraic Geometry 1*, I.5.3, Theorem 1.15 (finite projections) and
II.4.1; Hartshorne, *Algebraic Geometry*, Theorem II.7.1 (morphisms to projective space from
generating sections) and Exercise II.3.5; J. Roberts, *Chow's moving lemma* (1972), §1; S. Bloch,
*The moving lemma for higher Chow groups*, J. Algebraic Geom. 3 (1994), §2.
HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
open AlgebraicGeometry.ComplexProjectiveSpace HodgeLean.Foundations

namespace HodgeLean.Adapters

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ## The substitution `y_k ↦ ℓ_k` on integral polynomials -/

section Substitution

variable {σ : Type} [Fintype σ] {n : ℕ}

/-- The coefficient map `ℤ → ℂ` on the coefficients of `ℙⁿ_ℤ`. -/
def a3h_base : ULift.{0} ℤ →+* ℂ := (Int.castRingHom ℂ).comp ULift.ringEquiv.toRingHom

/-- The linear substitution `y_k ↦ ℓ_k = Σ_m ℓ_{km} x_m` from the homogeneous coordinate ring of
`ℙⁿ_ℤ` to `ℂ[x]`.
Source: Shafarevich, *Basic Algebraic Geometry 1*, I.4.4 (projections). -/
def a3h_sub (ℓ : Matrix (Fin (n + 1)) σ ℂ) : UniversalRing n →+* MvPolynomial σ ℂ :=
  (a3r_lin ℓ).toRingHom.comp (MvPolynomial.map a3h_base)

theorem a3h_sub_X (ℓ : Matrix (Fin (n + 1)) σ ℂ) (k : Fin (n + 1)) :
    a3h_sub ℓ (X k) = a3r_lin ℓ (X k) := by
  simp [a3h_sub]

theorem a3h_sub_C (ℓ : Matrix (Fin (n + 1)) σ ℂ) (c : ULift.{0} ℤ) :
    a3h_sub ℓ (C c) = C (a3h_base c) := by
  simp [a3h_sub]

theorem a3h_sub_isHomogeneous (ℓ : Matrix (Fin (n + 1)) σ ℂ) {r : UniversalRing n} {d : ℕ}
    (hr : r.IsHomogeneous d) : (a3h_sub ℓ r).IsHomogeneous d := by
  have h := (hr.map a3h_base).aeval (S := ℂ) (fun i => ∑ k, C (ℓ i k) * X k)
    (fun i => IsHomogeneous.sum _ _ _ fun k _ => isHomogeneous_C_mul_X _ _)
  rw [one_mul] at h
  exact h

omit [Fintype σ] in
theorem a3h_lin_isHomogeneous {ρ : Type} (ℓ : Matrix ρ σ ℂ) [Fintype σ] {G : MvPolynomial ρ ℂ}
    {d : ℕ} (hG : G.IsHomogeneous d) : (a3r_lin ℓ G).IsHomogeneous d := by
  have h := hG.aeval (S := ℂ) (fun i => ∑ k, C (ℓ i k) * X k)
    (fun i => IsHomogeneous.sum _ _ _ fun k _ => isHomogeneous_C_mul_X _ _)
  rw [one_mul] at h
  exact h

/-- The linear substitution respects homogeneous components. -/
theorem a3h_lin_homogeneousComponent {ρ : Type} (ℓ : Matrix ρ σ ℂ) (G : MvPolynomial ρ ℂ)
    (e : ℕ) : homogeneousComponent e (a3r_lin ℓ G) = a3r_lin ℓ (homogeneousComponent e G) := by
  classical
  conv_lhs => rw [← sum_homogeneousComponent G]
  rw [map_sum, map_sum]
  simp_rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).2
    (a3h_lin_isHomogeneous ℓ (homogeneousComponent_isHomogeneous _ G)))]
  rw [Finset.sum_ite_eq]
  split_ifs with he
  · rfl
  · rw [homogeneousComponent_eq_zero, map_zero]
    simp only [Finset.mem_range, not_lt] at he
    omega

end Substitution

/-! ## The centre of a finite projection misses `X` -/

section Centre

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom] {n : ℕ}

/-- If `ℂ[x]/I_X` is finite over `ℂ[ℓ]`, the forms `ℓ_0, …, ℓ_n` have no common zero on `X`:
otherwise a point of `X` would have a cone of dimension `0` over the vertex of `ℂ[y]`.
Source: Shafarevich, *Basic Algebraic Geometry 1*, I.5.3, Theorem 1.15. -/
theorem a3h_exists_notMem (ℓ : Matrix (Fin (n + 1)) (Fin (a3s_N X + 1)) ℂ)
    (hfin : ((Ideal.Quotient.mk (a3s_IX X)).comp (a3r_lin ℓ).toRingHom).Finite) (x : X.left) :
    ∃ k, a3r_lin ℓ (MvPolynomial.X k) ∉ (a3s_CX X).prime x := by
  by_contra hall
  push Not at hall
  set P := (a3s_CX X).prime x
  have hdim := a3r_dim_eq_of_finite (a3s_IX X) ℓ hfin P (a3s_IX_le X x)
  set K := RingHom.ker (constantCoeff : MvPolynomial (Fin (n + 1)) ℂ →+* ℂ)
  have hK : K.IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ fun z => ⟨C z, constantCoeff_C _ z⟩
  have hKle : K ≤ P.comap (a3r_lin ℓ) := by
    intro F hF
    have hF' : F ∈ Ideal.span (MvPolynomial.X '' (Set.univ : Set (Fin (n + 1))) :
        Set (MvPolynomial (Fin (n + 1)) ℂ)) := by
      rw [mem_ideal_span_X_image]
      intro m hm
      by_contra h0
      push Not at h0
      have hm0 : m = 0 := Finsupp.ext fun i => h0 i trivial
      rw [hm0, MvPolynomial.mem_support_iff, ← constantCoeff_eq] at hm
      exact hm (RingHom.mem_ker.1 hF)
    refine (Ideal.span_le.2 ?_) hF'
    rintro _ ⟨k, -, rfl⟩
    exact hall k
  have hcomapPrime : (P.comap (a3r_lin ℓ)).IsPrime := Ideal.comap_isPrime _ _
  have heq : P.comap (a3r_lin ℓ) = K := (hK.eq_of_le hcomapPrime.ne_top hKle).symm
  have h0 : ringKrullDim (MvPolynomial (Fin (n + 1)) ℂ ⧸ P.comap (a3r_lin ℓ)) = 0 := by
    rw [heq]
    exact ringKrullDim_eq_zero_of_isField ((Ideal.Quotient.maximal_ideal_iff_isField_quotient K).1 hK)
  obtain ⟨j, hj⟩ := a3s_relevant X x
  have h1 := a3r_one_le_dim P ((a3s_CX X).isHomogeneous_prime x) j hj
  rw [hdim, h0] at h1
  exact absurd h1 (by decide)

end Centre

/-! ## `Proj.fromOfGlobalSections` where a section is a unit -/

section AwayUnit

universe u

variable {σ' : Type*} {A : Type u} [CommRing A] [SetLike σ' A] [AddSubgroupClass σ' A]
  (𝒜 : ℕ → σ') [GradedRing 𝒜]

/-- The ring map `(A_t)₀ → Γ(X)` of sections `f : A → Γ(X)` with `f t` a unit. -/
def a3h_awayLift {X : Scheme.{u}} (f : A →+* Γ(X, ⊤)) {t : A} (hu : IsUnit (f t)) :
    HomogeneousLocalization.Away 𝒜 t →+* Γ(X, ⊤) :=
  (IsLocalization.Away.lift (S := Localization.Away (f t)) (f t) (g := RingHom.id _) hu).comp
    ((IsLocalization.map (M := .powers t) (T := .powers (f t)) _ f
      (by rw [← Submonoid.map_le_iff_le_comap, Submonoid.map_powers])).comp
        (algebraMap (HomogeneousLocalization.Away 𝒜 t) (Localization.Away t)))

theorem a3h_lift_mk' {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (r : R)
    [IsLocalization.Away r S] (hu : IsUnit r) (x : R) (y : Submonoid.powers r) (v : R)
    (hv : (y : R) = v) :
    v * IsLocalization.Away.lift (S := S) r (g := RingHom.id R) hu
      (IsLocalization.mk' S x y) = x := by
  have h := congrArg (IsLocalization.Away.lift (S := S) r (g := RingHom.id R) hu)
    (IsLocalization.mk'_spec S x y)
  rw [map_mul, IsLocalization.Away.lift_eq, IsLocalization.Away.lift_eq] at h
  rw [← hv, mul_comm]
  exact h

theorem a3h_awayLift_mk {X : Scheme.{u}} (f : A →+* Γ(X, ⊤)) {t : A} (hu : IsUnit (f t)) {d : ℕ}
    (hd : t ∈ 𝒜 d) (m : ℕ) (a : A) (ha : a ∈ 𝒜 (m • d)) :
    f t ^ m * a3h_awayLift 𝒜 f hu (HomogeneousLocalization.Away.mk 𝒜 hd m a ha) = f a := by
  simp only [a3h_awayLift, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk', IsLocalization.map_mk']
  rw [← map_pow]
  exact a3h_lift_mk' (S := Localization.Away (f t)) (f t) hu (f a) _ _ rfl

/-- If `f t` is a unit, `Proj.fromOfGlobalSections` lands in `D₊(t)` and is `Spec` of the ring map
`a ⁄ t^m ↦ f a ⁄ (f t)^m`.
Source: Hartshorne, *Algebraic Geometry*, Theorem II.7.1 (proof); Mathlib
`Proj.toBasicOpenOfGlobalSections`. -/
theorem a3h_fromOf_eq {X : Scheme.{u}} (f : A →+* Γ(X, ⊤))
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤) {t : A} {d : ℕ} (h0d : 0 < d)
    (hd : t ∈ 𝒜 d) (hu : IsUnit (f t)) :
    Proj.fromOfGlobalSections 𝒜 f hf =
      X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (a3h_awayLift 𝒜 f hu)) ≫ Proj.awayι 𝒜 t hd h0d := by
  have hU : X.basicOpen (f t) = ⊤ := Scheme.basicOpen_of_isUnit _ hu
  have : IsIso (X.basicOpen (f t)).ι := by rw [hU, ← Scheme.topIso_hom]; infer_instance
  rw [← cancel_epi (X.basicOpen (f t)).ι, g3c_ι_fromOfGlobalSections 𝒜 f hf h0d hd,
    g3c_toBasic_eq]
  simp only [Category.assoc, Proj.basicOpenIsoSpec_inv_ι]
  have key : g3c_basicOpenToSpecAway (f t) = (X.basicOpen (f t)).ι ≫ X.toSpecΓ ≫
      Spec.map (CommRingCat.ofHom (IsLocalization.Away.lift (S := Localization.Away (f t))
        (f t) (g := RingHom.id _) hu)) := by
    rw [← g3c_basicOpenToSpecAway_spec_assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have hid : (algebraMap Γ(X, ⊤) (Localization.Away (f t))).comp
        (IsLocalization.Away.lift (S := Localization.Away (f t)) (f t) (g := RingHom.id _) hu) =
          RingHom.id _ := by
      apply IsLocalization.ringHom_ext (Submonoid.powers (f t))
      rw [RingHom.comp_assoc, IsLocalization.Away.lift_comp, RingHom.comp_id, RingHom.id_comp]
    rw [hid]
    simp
  rw [key]
  simp only [Category.assoc, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
  rfl

end AwayUnit

/-! ## The chart morphisms and their glueing -/

section Glue

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom] {n : ℕ}
  (ℓ : Matrix (Fin (n + 1)) (Fin (a3s_N X + 1)) ℂ)

/-- The sections `ℓ_k / x_j` on the chart `X ∩ D₊(x_j)`, as a ring map from the homogeneous
coordinate ring of `ℙⁿ_ℤ`.
Source: Hartshorne, *Algebraic Geometry*, Theorem II.7.1. -/
def a3h_sect (j : Fin (a3s_N X + 1)) : UniversalRing n →+* Γ(Spec ((a3s_CX X).T j), ⊤) :=
  (Scheme.ΓSpecIso ((a3s_CX X).T j)).inv.hom.comp (((a3s_CX X).θ j).comp (a3h_sub ℓ))

variable {ℓ} (hfin : ((Ideal.Quotient.mk (a3s_IX X)).comp (a3r_lin ℓ).toRingHom).Finite)
include hfin

/-- On each chart the sections `ℓ_k / x_j` generate the unit ideal. -/
theorem a3h_sect_irrelevant (j : Fin (a3s_N X + 1)) :
    (HomogeneousIdeal.irrelevant (UniversalGrading n)).toIdeal.map (a3h_sect X ℓ j) = ⊤ := by
  have hspan : Ideal.span (Set.range fun k : Fin (n + 1) =>
      (a3s_CX X).θ j (a3r_lin ℓ (MvPolynomial.X k))) = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    let p : Spec ((a3s_CX X).T j) := ⟨M, hM.isPrime⟩
    obtain ⟨k, hk⟩ := a3h_exists_notMem X ℓ hfin ((a3s_CX X).κ j p)
    apply hk
    rw [(a3s_CX X).mem_prime_iff_of_isHomogeneous _ j p rfl _ 1 (a3r_lin_X_isHomogeneous ℓ k)]
    exact hle (Ideal.subset_span ⟨k, rfl⟩)
  rw [eq_top_iff, ← Ideal.map_top (Scheme.ΓSpecIso ((a3s_CX X).T j)).inv.hom, ← hspan,
    Ideal.map_span, Ideal.span_le]
  rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
  have hk := Ideal.mem_map_of_mem (a3h_sect X ℓ j)
    (HomogeneousIdeal.mem_irrelevant_of_mem (UniversalGrading n) zero_lt_one
      (isHomogeneous_X (ULift.{0} ℤ) k))
  simpa [a3h_sect, a3h_sub_X] using hk

/-- The projection on the chart `X ∩ D₊(x_j)`. -/
def a3h_chartMap (j : Fin (a3s_N X + 1)) : Spec ((a3s_CX X).T j) ⟶ g3c_P n :=
  Proj.fromOfGlobalSections (UniversalGrading n) (a3h_sect X ℓ j) (a3h_sect_irrelevant X hfin j)

omit hfin in
/-- The open cover of `X` by the charts `X ∩ D₊(x_j)`. -/
def a3h_cover : X.left.OpenCover :=
  Scheme.Cover.mkOfCovers (Fin (a3s_N X + 1)) (fun j => Spec ((a3s_CX X).T j)) (a3s_CX X).κ
    (fun x => let ⟨j, y, hy⟩ := (a3s_CX X).cover x; ⟨j, y, hy⟩)

omit [IsIntegral X.left] hfin in
theorem a3h_hov (a b : Fin (a3s_N X + 1)) (F : MvPolynomial (Fin (a3s_N X + 1)) ℂ) (e : ℕ)
    (hF : F.IsHomogeneous e) :
    (pullback.snd ((a3s_CX X).κ a) ((a3s_CX X).κ b)).appTop
        ((Scheme.ΓSpecIso _).inv ((a3s_CX X).θ b F)) =
      (pullback.snd ((a3s_CX X).κ a) ((a3s_CX X).κ b)).appTop
          ((Scheme.ΓSpecIso _).inv ((a3s_CX X).θ b (MvPolynomial.X a))) ^ e *
        (pullback.fst ((a3s_CX X).κ a) ((a3s_CX X).κ b)).appTop
          ((Scheme.ΓSpecIso _).inv ((a3s_CX X).θ a F)) :=
  a3m_restrict_hov (a3m_projCharts (a3s_N X)) (a3s_i X) (a3m_Pn_hov (a3s_N X)) a b F e hF

/-- The chart morphisms agree on overlaps: the sections differ by the unit `x_a / x_b`. -/
theorem a3h_chartMap_compat (a b : Fin (a3s_N X + 1)) :
    pullback.fst ((a3s_CX X).κ a) ((a3s_CX X).κ b) ≫ a3h_chartMap X hfin a =
      pullback.snd ((a3s_CX X).κ a) ((a3s_CX X).κ b) ≫ a3h_chartMap X hfin b := by
  set p₁ := pullback.fst ((a3s_CX X).κ a) ((a3s_CX X).κ b)
  set p₂ := pullback.snd ((a3s_CX X).κ a) ((a3s_CX X).κ b)
  have h₁ : (HomogeneousIdeal.irrelevant (UniversalGrading n)).toIdeal.map
      (p₁.appTop.hom.comp (a3h_sect X ℓ a)) = ⊤ := by
    rw [← Ideal.map_map, a3h_sect_irrelevant X hfin a, Ideal.map_top]
  have h₂ : (HomogeneousIdeal.irrelevant (UniversalGrading n)).toIdeal.map
      (p₂.appTop.hom.comp (a3h_sect X ℓ b)) = ⊤ := by
    rw [← Ideal.map_map, a3h_sect_irrelevant X hfin b, Ideal.map_top]
  rw [a3h_chartMap, a3h_chartMap, spec_g3c_comp_fromOfGlobalSections_aux _ p₁ _ _ h₁,
    spec_g3c_comp_fromOfGlobalSections_aux _ p₂ _ _ h₂]
  set u := p₂.appTop ((Scheme.ΓSpecIso _).inv ((a3s_CX X).θ b (MvPolynomial.X a)))
  set w := p₁.appTop ((Scheme.ΓSpecIso _).inv ((a3s_CX X).θ a (MvPolynomial.X b)))
  have huw : u * w = 1 := by
    have h := a3h_hov X a b (MvPolynomial.X b) 1 (isHomogeneous_X ℂ b)
    rw [(a3s_CX X).θ_X_self, map_one, map_one, pow_one] at h
    exact h.symm
  refine spec_g3c_fromOfGlobalSections_unit_twist_aux _ _ _ h₁ h₂ (Units.mkOfMulEqOne u w huw)
    fun d r hr => ?_
  rw [mem_homogeneousSubmodule] at hr
  exact a3h_hov X a b _ d (a3h_sub_isHomogeneous ℓ hr)

/-- The projection `X → ℙⁿ_ℤ`, glued from the chart morphisms. -/
def a3h_π₀ : X.left ⟶ g3c_P n :=
  (a3h_cover X).glueMorphisms (a3h_chartMap X hfin) fun a b => a3h_chartMap_compat X hfin a b

theorem a3h_κ_π₀ (j : Fin (a3s_N X + 1)) :
    (a3s_CX X).κ j ≫ a3h_π₀ X hfin = a3h_chartMap X hfin j :=
  (a3h_cover X).ι_glueMorphisms _ _ j

/-- **The linear projection `π_ℓ : X → ℙⁿ_ℂ`.**
Source: Shafarevich, *Basic Algebraic Geometry 1*, I.5.3, Theorem 1.15; Hartshorne, *Algebraic
Geometry*, Theorem II.7.1. -/
def a3h_π : X.left ⟶ a3m_Pn n :=
  pullback.lift X.hom (a3h_π₀ X hfin) (terminal.hom_ext _ _)

theorem a3h_π_fst : a3h_π X hfin ≫ pullback.fst _ _ = X.hom := pullback.lift_fst _ _ _

theorem a3h_π_snd : a3h_π X hfin ≫ pullback.snd _ _ = a3h_π₀ X hfin := pullback.lift_snd _ _ _

end Glue

/-! ## The projection on a chart -/

section ChartFormula

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom] {n : ℕ}
  {ℓ : Matrix (Fin (n + 1)) (Fin (a3s_N X + 1)) ℂ}
  (hfin : ((Ideal.Quotient.mk (a3s_IX X)).comp (a3r_lin ℓ).toRingHom).Finite)
  (j : Fin (a3s_N X + 1)) (i : Fin (n + 1))

omit [IsIntegral X.left] in
/-- The structure map of `X` on the chart `X ∩ D₊(x_j)` is `Spec` of `ℂ → T_j`. -/
theorem a3h_κ_hom : (a3s_CX X).κ j ≫ X.hom =
    Spec.map (CommRingCat.ofHom (((a3s_CX X).θ j).comp MvPolynomial.C)) := by
  have h1 : X.hom = a3s_i X ≫ pullback.fst (terminal.from (Spec ↧ℂ))
      (terminal.from (g3c_P (a3s_N X))) :=
    (a3s_pres X).immersion_toBase.symm
  have h2 : (a3s_CX X).κ j ≫ a3s_i X =
      @CategoryStruct.comp _ _ (Spec ((a3s_CX X).T j)) _ _
        (Spec.map (a3m_restrictHom (a3m_projCharts (a3s_N X)) (a3s_i X) j))
        ((a3m_projCharts (a3s_N X)).κ j) :=
    a3m_restrict_κ_comp _ _ j
  have h3 : (a3m_projCharts (a3s_N X)).κ j ≫ pullback.fst (terminal.from (Spec ↧ℂ))
      (terminal.from (g3c_P (a3s_N X))) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := ℂ)
        (B := HomogeneousLocalization.Away (UniversalGrading (a3s_N X))
          (MvPolynomial.X j : UniversalRing (a3s_N X))))) :=
    (a3m_prodChart_fst _ _).trans (Category.comp_id _)
  rw [h1, ← Category.assoc, h2, Category.assoc, h3]
  erw [← Spec.map_comp]
  congr 1
  ext c
  change (a3m_restrictHom (a3m_projCharts (a3s_N X)) (a3s_i X) j).hom
      (Algebra.TensorProduct.includeLeftRingHom c) =
    (a3m_restrictHom (a3m_projCharts (a3s_N X)) (a3s_i X) j).hom (a3m_Pnθ (a3s_N X) j (C c))
  rw [a3m_Pnθ, coe_eval₂Hom, eval₂_C]

variable (ℓ) in
/-- The value `s = ℓ_i / x_j` on the chart `j`. -/
abbrev a3h_s : (a3s_CX X).T j := (a3s_CX X).θ j (a3r_lin ℓ (MvPolynomial.X i))

variable (ℓ) in
/-- The chart ring localized at `s = ℓ_i / x_j`. -/
abbrev a3h_Rs : CommRingCat.{0} := .of (Localization.Away (a3h_s X ℓ j i))

variable (ℓ) in
/-- The open `D(ℓ_i / x_j)` of the chart `j`. -/
def a3h_ιs : Spec (a3h_Rs X ℓ j i) ⟶ Spec ((a3s_CX X).T j) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap ((a3s_CX X).T j) (Localization.Away (a3h_s X ℓ j i))))

variable (ℓ) in
/-- The sections `ℓ_k / x_j` on `D(ℓ_i / x_j)`. -/
def a3h_g : UniversalRing n →+* Γ(Spec (a3h_Rs X ℓ j i), ⊤) :=
  (a3h_ιs X ℓ j i).appTop.hom.comp (a3h_sect X ℓ j)

omit [IsIntegral X.left] in
theorem a3h_g_apply (r : UniversalRing n) :
    a3h_g X ℓ j i r = (Scheme.ΓSpecIso (a3h_Rs X ℓ j i)).inv.hom
      (algebraMap ((a3s_CX X).T j) (Localization.Away (a3h_s X ℓ j i))
        ((a3s_CX X).θ j (a3h_sub ℓ r))) := by
  rw [a3h_g, RingHom.comp_apply, a3h_sect, RingHom.comp_apply, a3h_ιs]
  erw [g3c_SpecMap_appTop_ΓSpecIso_inv]
  rfl

omit [IsIntegral X.left] in
theorem a3h_g_isUnit : IsUnit (a3h_g X ℓ j i (MvPolynomial.X i)) := by
  rw [a3h_g_apply, a3h_sub_X]
  exact (IsLocalization.Away.algebraMap_isUnit _).map _

variable (ℓ) in
/-- The ring map `ℤ[y / y_i] → T_j[1/s]`, `y_k / y_i ↦ ℓ_k / ℓ_i`. -/
def a3h_β : HomogeneousLocalization.Away (UniversalGrading n) (MvPolynomial.X i) →+*
    Localization.Away (a3h_s X ℓ j i) :=
  (Scheme.ΓSpecIso (a3h_Rs X ℓ j i)).hom.hom.comp
    (a3h_awayLift (UniversalGrading n) (a3h_g X ℓ j i) (a3h_g_isUnit X j i))

theorem a3h_ιs_chartMap : a3h_ιs X ℓ j i ≫ a3h_chartMap X hfin j =
    Spec.map (CommRingCat.ofHom (a3h_β X ℓ j i)) ≫ g3c_chartι n i := by
  have h' : (HomogeneousIdeal.irrelevant (UniversalGrading n)).toIdeal.map
      ((a3h_ιs X ℓ j i).appTop.hom.comp (a3h_sect X ℓ j)) = ⊤ := by
    rw [← Ideal.map_map, a3h_sect_irrelevant X hfin j, Ideal.map_top]
  rw [a3h_chartMap, spec_g3c_comp_fromOfGlobalSections_aux _ _ _ _ h']
  rw [a3h_fromOf_eq (UniversalGrading n) _ h' zero_lt_one (isHomogeneous_X (ULift.{0} ℤ) i)
    (a3h_g_isUnit X j i), ← SpecMap_ΓSpecIso_hom, ← Category.assoc, ← Spec.map_comp]
  rfl

variable (ℓ) in
/-- The ring map `ℂ ⊗ ℤ[y / y_i] → T_j[1/s]` of the projection on `D(ℓ_i / x_j)`. -/
def a3h_ψ : a3m_PnT n i →+* Localization.Away (a3h_s X ℓ j i) :=
  letI : Algebra ℤ (Localization.Away (a3h_s X ℓ j i)) := Ring.toIntAlgebra _
  (Algebra.TensorProduct.productMap
    ((algebraMap ((a3s_CX X).T j) (Localization.Away (a3h_s X ℓ j i))).comp
      (((a3s_CX X).θ j).comp MvPolynomial.C)).toIntAlgHom
    (a3h_β X ℓ j i).toIntAlgHom).toRingHom

/-- **The projection on a chart**: on `D(ℓ_i / x_j) ⊆ X ∩ D₊(x_j)`, `π_ℓ` is `Spec` of `a3h_ψ`
followed by the chart `D₊(y_i)` of `ℙⁿ_ℂ`. -/
theorem a3h_chart : Spec.map (CommRingCat.ofHom (a3h_ψ X ℓ j i)) ≫ a3m_Pnκ n i =
    a3h_ιs X ℓ j i ≫ (a3s_CX X).κ j ≫ a3h_π X hfin := by
  apply pullback.hom_ext
  · simp only [Category.assoc]
    rw [a3h_π_fst, a3h_κ_hom, a3m_Pnκ, a3m_prodChart_fst,
      Category.comp_id, a3h_ιs]
    erw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext c
    simp [a3h_ψ, Algebra.TensorProduct.productMap_apply_tmul]
    rfl
  · simp only [Category.assoc]
    rw [a3h_π_snd, a3h_κ_π₀ X hfin j, a3h_ιs_chartMap, a3m_Pnκ,
      a3m_prodChart_snd, ← Category.assoc, ← Spec.map_comp]
    congr 2
    ext b
    simp [a3h_ψ, Algebra.TensorProduct.productMap_apply_tmul]

omit [IsIntegral X.left] in
/-- On `D(ℓ_i / x_j)`, `ψ` sends the dehomogenization `G(y / y_i)` of a form `G` of degree `e` to
`G(ℓ) / ℓ_i^e`. -/
theorem a3h_ψ_θ (G : MvPolynomial (Fin (n + 1)) ℂ) (e : ℕ) (hG : G.IsHomogeneous e) :
    algebraMap ((a3s_CX X).T j) (Localization.Away (a3h_s X ℓ j i))
        ((a3s_CX X).θ j (a3r_lin ℓ G)) =
      algebraMap ((a3s_CX X).T j) (Localization.Away (a3h_s X ℓ j i)) (a3h_s X ℓ j i) ^ e *
        a3h_ψ X ℓ j i (a3m_Pnθ n i G) := by
  let φ₁ : MvPolynomial (Fin (n + 1)) ℂ →+* Localization.Away (a3h_s X ℓ j i) :=
    (algebraMap ((a3s_CX X).T j) _).comp (((a3s_CX X).θ j).comp (a3r_lin ℓ).toRingHom)
  let φ₂ : MvPolynomial (Fin (n + 1)) ℂ →+* Localization.Away (a3h_s X ℓ j i) :=
    (a3h_ψ X ℓ j i).comp (a3m_Pnθ n i)
  have hC : ∀ c, φ₁ (C c) = φ₂ (C c) := by
    intro c
    simp [φ₁, φ₂, a3m_Pnθ, a3h_ψ, Algebra.TensorProduct.productMap_apply_tmul]
  have hΓ : ∀ r, (Scheme.ΓSpecIso (a3h_Rs X ℓ j i)).hom.hom (a3h_g X ℓ j i r) =
      algebraMap ((a3s_CX X).T j) (Localization.Away (a3h_s X ℓ j i))
        ((a3s_CX X).θ j (a3h_sub ℓ r)) := by
    intro r
    rw [a3h_g_apply]
    exact Iso.inv_hom_id_apply (Scheme.ΓSpecIso (a3h_Rs X ℓ j i)) _
  have hX : ∀ k, φ₁ (MvPolynomial.X k) =
      algebraMap ((a3s_CX X).T j) _ (a3h_s X ℓ j i) * φ₂ (MvPolynomial.X k) := by
    intro k
    have h := a3h_awayLift_mk (UniversalGrading n) (a3h_g X ℓ j i) (a3h_g_isUnit X j i)
      (isHomogeneous_X (ULift.{0} ℤ) i) 1 (MvPolynomial.X k)
      (by simpa using isHomogeneous_X (ULift.{0} ℤ) k)
    have h' := congrArg (Scheme.ΓSpecIso (a3h_Rs X ℓ j i)).hom.hom h
    rw [map_mul, map_pow, pow_one, hΓ, hΓ, a3h_sub_X, a3h_sub_X] at h'
    simp only [φ₁, φ₂, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, a3m_Pnθ,
      coe_eval₂Hom, eval₂_X]
    rw [← h']
    simp [a3h_ψ, a3h_β, Algebra.TensorProduct.productMap_apply_tmul, chartCoordinate]
  exact a3m_twist φ₁ φ₂ _ hC hX G e hG

/-- **The point formula**: the homogeneous prime of `π_ℓ(x)` is the pull-back of that of `x` along
`y ↦ ℓ`. -/
theorem a3h_prime_π (x : X.left) :
    (a3m_projCharts n).prime (a3h_π X hfin x) = ((a3s_CX X).prime x).comap (a3r_lin ℓ) := by
  obtain ⟨j, p, hp⟩ := (a3s_CX X).cover x
  obtain ⟨i, hi⟩ := a3h_exists_notMem X ℓ hfin x
  have hs : a3h_s X ℓ j i ∉ p.asIdeal := by
    rwa [← (a3s_CX X).mem_prime_iff_of_isHomogeneous x j p hp _ 1
      (a3r_lin_X_isHomogeneous ℓ i)]
  obtain ⟨p', hp'⟩ : ∃ p' : Spec (a3h_Rs X ℓ j i),
      PrimeSpectrum.comap (algebraMap ((a3s_CX X).T j) (Localization.Away (a3h_s X ℓ j i))) p' =
        p :=
    (PrimeSpectrum.localization_away_comap_range (Localization.Away (a3h_s X ℓ j i))
      (a3h_s X ℓ j i)).ge ((PrimeSpectrum.mem_basicOpen _ _).2 hs)
  have hq : a3m_Pnκ n i (Spec.map (CommRingCat.ofHom (a3h_ψ X ℓ j i)) p') = a3h_π X hfin x := by
    rw [← Scheme.Hom.comp_apply, a3h_chart X hfin j i, Scheme.Hom.comp_apply,
      Scheme.Hom.comp_apply, ← hp, ← hp']
    rfl
  ext G
  rw [(a3m_projCharts n).mem_prime_iff _ i _ hq, Ideal.mem_comap,
    (a3s_CX X).mem_prime_iff x j p hp]
  refine forall_congr' fun e => ?_
  rw [a3h_lin_homogeneousComponent]
  have key := a3h_ψ_θ X (ℓ := ℓ) j i (homogeneousComponent e G) e (homogeneousComponent_isHomogeneous e G)
  have hu : IsUnit (algebraMap ((a3s_CX X).T j) (Localization.Away (a3h_s X ℓ j i))
      (a3h_s X ℓ j i) ^ e) := (IsLocalization.Away.algebraMap_isUnit _).pow e
  change a3h_ψ X ℓ j i (a3m_Pnθ n i (homogeneousComponent e G)) ∈ p'.asIdeal ↔
    (a3s_CX X).θ j (a3r_lin ℓ (homogeneousComponent e G)) ∈ p.asIdeal
  rw [← hp']
  change _ ↔ algebraMap ((a3s_CX X).T j) (Localization.Away (a3h_s X ℓ j i))
    ((a3s_CX X).θ j (a3r_lin ℓ (homogeneousComponent e G))) ∈ p'.asIdeal
  rw [key, mul_comm, Ideal.mul_unit_mem_iff_mem _ hu]

end ChartFormula

/-! ## The projection is finite and surjective -/

section FiniteSurjective

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom] {n : ℕ}
  {ℓ : Matrix (Fin (n + 1)) (Fin (a3s_N X + 1)) ℂ}
  (hfin : ((Ideal.Quotient.mk (a3s_IX X)).comp (a3r_lin ℓ).toRingHom).Finite)

instance a3h_π_isProper : IsProper (a3h_π X hfin) := by
  have : IsProper (a3h_π X hfin ≫ pullback.fst (terminal.from (Spec ↧ℂ))
      (terminal.from (g3c_P n))) := by
    rw [a3h_π_fst]; infer_instance
  have : IsSeparated (pullback.fst (terminal.from (Spec ↧ℂ)) (terminal.from (g3c_P n))) :=
    (ProjectiveSpace.toBaseProper (Fin (n + 1)) (Spec ↧ℂ)).toIsSeparated
  exact IsProper.of_comp _ (pullback.fst (terminal.from (Spec ↧ℂ)) (terminal.from (g3c_P n)))

/-- The point of `Spec (ℂ[x]/I_X)` of a point of `X`. -/
def a3h_ptS (x : X.left) : PrimeSpectrum (MvPolynomial (Fin (a3s_N X + 1)) ℂ ⧸ a3s_IX X) :=
  ⟨((a3s_CX X).prime x).map (Ideal.Quotient.mk (a3s_IX X)),
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by
      rw [Ideal.mk_ker]; exact a3s_IX_le X x)⟩

omit [IsProjective X.hom] in
theorem a3h_comap_ptS [IsProjective X.hom] (x : X.left) :
    ((a3h_ptS X x).asIdeal).comap (Ideal.Quotient.mk (a3s_IX X)) = (a3s_CX X).prime x := by
  rw [a3h_ptS, Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker,
    sup_eq_left.2 (a3s_IX_le X x)]

/-- The fibres of `π_ℓ` are finite: the points over `y` give distinct primes of the finite
`ℂ[y]`-algebra `ℂ[x]/I_X` over the prime of `y`.
Source: Atiyah–Macdonald, *Introduction to Commutative Algebra*, Corollary 5.9 (primes over a
prime in an integral extension are incomparable); Mathlib,
`Algebra.QuasiFinite.finite_comap_preimage_singleton`. -/
theorem a3h_finite_fibre (y : a3m_Pn n) : (a3h_π X hfin ⁻¹' {y}).Finite := by
  let alg : Algebra (MvPolynomial (Fin (n + 1)) ℂ)
      (MvPolynomial (Fin (a3s_N X + 1)) ℂ ⧸ a3s_IX X) :=
    ((Ideal.Quotient.mk (a3s_IX X)).comp (a3r_lin ℓ).toRingHom).toAlgebra
  have hmod : @Module.Finite (MvPolynomial (Fin (n + 1)) ℂ)
      (MvPolynomial (Fin (a3s_N X + 1)) ℂ ⧸ a3s_IX X) _ _ alg.toModule := hfin
  have hqf : @Algebra.QuasiFinite (MvPolynomial (Fin (n + 1)) ℂ)
      (MvPolynomial (Fin (a3s_N X + 1)) ℂ ⧸ a3s_IX X) _ _ alg :=
    @Algebra.QuasiFinite.instOfFinite _ _ _ _ alg hmod
  let P₀ : PrimeSpectrum (MvPolynomial (Fin (n + 1)) ℂ) := ⟨(a3m_projCharts n).prime y, inferInstance⟩
  have hF := @Algebra.QuasiFinite.finite_comap_preimage_singleton
    (MvPolynomial (Fin (n + 1)) ℂ) (MvPolynomial (Fin (a3s_N X + 1)) ℂ ⧸ a3s_IX X) _ _ alg hqf P₀
  refine Set.Finite.of_finite_image (f := a3h_ptS X) (hF.subset ?_) fun x _ x' _ hxx' => ?_
  · rintro _ ⟨x, hx, rfl⟩
    rw [Set.mem_preimage, Set.mem_singleton_iff]
    ext1
    change Ideal.comap (((Ideal.Quotient.mk (a3s_IX X)).comp (a3r_lin ℓ).toRingHom))
      (a3h_ptS X x).asIdeal = (a3m_projCharts n).prime y
    rw [← Ideal.comap_comap, a3h_comap_ptS]
    have h := a3h_prime_π X hfin x
    rw [Set.mem_singleton_iff.1 hx] at h
    exact h.symm
  · have h := congrArg (fun P : PrimeSpectrum _ => P.asIdeal.comap (Ideal.Quotient.mk (a3s_IX X)))
      hxx'
    simp only [a3h_comap_ptS] at h
    exact (a3s_CX X).prime_injective h

instance a3h_π_locallyQuasiFinite : LocallyQuasiFinite (a3h_π X hfin) :=
  (locallyQuasiFinite_iff_finite_preimage_singleton).2 (a3h_finite_fibre X hfin)

/-- **The projection is finite.**
Source: Stacks Project, Tag 02LS (proper and quasi-finite morphisms are finite); Shafarevich,
*Basic Algebraic Geometry 1*, I.5.3, Theorem 1.15. -/
instance a3h_π_isFinite : IsFinite (a3h_π X hfin) :=
  IsFinite.of_isProper_of_locallyQuasiFinite _

include hfin in
/-- The forms `ℓ_0, …, ℓ_n` are algebraically independent modulo `I_X`: the kernel of
`ℂ[y] → ℂ[x]/I_X` is zero, by the dimension count. -/
theorem a3h_comap_IX (hdim : ringKrullDim (MvPolynomial (Fin (a3s_N X + 1)) ℂ ⧸ a3s_IX X) =
    (n + 1 : ℕ)) : (a3s_IX X).comap (a3r_lin ℓ) = ⊥ := by
  by_contra hne
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hd := a3r_dim_eq_of_finite (a3s_IX X) ℓ hfin (a3s_IX X) le_rfl
  have hR : ringKrullDim (MvPolynomial (Fin (n + 1)) ℂ) = (n + 1 : ℕ) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
      ENat.card_eq_coe_fintype_card]
    simp
  have h1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (R := MvPolynomial (Fin (n + 1)) ℂ)
    (mem_nonZeroDivisors_of_ne_zero hr0)
  have h2 : ringKrullDim (MvPolynomial (Fin (n + 1)) ℂ ⧸ (a3s_IX X).comap (a3r_lin ℓ)) ≤
      ringKrullDim (MvPolynomial (Fin (n + 1)) ℂ ⧸ Ideal.span {r}) :=
    ringKrullDim_le_of_surjective (Ideal.Quotient.factor (Ideal.span_le.2
      (Set.singleton_subset_iff.2 hr))) (Ideal.Quotient.factor_surjective _)
  have h3 : ringKrullDim (MvPolynomial (Fin (n + 1)) ℂ ⧸ (a3s_IX X).comap (a3r_lin ℓ)) + 1 ≤
      ringKrullDim (MvPolynomial (Fin (n + 1)) ℂ) := le_trans (by gcongr) h1
  rw [← hd, hdim, hR] at h3
  exact absurd h3 (by norm_cast; omega)

/-- **The projection is surjective**: a relevant homogeneous prime `Q` of `ℂ[y]` has a prime of
`ℂ[x]/I_X` over it (lying over, `ℂ[y] ⊆ ℂ[x]/I_X` being integral), whose homogeneous core is a
relevant homogeneous prime over `Q`, the prime of a point of `X`.
Source: Atiyah–Macdonald, *Introduction to Commutative Algebra*, Theorem 5.10 (lying over);
Shafarevich, *Basic Algebraic Geometry 1*, I.5.3, Theorem 1.15. -/
theorem a3h_π_surjective (hdim : ringKrullDim (MvPolynomial (Fin (a3s_N X + 1)) ℂ ⧸ a3s_IX X) =
    (n + 1 : ℕ)) : Function.Surjective (a3h_π X hfin) := by
  intro y
  set Q := (a3m_projCharts n).prime y
  let _ : Algebra (MvPolynomial (Fin (n + 1)) ℂ) (MvPolynomial (Fin (a3s_N X + 1)) ℂ ⧸ a3s_IX X) :=
    ((Ideal.Quotient.mk (a3s_IX X)).comp (a3r_lin ℓ).toRingHom).toAlgebra
  have : Algebra.IsIntegral (MvPolynomial (Fin (n + 1)) ℂ)
      (MvPolynomial (Fin (a3s_N X + 1)) ℂ ⧸ a3s_IX X) := ⟨hfin.to_isIntegral⟩
  obtain ⟨P', -, hP', hP'Q⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S :=
    MvPolynomial (Fin (a3s_N X + 1)) ℂ ⧸ a3s_IX X) Q ⊥ (by
      intro r hr
      have : r ∈ (a3s_IX X).comap (a3r_lin ℓ) := by
        change (Ideal.Quotient.mk (a3s_IX X)) (a3r_lin ℓ r) ∈ (⊥ : Ideal _) at hr
        rw [Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at hr
        exact hr
      rw [a3h_comap_IX X hfin hdim, Ideal.mem_bot] at this
      rw [this]; exact zero_mem _)
  set P := P'.comap (Ideal.Quotient.mk (a3s_IX X))
  have hPprime : P.IsPrime := Ideal.comap_isPrime _ _
  have hIXP : a3s_IX X ≤ P := fun F hF => by
    change Ideal.Quotient.mk _ F ∈ P'
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hF]; exact zero_mem _
  have hPQ : P.comap (a3r_lin ℓ) = Q := hP'Q
  set P₀ := (P.homogeneousCore (homogeneousSubmodule (Fin (a3s_N X + 1)) ℂ)).toIdeal
  have hP₀prime : P₀.IsPrime := hPprime.homogeneousCore
  have hP₀h : P₀.IsHomogeneous (homogeneousSubmodule (Fin (a3s_N X + 1)) ℂ) :=
    (P.homogeneousCore _).isHomogeneous
  have hP₀le : P₀ ≤ P := Ideal.toIdeal_homogeneousCore_le _ _
  have hIXP₀ : a3s_IX X ≤ P₀ := fun F hF => by
    rw [← sum_homogeneousComponent F]
    exact Ideal.sum_mem _ fun e _ => Ideal.mem_homogeneousCore_of_homogeneous_of_mem
      ⟨e, (mem_homogeneousSubmodule _ _).2 (homogeneousComponent_isHomogeneous e F)⟩
      (hIXP (homogeneousComponent_mem_of_mem (a3s_IX_isHomogeneous X) hF e))
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
  obtain ⟨x, hx⟩ := a3s_exists_point X P₀ hP₀h k hk hIXP₀
  refine ⟨x, (a3m_projCharts n).prime_injective ?_⟩
  rw [a3h_prime_π X hfin x, hx, hcomap]

end FiniteSurjective

/-! ## Projective Noether normalization -/

section Noether

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]

/-- The affine cone over `X` has dimension `dim X + 1`. -/
theorem a3h_dim_cone (n : ℕ) (hn : Order.height (genericPoint X.left) = n) :
    ringKrullDim (MvPolynomial (Fin (a3s_N X + 1)) ℂ ⧸ a3s_IX X) = (n + 1 : ℕ) := by
  rw [← a3s_height_add_one X (genericPoint X.left), hn]
  rfl

/-- **Projective Noether normalization by a general linear projection.** For `X ⊂ ℙᴺ` of
dimension `n`, for a generic `ℓ : ℂ^{N+1} → ℂ^{n+1}` the projection `π_ℓ : X → ℙⁿ` is a finite
surjective morphism, and the homogeneous prime of `π_ℓ(x)` is the pull-back of that of `x` along
`y ↦ ℓ`.
Source: Shafarevich, *Basic Algebraic Geometry 1*, I.5.3, Theorem 1.15 and II.4.1; J. Roberts,
*Chow's moving lemma* (1972), §1; S. Bloch, *The moving lemma for higher Chow groups*,
J. Algebraic Geom. 3 (1994), §2. -/
theorem a3h_noether (n : ℕ) (hn : Order.height (genericPoint X.left) = n) :
    a3r_Generic {a : Fin (n + 1) × Fin (a3s_N X + 1) → ℂ |
      ∃ π : X.left ⟶ a3m_Pn n, IsFinite π ∧ Function.Surjective π ∧
        ∀ x, (a3m_projCharts n).prime (π x) =
          ((a3s_CX X).prime x).comap (a3r_lin (a3r_mat a))} :=
  (a3r_generic_finite (a3s_IX X) (a3s_IX_isHomogeneous X) (a3h_dim_cone X n hn)).mono
    fun _ ha => ⟨a3h_π X ha, inferInstance, a3h_π_surjective X ha (a3h_dim_cone X n hn),
      a3h_prime_π X ha⟩

example : ∃ n : ℕ, Order.height (genericPoint X.left) = n := by
  obtain ⟨-, n, hn, -⟩ := a1d_height_eq_trdeg (X := X) (genericPoint X.left)
  exact ⟨n, hn⟩

end Noether

end HodgeLean.Adapters
