import HodgeLean.Adapters.IntersectionProductFamilyLine

/-! # Families over `ℙ¹`: the product `X × ℙ¹` and its fibres over `0` and `1`

For a smooth projective integral `X` over `ℂ`, `T = X × ℙ¹_ℂ` (`a3n_T`) is smooth, integral,
Noetherian, and its projection `q : T → X` is proper and flat. The `ℂ`-points `t = c` of the chart
`ℙ¹ ∖ {∞}` give sections `σ_c : X → T` of `q` (`a3n_σ`).

Source: Hartshorne, *Algebraic Geometry*, II, §3 (fibred products) and Theorem II.8.15; Fulton,
*Intersection Theory*, second edition, §1.6 (families over `ℙ¹`). HC no distance; AV milestone
no distance.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial HomogeneousLocalization
open AlgebraicGeometry.ComplexProjectiveSpace HodgeLean.Foundations
open scoped MonoidalCategory

set_option backward.isDefEq.respectTransparency false

namespace HodgeLean.Adapters

attribute [local instance] MvPolynomial.gradedAlgebra

instance a3n_P1_lft : LocallyOfFiniteType a3n_P1.hom :=
  inferInstanceAs (LocallyOfFiniteType (ProjectiveSpace.toBase (Fin 2) (Spec ↧ℂ)))

instance a3n_P1_proper : IsProper a3n_P1.hom :=
  inferInstanceAs (IsProper (ProjectiveSpace.toBase (Fin 2) (Spec ↧ℂ)))

instance a3n_P1_isIntegral' : IsIntegral a3n_P1.left := a3n_P1_isIntegral

instance a3n_P1_smooth' : Smooth a3n_P1.hom := a3n_P1_smooth

section product
variable (X : Over (Spec ↧ℂ))

/-- The product `X × ℙ¹` over `ℂ`.
Source: Hartshorne, *Algebraic Geometry*, II, Theorem 3.3 (fibred products). -/
abbrev a3n_T : Over (Spec ↧ℂ) := X ⊗ a3n_P1

example : (a3n_T X).left = pullback X.hom a3n_P1.hom := rfl

/-- The projection `X × ℙ¹ → X`.
Source: Hartshorne, *Algebraic Geometry*, II, Theorem 3.3 (fibred products). -/
def a3n_q : a3n_T X ⟶ X := Over.homMk (pullback.fst X.hom a3n_P1.hom) rfl

example : (a3n_q X).left = pullback.fst X.hom a3n_P1.hom := rfl

/-- The projection `X × ℙ¹ → ℙ¹`.
Source: Hartshorne, *Algebraic Geometry*, II, Theorem 3.3 (fibred products). -/
abbrev a3n_p : (a3n_T X).left ⟶ a3m_Pn 1 := pullback.snd X.hom a3n_P1.hom

example : a3n_p X = pullback.snd X.hom a3n_P1.hom := rfl

instance a3n_q_proper : IsProper (a3n_q X).left :=
  inferInstanceAs (IsProper (pullback.fst X.hom a3n_P1.hom))

instance a3n_q_flat : Flat (a3n_q X).left :=
  inferInstanceAs (Flat (pullback.fst X.hom a3n_P1.hom))

instance a3n_T_smooth [Smooth X.hom] : Smooth (a3n_T X).hom :=
  inferInstanceAs (Smooth (pullback.fst X.hom a3n_P1.hom ≫ X.hom))

instance a3n_T_lft [LocallyOfFiniteType X.hom] : LocallyOfFiniteType (a3n_T X).hom :=
  inferInstanceAs (LocallyOfFiniteType (pullback.fst X.hom a3n_P1.hom ≫ X.hom))

instance a3n_T_isIntegral [IsIntegral X.left] [LocallyOfFiniteType X.hom] :
    IsIntegral (a3n_T X).left :=
  isIntegral_pullback_of_isAlgClosed ℂ X.left a3n_P1.left X.hom a3n_P1.hom

instance a3n_T_proper [IsProper X.hom] : IsProper (a3n_T X).hom :=
  inferInstanceAs (IsProper (pullback.fst X.hom a3n_P1.hom ≫ X.hom))

instance a3n_T_noeth [IsProper X.hom] : IsNoetherian (a3n_T X).left := by
  have : IsLocallyNoetherian (a3n_T X).left :=
    LocallyOfFiniteType.isLocallyNoetherian (a3n_T X).hom
  have : CompactSpace (a3n_T X).left := by
    have h := QuasiCompact.isCompact_preimage (f := (a3n_T X).hom) _ isOpen_univ isCompact_univ
    rw [Set.preimage_univ] at h
    exact isCompact_univ_iff.mp h
  exact ⟨⟩

end product

/-! ## The points `t = c` and the sections `σ_c` -/

section points

/-- Evaluation at `t = c` on the chart ring `ℂ ⊗ ℤ[t]` of `ℙ¹_ℂ ∖ {∞}`.
Source: Hartshorne, *Algebraic Geometry*, I, Theorem 1.3A (points of affine space). -/
def a3n_evc (c : ℂ) : a3m_PnT 1 0 →+* ℂ :=
  (Polynomial.evalRingHom c).comp (a3n_chartEquiv 0).symm.toRingHom

example (c : ℂ) : a3n_evc c 1 = 1 := map_one _

theorem a3n_evc_includeLeft (c z : ℂ) :
    a3n_evc c (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := ℂ) (B := a3n_A 0) z) =
      z := by
  have h : (a3n_chartEquiv 0).symm
      (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := ℂ) (B := a3n_A 0) z) =
        Polynomial.C z := by
    apply (a3n_chartEquiv 0).injective
    rw [AlgEquiv.apply_symm_apply]
    simp [a3n_chartEquiv]
  simp only [a3n_evc, RingHom.comp_apply]
  erw [h]
  simp

theorem a3n_chartEquiv_X :
    a3n_chartEquiv 0 Polynomial.X =
      Algebra.TensorProduct.includeRight (R := ℤ) (A := ℂ) (B := a3n_A 0)
        (chartCoordinate 0 1) := by
  simp [a3n_chartEquiv, a3n_awayEquiv, a3n_ev]

/-- The `ℂ`-point `t = c` of `ℙ¹_ℂ`.
Source: Hartshorne, *Algebraic Geometry*, II, Exercise 2.7 (points with values in a field). -/
def a3n_pt (c : ℂ) : Spec ↧ℂ ⟶ a3m_Pn 1 :=
  Spec.map (CommRingCat.ofHom (a3n_evc c)) ≫ a3m_Pnκ 1 0

example : Spec ↧ℂ ⟶ a3m_Pn 1 := a3n_pt 0

theorem a3n_pt_toBase (c : ℂ) :
    a3n_pt c ≫ ProjectiveSpace.toBase (Fin 2) (Spec ↧ℂ) = 𝟙 _ := by
  rw [a3n_pt, Category.assoc, a3n_chart_toBase, ← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext z
  exact a3n_evc_includeLeft c z

variable (X : Over (Spec ↧ℂ))

/-- The section `x ↦ (x, c)` of `X × ℙ¹ → X`.
Source: Hartshorne, *Algebraic Geometry*, II, Theorem 3.3 (universal property of fibred
products). -/
def a3n_σ (c : ℂ) : X.left ⟶ (a3n_T X).left :=
  pullback.lift (𝟙 X.left) (X.hom ≫ a3n_pt c) (by
    change 𝟙 X.left ≫ X.hom = (X.hom ≫ a3n_pt c) ≫ ProjectiveSpace.toBase (Fin 2) (Spec ↧ℂ)
    rw [Category.id_comp, Category.assoc, a3n_pt_toBase, Category.comp_id])

example (c : ℂ) : X.left ⟶ (a3n_T X).left := a3n_σ X c

@[reassoc (attr := simp)]
theorem a3n_σ_q (c : ℂ) : a3n_σ X c ≫ (a3n_q X).left = 𝟙 X.left :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem a3n_σ_p (c : ℂ) : a3n_σ X c ≫ a3n_p X = X.hom ≫ a3n_pt c :=
  pullback.lift_snd _ _ _

theorem a3n_q_σ_apply (c : ℂ) (x : X.left) : (a3n_q X).left (a3n_σ X c x) = x := by
  rw [← Scheme.Hom.comp_apply, a3n_σ_q]
  rfl

/-- The section `σ_c` is the fibre of `X × ℙ¹ → ℙ¹` over `t = c`. -/
theorem a3n_isPullback (c : ℂ) :
    IsPullback (a3n_σ X c) X.hom (a3n_p X) (a3n_pt c) := by
  refine IsPullback.of_right (h₁₂ := (a3n_q X).left)
    (h₂₂ := ProjectiveSpace.toBase (Fin 2) (Spec ↧ℂ)) (v₁₃ := X.hom) ?_ (a3n_σ_p X c) ?_
  · rw [a3n_σ_q, a3n_pt_toBase]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  · exact (IsPullback.of_hasPullback X.hom a3n_P1.hom).flip.flip

theorem a3n_range_σ (c : ℂ) :
    Set.range (a3n_σ X c) = a3n_p X ⁻¹' Set.range (a3n_pt c) := by
  have h := a3n_isPullback X c
  have e : a3n_σ X c = h.isoPullback.hom ≫ pullback.fst (a3n_p X) (a3n_pt c) :=
    (h.isoPullback_hom_fst).symm
  rw [e, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.2 h.isoPullback.hom.surjective, Set.image_univ, Scheme.Pullback.range_fst]

end points


/-! ## The fibres over `t = 0` and `t = 1` -/

section fibres

/-- The projection `ℙ¹_ℂ → ℙ¹_ℤ`.
Source: Hartshorne, *Algebraic Geometry*, II, Theorem 3.3 (base change). -/
abbrev a3n_π : a3m_Pn 1 ⟶ g3c_P 1 :=
  pullback.snd (terminal.from (Spec ↧ℂ)) (terminal.from (g3c_P 1))

example : a3n_π = pullback.snd (terminal.from (Spec ↧ℂ)) (terminal.from (g3c_P 1)) := rfl

/-- A prime of `ℂ ⊗ ℤ[t]` containing `t - c` is the kernel of evaluation at `c`. -/
theorem a3n_prime_eq (c : ℂ) (r : Spec (a3m_PnT 1 0))
    (hr : a3n_chartEquiv 0 (Polynomial.X - Polynomial.C c) ∈ r.asIdeal) :
    r = Spec.map (CommRingCat.ofHom (a3n_evc c)) (⟨⊥, Ideal.isPrime_bot⟩ : Spec ↧ℂ) := by
  have hC : ∀ a : ℂ, a3n_chartEquiv 0 (Polynomial.C a) =
      Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := ℂ) (B := a3n_A 0) a := fun a => by
    simp [a3n_chartEquiv]
  have hCmem : ∀ a : ℂ, a3n_chartEquiv 0 (Polynomial.C a) ∈ r.asIdeal ↔ a = 0 := by
    intro a
    constructor
    · intro h
      by_contra ha
      apply r.isPrime.ne_top
      refine Ideal.eq_top_of_isUnit_mem _ h ?_
      rw [hC]
      exact (isUnit_iff_ne_zero.2 ha).map _
    · rintro rfl
      rw [map_zero, map_zero]
      exact r.asIdeal.zero_mem
  apply PrimeSpectrum.ext
  ext y
  change y ∈ r.asIdeal ↔ y ∈ (⊥ : Ideal ℂ).comap (a3n_evc c)
  rw [Ideal.mem_comap, Ideal.mem_bot]
  obtain ⟨P, rfl⟩ := (a3n_chartEquiv 0).surjective y
  obtain ⟨Q, hQ⟩ := Polynomial.X_sub_C_dvd_sub_C_eval (a := c) (p := P)
  have hP : P = Polynomial.C (P.eval c) + (Polynomial.X - Polynomial.C c) * Q := by
    rw [← hQ]; ring
  have hev : a3n_evc c (a3n_chartEquiv 0 P) = P.eval c := by
    simp [a3n_evc]
  rw [hev]
  conv_lhs => rw [hP, map_add, map_mul]
  constructor
  · intro h
    have h2 : a3n_chartEquiv 0 (Polynomial.C (P.eval c)) ∈ r.asIdeal := by
      have := r.asIdeal.sub_mem h (r.asIdeal.mul_mem_right (a3n_chartEquiv 0 Q) hr)
      rwa [add_sub_cancel_right] at this
    exact (hCmem _).1 h2
  · intro h
    exact r.asIdeal.add_mem ((hCmem _).2 h) (r.asIdeal.mul_mem_right _ hr)

/-- The point of the chart over `t = c`. -/
theorem a3n_mem_range_pt (c : ℂ) (r : Spec (a3m_PnT 1 0))
    (hr : a3n_chartEquiv 0 (Polynomial.X - Polynomial.C c) ∈ r.asIdeal) :
    a3m_Pnκ 1 0 r ∈ Set.range (a3n_pt c) := by
  refine ⟨⟨⊥, Ideal.isPrime_bot⟩, ?_⟩
  rw [a3n_pt, Scheme.Hom.comp_apply, ← a3n_prime_eq c r hr]

theorem a3n_mem_chart_of_π (c : a3m_Pn 1) (hc : a3n_π c ∈ Set.range (g3c_chartι 1 0)) :
    c ∈ Set.range (a3m_Pnκ 1 0) := by
  have h := a3m_range_prodChart (𝟙 (Spec ↧ℂ)) (g3c_chartι 1 0)
  have hy : c ∈ pullback.fst (terminal.from (Spec ↧ℂ)) (terminal.from (g3c_P 1)) ⁻¹'
      Set.range (𝟙 (Spec ↧ℂ)) ∩ pullback.snd (terminal.from (Spec ↧ℂ))
        (terminal.from (g3c_P 1)) ⁻¹' Set.range (g3c_chartι 1 0) :=
    ⟨Set.mem_preimage.2 ⟨pullback.fst (terminal.from (Spec ↧ℂ)) (terminal.from (g3c_P 1)) c,
      by simp⟩, hc⟩
  rw [← h] at hy
  exact hy

theorem a3n_π_κ (r : Spec (a3m_PnT 1 0)) :
    a3n_π (a3m_Pnκ 1 0 r) = g3c_chartι 1 0 (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℂ) (B := a3n_A 0)).toRingHom) r) := by
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
  change (a3m_prodChart (𝟙 (Spec ↧ℂ)) (g3c_chartι 1 0) ≫ a3n_π) r = _
  rw [a3m_prodChart_snd]

/-- The points of `ℙ¹_ℂ` over the special point `c` of `ℙ¹_ℤ` (`t₁ = c` in the first chart), for
`c ∈ {0, 1}`. -/
theorem a3n_pt_of_π (c : ℂ) (n : ℤ) (hn : (n : ℂ) = c) (x : a3m_Pn 1)
    (hx : ∃ q : Spec (.of a3m_Away1), g3c_chartι 1 0 q = a3n_π x ∧ a3m_t₁ - n ∈ q.asIdeal) :
    x ∈ Set.range (a3n_pt c) := by
  obtain ⟨q, hq, ht⟩ := hx
  obtain ⟨r, rfl⟩ := a3n_mem_chart_of_π x ⟨q, hq⟩
  rw [a3n_π_κ] at hq
  have hq' := (g3c_chartι 1 0).isOpenEmbedding.injective hq
  subst hq'
  refine a3n_mem_range_pt c r ?_
  have h1 : a3n_chartEquiv 0 (Polynomial.X - Polynomial.C c) =
      Algebra.TensorProduct.includeRight (R := ℤ) (A := ℂ) (B := a3n_A 0) (a3m_t₁ - n) := by
    rw [map_sub, a3n_chartEquiv_X, map_sub, ← hn, map_intCast]
    simp only [map_intCast]
  rw [h1]
  exact ht

theorem a3n_pt_of_Z0 (x : a3m_Pn 1) (hx : a3n_π x ∈ a3m_Z0) : x ∈ Set.range (a3n_pt 0) := by
  obtain ⟨q, hq, ht⟩ := hx
  exact a3n_pt_of_π 0 0 (by simp) x ⟨q, hq, by simpa using ht⟩

theorem a3n_pt_of_Zinf (x : a3m_Pn 1) (hx : a3n_π x ∈ a3m_Zinf) : x ∈ Set.range (a3n_pt 1) := by
  obtain ⟨q, hq, ht⟩ := hx
  exact a3n_pt_of_π 1 1 (by simp) x ⟨q, hq, by simpa using ht⟩

variable (X : Over (Spec ↧ℂ))

/-- The map `X × ℙ¹ → ℙ¹_ℤ` to the pointed curve of `a3m_P1curve`.
Source: Fulton, *Intersection Theory*, second edition, §1.6 (families over `ℙ¹`). -/
abbrev a3n_h : (a3n_T X).left ⟶ g3c_P 1 := a3n_p X ≫ a3n_π

example : a3n_h X = a3n_p X ≫ a3n_π := rfl

/-- A point of `X × ℙ¹` over `t = 0` is `σ_0` of its projection. -/
theorem a3n_eq_σ0 (τ : (a3n_T X).left) (h : a3n_h X τ ∈ a3m_Z0) :
    τ = a3n_σ X 0 ((a3n_q X).left τ) := by
  have h1 := a3n_pt_of_Z0 (a3n_p X τ) h
  have h2 : τ ∈ Set.range (a3n_σ X 0) := by rw [a3n_range_σ]; exact h1
  obtain ⟨x, rfl⟩ := h2
  rw [a3n_q_σ_apply]

/-- A point of `X × ℙ¹` over `t = 1` is `σ_1` of its projection. -/
theorem a3n_eq_σ1 (τ : (a3n_T X).left) (h : a3n_h X τ ∈ a3m_Zinf) :
    τ = a3n_σ X 1 ((a3n_q X).left τ) := by
  have h1 := a3n_pt_of_Zinf (a3n_p X τ) h
  have h2 : τ ∈ Set.range (a3n_σ X 1) := by rw [a3n_range_σ]; exact h1
  obtain ⟨x, rfl⟩ := h2
  rw [a3n_q_σ_apply]

end fibres

/-! ## Dimensions on `X × ℙ¹` -/

section dims
open Order

/-- The unique point of `Spec ℂ`.
Source: Hartshorne, *Algebraic Geometry*, II, Example 2.3.1 (`Spec` of a field). -/
def a3n_o : Spec ↧ℂ := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)

example (y : Spec ↧ℂ) : y = a3n_o := Subsingleton.elim _ _

/-- A point is closed exactly when it has no proper specialization, i.e. height zero. -/
theorem a3n_isClosed_of_height_eq_zero {Y : Scheme.{0}} (y : Y) (h : height y = 0) :
    IsClosed ({y} : Set Y) := by
  rw [← closure_subset_iff_isClosed]
  intro z hz
  have hyz : y ⤳ z := specializes_iff_mem_closure.2 hz
  have hmin : IsMin y := Order.height_eq_zero.1 h
  have hzy : z ≤ y := Scheme.le_iff_specializes.2 hyz
  exact (hyz.antisymm (Scheme.le_iff_specializes.1 (hmin hzy))).eq.symm

theorem a3n_height_eq_zero_of_isClosed {Y : Scheme.{0}} (y : Y) (h : IsClosed ({y} : Set Y)) :
    height y = 0 := by
  rw [Order.height_eq_zero]
  intro z hz
  have hyz : y ⤳ z := Scheme.le_iff_specializes.1 hz
  have : z ∈ closure ({y} : Set Y) := specializes_iff_mem_closure.1 hyz
  rw [h.closure_eq, Set.mem_singleton_iff] at this
  rw [this]

theorem a3n_genericPoint_P1 : genericPoint (a3m_Pn 1) = a3n_η := by
  refine (genericPoint_spec (a3m_Pn 1)).eq ?_
  rw [isGenericPoint_def]
  exact Set.eq_univ_of_forall fun c => specializes_iff_mem_closure.1 (a3n_η_specializes c)

theorem a3n_ringKrullDim_chart : ringKrullDim (a3m_PnT 1 0) = 1 := by
  rw [← ringKrullDim_eq_of_ringEquiv (a3n_chartEquiv 0).toRingEquiv,
    Polynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  rfl

/-- `ℙ¹_ℂ` has dimension one. -/
theorem a3n_height_genericPoint_P1 : height (genericPoint (a3m_Pn 1)) = 1 := by
  rw [a3n_genericPoint_P1, a3n_η]
  refine (a3m_height_openImmersion (Y := a3n_P1) (a3m_Pnκ 1 0) (a3n_bot 0)).trans ?_
  have h := hc9k8_height_spec (a3m_PnT 1 0) (a3n_bot 0)
  have h2 : ringKrullDim (a3m_PnT 1 0 ⧸ (a3n_bot 0).asIdeal) = 1 := by
    change ringKrullDim (a3m_PnT 1 0 ⧸ (⊥ : Ideal (a3m_PnT 1 0))) = 1
    rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _), a3n_ringKrullDim_chart]
  rw [h2] at h
  exact_mod_cast h

/-- On an integral scheme of finite type over `ℂ` of dimension `n`, closed points have
codimension `n`. -/
theorem a3n_coheight_of_isClosed (Y : Over (Spec ↧ℂ)) [LocallyOfFiniteType Y.hom]
    [IsIntegral Y.left] (n : ℕ) (hn : height (genericPoint Y.left) = n) (y : Y.left)
    (h : IsClosed ({y} : Set Y.left)) : coheight y = n := by
  have := a3m_height_add_coheight Y y
  rwa [a3n_height_eq_zero_of_isClosed y h, zero_add, hn] at this

/-- The dimension formula on `X × ℙ¹`: `height τ + coheight τ = dim X + 1`. -/
theorem a3n_height_add_coheight_T (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [LocallyOfFiniteType X.hom] (n : ℕ) (hn : height (genericPoint X.left) = n)
    (τ : (a3n_T X).left) : height τ + coheight τ = (n + 1 : ℕ) := by
  refine hc9k8_pullback_height_add_coheight X.hom a3n_P1.hom n 1 (fun U hU hne => ?_)
    (fun V hV hne => ?_) τ
  · exact hc9k8_ringKrullDim_affineOpen X.hom n
      (fun y hy => a3n_coheight_of_isClosed X n hn y hy) U hU hne
  · exact hc9k8_ringKrullDim_affineOpen a3n_P1.hom 1
      (fun y hy => a3n_coheight_of_isClosed a3n_P1 1 (by exact_mod_cast
        a3n_height_genericPoint_P1) y hy) V hV hne

/-- The point `t = c` of `ℙ¹_ℂ` is closed. -/
theorem a3n_isClosed_pt (c : ℂ) :
    IsClosed ({a3n_pt c a3n_o} : Set (a3m_Pn 1)) := by
  refine a3n_isClosed_of_height_eq_zero _ ?_
  rw [a3n_pt, Scheme.Hom.comp_apply]
  refine (a3m_height_openImmersion (Y := a3n_P1) (a3m_Pnκ 1 0) _).trans ?_
  have h := hc9k8_height_spec (a3m_PnT 1 0)
    (Spec.map (CommRingCat.ofHom (a3n_evc c)) a3n_o)
  have hsurj : Function.Surjective (a3n_evc c) := fun z =>
    ⟨Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := ℂ) (B := a3n_A 0) z,
      a3n_evc_includeLeft c z⟩
  have h2 : ringKrullDim (a3m_PnT 1 0 ⧸ (Spec.map (CommRingCat.ofHom (a3n_evc c))
      a3n_o).asIdeal) = 0 := by
    change ringKrullDim (a3m_PnT 1 0 ⧸ (⊥ : Ideal ℂ).comap (a3n_evc c)) = 0
    rw [← RingHom.ker_eq_comap_bot, ringKrullDim_eq_of_ringEquiv
      (RingHom.quotientKerEquivOfSurjective hsurj), ringKrullDim_eq_zero_of_field]
  rw [h2] at h
  exact_mod_cast h

variable (X : Over (Spec ↧ℂ))

/-- Every specialization of a point of `σ_c(X)` lies in `σ_c(X)`. -/
theorem a3n_mem_range_σ_of_specializes (c : ℂ) {x : X.left} {τ : (a3n_T X).left}
    (h : a3n_σ X c x ⤳ τ) : τ ∈ Set.range (a3n_σ X c) := by
  rw [a3n_range_σ]
  have h1 := h.map (a3n_p X).continuous
  rw [← Scheme.Hom.comp_apply, a3n_σ_p, Scheme.Hom.comp_apply] at h1
  have h2 : a3n_p X τ ∈ closure ({a3n_pt c (X.hom x)} : Set (a3m_Pn 1)) :=
    specializes_iff_mem_closure.1 h1
  have hpt : X.hom x = a3n_o := Subsingleton.elim _ _
  rw [hpt, (a3n_isClosed_pt c).closure_eq, Set.mem_singleton_iff] at h2
  exact ⟨_, h2.symm⟩

theorem a3n_σ_strictMono (c : ℂ) : StrictMono (a3n_σ X c) := by
  intro a b hab
  have h1 : b ⤳ a := Scheme.le_iff_specializes.1 hab.le
  refine lt_of_le_not_ge (Scheme.le_iff_specializes.2 (h1.map (a3n_σ X c).continuous)) ?_
  intro hle
  apply hab.not_ge
  have := (Scheme.le_iff_specializes.1 hle).map (a3n_q X).left.continuous
  rw [a3n_q_σ_apply, a3n_q_σ_apply] at this
  exact Scheme.le_iff_specializes.2 this

/-- `σ_c` preserves heights. -/
theorem a3n_height_σ (c : ℂ) (x : X.left) : height (a3n_σ X c x) = height x := by
  refine (Order.height_eq_of_strictMono (a3n_σ X c) (a3n_σ_strictMono X c) (fun a b hb => ?_)
    x).symm
  obtain ⟨a', rfl⟩ := a3n_mem_range_σ_of_specializes X c
    (Scheme.le_iff_specializes.1 hb.le)
  refine ⟨a', lt_of_le_not_ge ?_ ?_, rfl⟩
  · have := (Scheme.le_iff_specializes.1 hb.le).map (a3n_q X).left.continuous
    rw [a3n_q_σ_apply, a3n_q_σ_apply] at this
    exact Scheme.le_iff_specializes.2 this
  · intro hle
    exact hb.not_ge (Scheme.le_iff_specializes.2
      ((Scheme.le_iff_specializes.1 hle).map (a3n_σ X c).continuous))

/-- `codim (x, c) = codim x + 1` on `X × ℙ¹`. -/
theorem a3n_coheight_σ [IsIntegral X.left] [LocallyOfFiniteType X.hom] (c : ℂ) (x : X.left) :
    coheight (a3n_σ X c x) = coheight x + 1 := by
  obtain ⟨-, n, hn, -⟩ := a1d_height_eq_trdeg (X := X) (genericPoint X.left)
  have hT := a3n_height_add_coheight_T X n hn (a3n_σ X c x)
  have hX := a3m_height_add_coheight X x
  rw [hn] at hX
  rw [a3n_height_σ] at hT
  have hfin : height x ≠ ⊤ := fun h => by rw [h, top_add] at hX; exact ENat.top_ne_natCast n hX
  obtain ⟨h, hh⟩ := ENat.ne_top_iff_exists.1 hfin
  rw [← hh] at hT hX
  have hc1 : coheight x ≠ ⊤ := fun h' => by rw [h', add_top] at hX; exact ENat.top_ne_natCast n hX
  have hc2 : coheight (a3n_σ X c x) ≠ ⊤ := fun h' => by
    rw [h', add_top] at hT; exact ENat.top_ne_natCast _ hT
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.1 hc1
  obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.1 hc2
  rw [← ha] at hX ⊢
  rw [← hb] at hT ⊢
  have e1 : h + a = n := by exact_mod_cast hX
  have e2 : h + b = n + 1 := by exact_mod_cast hT
  norm_cast
  omega

end dims

/-! ## The point `b_v` of `V × ℙ¹` -/

section bv
variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [LocallyOfFiniteType X.hom] (v : X.left)

/-- `V × ℙ¹` for `V = closure {v}`.
Source: Hartshorne, *Algebraic Geometry*, II, Theorem 3.3 and Exercise 3.15. -/
abbrev a3n_Z : Scheme.{0} := pullback (cycleComponentι X.left v ≫ X.hom) a3n_P1.hom

example : a3n_Z X v = pullback (cycleComponentι X.left v ≫ X.hom) a3n_P1.hom := rfl

instance a3n_Z_isIntegral : IsIntegral (a3n_Z X v) :=
  isIntegral_pullback_of_isAlgClosed ℂ (cycleComponent X.left v) a3n_P1.left
    (cycleComponentι X.left v ≫ X.hom) a3n_P1.hom

/-- `V × ℙ¹ → X × ℙ¹`.
Source: Hartshorne, *Algebraic Geometry*, II, Theorem 3.3 (functoriality of fibred products). -/
def a3n_j : a3n_Z X v ⟶ (a3n_T X).left :=
  pullback.map _ _ X.hom a3n_P1.hom (cycleComponentι X.left v) (𝟙 _) (𝟙 _) (by simp) (by simp)

example : a3n_j X v ≫ pullback.snd X.hom a3n_P1.hom = pullback.snd _ _ := by
  simp [a3n_j]

omit [IsIntegral X.left] [LocallyOfFiniteType X.hom] in
theorem a3n_range_j : Set.range (a3n_j X v) = (a3n_q X).left ⁻¹' closure {v} := by
  rw [a3n_j]
  erw [Scheme.Pullback.range_map]
  rw [range_cycleComponentι]
  ext τ
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_range]
  exact ⟨fun h => h.1, fun h => ⟨h, ⟨_, rfl⟩⟩⟩

/-- The generic point of `q⁻¹(closure {v}) = V × ℙ¹`.
Source: Hartshorne, *Algebraic Geometry*, Exercise II.3.15 (products of varieties are
irreducible). -/
def a3n_b : (a3n_T X).left := a3n_j X v (genericPoint (a3n_Z X v))

example : (a3n_T X).left := a3n_b X v

theorem a3n_closure_b : closure ({a3n_b X v} : Set (a3n_T X).left) =
    (a3n_q X).left ⁻¹' closure {v} := by
  have hclosed : IsClosed ((a3n_q X).left ⁻¹' closure ({v} : Set X.left)) :=
    isClosed_closure.preimage (a3n_q X).left.continuous
  refine le_antisymm ?_ fun τ hτ => ?_
  · refine closure_minimal ?_ hclosed
    rw [Set.singleton_subset_iff, ← a3n_range_j]
    exact ⟨_, rfl⟩
  · rw [← a3n_range_j] at hτ
    obtain ⟨z, rfl⟩ := hτ
    exact specializes_iff_mem_closure.1
      ((genericPoint_specializes z).map (a3n_j X v).continuous)

theorem a3n_b_specializes_iff (τ : (a3n_T X).left) :
    a3n_b X v ⤳ τ ↔ v ⤳ (a3n_q X).left τ := by
  rw [specializes_iff_mem_closure, a3n_closure_b, Set.mem_preimage, ← specializes_iff_mem_closure]

theorem a3n_q_b : (a3n_q X).left (a3n_b X v) = v := by
  have h1 : v ⤳ (a3n_q X).left (a3n_b X v) := (a3n_b_specializes_iff X v _).1 specializes_rfl
  have h2 : a3n_b X v ⤳ a3n_σ X 0 v := by
    rw [a3n_b_specializes_iff, a3n_q_σ_apply]
  have h3 := h2.map (a3n_q X).left.continuous
  rw [a3n_q_σ_apply] at h3
  exact (h3.antisymm h1).eq

end bv

end HodgeLean.Adapters
