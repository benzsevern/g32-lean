import HodgeLean.Adapters.IntersectionProductBlochExcess
import HodgeLean.Adapters.IntersectionProductTor

/-! # The coordinate `t₁` on `ℙ¹` and the divisor of `t` on `X × ℙ¹`

Stage A3.3, the description of rational equivalence through `X × ℙ¹` (Fulton, Proposition 1.6).
This file collects the facts on `ℙ¹` and on `T = X × ℙ¹` used there:
* the generic point of `ℙ¹` lies over neither `t₁ = 0` nor `t₁ = 1`, and a point of `T` that
  specializes both to a point of `σ₀(X)` and to a point of `σ₁(X)` dominates `ℙ¹`
  (`a3k_h_eq_generic`);
* the affine coordinate `t₁ = s₁/s₀` as a section of `ℙ¹_ℤ` over `D₊(s₀)` (`a3k_S1`), whose germ
  lies in the maximal ideal over `t₁ = 0` and is congruent to `1` over `t₁ = 1`;
* for a subvariety `D` of `T` dominating `ℙ¹`, `[div (t|_D)] = [div t] · [D]` on `T`
  (`a3k_cyc_eq_intersect`), the cycle form of Fulton, Theorem 2.4, for `t` on `T` met with `D`;
  the divisor of `t` on `T` is carried by `X × {0}` and `X × {1}`, with a positive coefficient on
  `X × {0}` (`a3k_cycT_supp`, `a3k_cycT_pos`).

Source: Fulton, *Intersection Theory*, second edition, §1.6 and Theorem 2.4; Hartshorne,
*Algebraic Geometry*, II, Proposition 2.5. HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Order MvPolynomial
open AlgebraicGeometry.ComplexProjectiveSpace HodgeLean.Foundations
open scoped MonoidalCategory

set_option backward.isDefEq.respectTransparency false

namespace HodgeLean.Adapters

attribute [local instance] MvPolynomial.gradedAlgebra

section P1

theorem a3k_generic_not_mem_Z0 : genericPoint (g3c_P 1) ∉ a3m_Z0 := by
  rintro ⟨q, hq, ht⟩
  rw [a3m_genericPoint_P1, a3m_η1] at hq
  have hq' := (g3c_chartι 1 0).isOpenEmbedding.injective hq
  subst hq'
  exact a3m_chartCoordinate_ne_zero 0 1 ((Ideal.mem_bot).1 ht)

theorem a3k_generic_not_mem_Zinf : genericPoint (g3c_P 1) ∉ a3m_Zinf := by
  rintro ⟨q, hq, ht⟩
  rw [a3m_genericPoint_P1, a3m_η1] at hq
  have hq' := (g3c_chartι 1 0).isOpenEmbedding.injective hq
  subst hq'
  exact a3m_t₁_sub_one_ne_zero ((Ideal.mem_bot).1 ht)

/-- `ℂ ⊗ ℤ[t₁] ← ℤ[t₁]` is injective. -/
theorem a3k_includeRight_injective :
    Function.Injective (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℂ)
      (B := a3n_A 0)).toRingHom := by
  have hcomp : (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℂ) (B := a3n_A 0)).toRingHom.comp
      a3m_evt = (Polynomial.eval₂RingHom
        (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := ℂ) (B := a3m_Away1))
        (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℂ) a3m_t₁)).comp
        (Polynomial.mapRingHom (Int.castRingHom ℂ)) := by
    refine Polynomial.ringHom_ext (fun n => ?_) ?_
    · simp [a3m_evt]
    · simp [a3m_evt]
  intro a b hab
  obtain ⟨p, rfl⟩ := a3m_evt_surjective a
  obtain ⟨p', rfl⟩ := a3m_evt_surjective b
  have h := RingHom.congr_fun hcomp p
  have h' := RingHom.congr_fun hcomp p'
  simp only [RingHom.comp_apply] at h h'
  rw [h, h'] at hab
  have := a3m_tensor_eval₂_injective ℂ hab
  rw [Polynomial.map_injective _ (Int.cast_injective (α := ℂ)) this]

/-- `ℙ¹_ℂ → ℙ¹_ℤ` sends the generic point to the generic point. -/
theorem a3k_π_generic : a3n_π (genericPoint (a3m_Pn 1)) = genericPoint (g3c_P 1) := by
  rw [a3n_genericPoint_P1, a3n_η, a3n_π_κ, a3m_genericPoint_P1, a3m_η1]
  congr 1
  apply PrimeSpectrum.ext
  change Ideal.comap _ (⊥ : Ideal (a3m_PnT 1 0)) = ⊥
  rw [← RingHom.ker_eq_comap_bot]
  exact (RingHom.injective_iff_ker_eq_bot _).1 a3k_includeRight_injective

/-- On `ℙ¹_ℂ`, a proper generization of a point is the generic point. -/
theorem a3k_P1_eq_generic {p c : a3m_Pn 1} (h : p ⤳ c) (hne : p ≠ c) :
    p = genericPoint (a3m_Pn 1) := by
  have : IsLocallyNoetherian (a3m_Pn 1) := LocallyOfFiniteType.isLocallyNoetherian a3n_P1.hom
  have hlt := a3y_coheight_lt h hne
  have hc := a3m_height_add_coheight a3n_P1 c
  rw [show height (genericPoint a3n_P1.left) = 1 from a3n_height_genericPoint_P1] at hc
  have hc1 : coheight c ≤ 1 := by
    rw [← hc]
    exact le_add_self
  have hp0 : coheight p = 0 := Order.lt_one_iff.1 (hlt.trans_le hc1)
  have hmax : IsMax p := Order.coheight_eq_zero.1 hp0
  have h1 : p ≤ genericPoint (a3m_Pn 1) := by
    rw [Scheme.le_iff_specializes]
    exact genericPoint_specializes p
  have h2 := hmax h1
  rw [Scheme.le_iff_specializes] at h1 h2
  exact (h2.antisymm h1).eq

variable (X : Over (Spec ↧ℂ))

theorem a3k_p_σ (c : ℂ) (x : X.left) : a3n_p X (a3n_σ X c x) = a3n_pt c a3n_o := by
  rw [← Scheme.Hom.comp_apply, a3n_σ_p, Scheme.Hom.comp_apply,
    show X.hom x = a3n_o from Subsingleton.elim _ _]

/-- A point of `X × ℙ¹` specializing to points of `σ₀(X)` and of `σ₁(X)` dominates `ℙ¹`. -/
theorem a3k_h_eq_generic {τ : (a3n_T X).left} {x x' : X.left} (h0 : τ ⤳ a3n_σ X 0 x)
    (h1 : τ ⤳ a3n_σ X 1 x') : a3n_h X τ = genericPoint (g3c_P 1) := by
  have h0' := h0.map (a3n_p X).continuous
  have h1' := h1.map (a3n_p X).continuous
  rw [a3k_p_σ] at h0' h1'
  have hne : a3n_p X τ ≠ a3n_pt 0 a3n_o := by
    intro he
    rw [he] at h1'
    have := specializes_iff_mem_closure.1 h1'
    rw [(a3n_isClosed_pt 0).closure_eq, Set.mem_singleton_iff] at this
    exact a3n_pt_ne this.symm
  have hgen := a3k_P1_eq_generic h0' hne
  change a3n_π (a3n_p X τ) = _
  rw [hgen, a3k_π_generic]

/-- A point dominating `ℙ¹` does not lie on `σ_c(X)` for `c ∈ {0, 1}`. -/
theorem a3k_not_mem_range_σ {τ : (a3n_T X).left} (hτ : a3n_h X τ = genericPoint (g3c_P 1))
    (c : ℂ) (hc : c = 0 ∨ c = 1) : τ ∉ Set.range (a3n_σ X c) := by
  rintro ⟨x, rfl⟩
  rcases hc with rfl | rfl
  · exact a3k_generic_not_mem_Z0 (hτ ▸ a3n_h_σ0 X x)
  · exact a3k_generic_not_mem_Zinf (hτ ▸ a3n_h_σ1 X x)

end P1

section coordinate

theorem a3k_mem_basicOpen_X0 (c : g3c_P 1) (hc : c ∈ Set.range (g3c_chartι 1 0)) :
    c ∈ Proj.basicOpen (UniversalGrading.{0} 1) (X 0) :=
  (a3m_mem_range_chart 0 c).1 hc

/-- The section `g/s₀` of `ℙ¹_ℤ` over `D₊(s₀)` for a linear form `g`.
Source: Hartshorne, *Algebraic Geometry*, II, Proposition 2.5 (`D₊(f) ≅ Spec S_(f)`). -/
def a3k_Sg {g : UniversalRing.{0} 1} (hg : g ∈ UniversalGrading.{0} 1 1) :
    Γ(g3c_P 1, Proj.basicOpen (UniversalGrading.{0} 1) (X 0)) :=
  (Proj.basicOpenIsoAway _ (X 0) (a3m_X_mem 0) one_pos).hom
    (HomogeneousLocalization.Away.isLocalizationElem (a3m_X_mem 0) hg)

example : Γ(g3c_P 1, Proj.basicOpen (UniversalGrading.{0} 1) (X 0)) := a3k_Sg (a3m_X_mem 0)

theorem a3k_germ_Sg {g : UniversalRing.{0} 1} (hg : g ∈ UniversalGrading.{0} 1 1)
    (c : g3c_P 1) (hc : c ∈ Proj.basicOpen (UniversalGrading.{0} 1) (X 0)) :
    Proj.stalkIso' _ c ((g3c_P 1).presheaf.germ _ c hc (a3k_Sg hg)) =
      HomogeneousLocalization.mapId _ (Submonoid.powers_le.mpr hc)
        (HomogeneousLocalization.Away.isLocalizationElem (a3m_X_mem 0) hg) := by
  exact Proj.stalkIso'_germ (𝒜 := UniversalGrading.{0} 1) _ c hc (a3k_Sg hg)

theorem a3k_isUnit_germ_Sg {g : UniversalRing.{0} 1} (hg : g ∈ UniversalGrading.{0} 1 1)
    (c : g3c_P 1) (hc : c ∈ Proj.basicOpen (UniversalGrading.{0} 1) (X 0)) :
    IsUnit ((g3c_P 1).presheaf.germ _ c hc (a3k_Sg hg)) ↔ g ∉ c.asHomogeneousIdeal := by
  refine (MulEquiv.isUnit_map (Proj.stalkIso' (UniversalGrading.{0} 1) c).toMulEquiv).symm.trans ?_
  change IsUnit (Proj.stalkIso' _ c _) ↔ _
  rw [a3k_germ_Sg, ← HomogeneousLocalization.isUnit_iff_isUnit_val]
  rw [HomogeneousLocalization.Away.isLocalizationElem, HomogeneousLocalization.Away.mk]
  erw [HomogeneousLocalization.map_mk, HomogeneousLocalization.val_mk]
  rw [Localization.mk_eq_mk']
  erw [IsLocalization.AtPrime.isUnit_mk'_iff]
  simp only [pow_one]
  rfl

/-- The coordinate `t₁ = s₁/s₀` over `D₊(s₀)`.
Source: Hartshorne, *Algebraic Geometry*, II, Proposition 2.5. -/
def a3k_S1 : Γ(g3c_P 1, Proj.basicOpen (UniversalGrading.{0} 1) (X 0)) := a3k_Sg (a3m_X_mem 1)

example : a3k_S1 = a3k_Sg (a3m_X_mem 1) := rfl

theorem a3k_Sg_sub : a3k_Sg a3m_g_mem = a3k_S1 - 1 := by
  rw [a3k_S1, a3k_Sg, a3k_Sg, a3m_elem_g, a3m_elem_X1, map_sub, map_one]

/-- Over `t₁ = 0` the germ of `t₁` lies in the maximal ideal. -/
theorem a3k_germ_S1_mem_Z0 (c : g3c_P 1) (h0 : c ∈ a3m_Z0)
    (hc : c ∈ Proj.basicOpen (UniversalGrading.{0} 1) (X 0)) :
    (g3c_P 1).presheaf.germ _ c hc a3k_S1 ∈ IsLocalRing.maximalIdeal _ := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, a3k_S1, a3k_isUnit_germ_Sg, not_not]
  exact (a3m_mem_Z0 c h0).1

/-- Over `t₁ = 1` the germ of `t₁ - 1` lies in the maximal ideal. -/
theorem a3k_germ_S1_mem_Zinf (c : g3c_P 1) (h1 : c ∈ a3m_Zinf)
    (hc : c ∈ Proj.basicOpen (UniversalGrading.{0} 1) (X 0)) :
    (g3c_P 1).presheaf.germ _ c hc a3k_S1 - 1 ∈ IsLocalRing.maximalIdeal _ := by
  rw [← map_one ((g3c_P 1).presheaf.germ _ c hc).hom, ← map_sub, ← a3k_Sg_sub,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, a3k_isUnit_germ_Sg, not_not]
  obtain ⟨q, rfl, hq⟩ := h1
  have := (a3m_chart0_mem_basicOpen q _ a3m_g_mem).not.2 (by rw [a3m_elem_g, not_not]; exact hq)
  rwa [Proj.mem_basicOpen, not_not] at this

theorem a3k_Z0_mem_basicOpen (c : g3c_P 1) (h0 : c ∈ a3m_Z0) :
    c ∈ Proj.basicOpen (UniversalGrading.{0} 1) (X 0) := by
  obtain ⟨q, rfl, -⟩ := h0
  exact a3k_mem_basicOpen_X0 _ ⟨q, rfl⟩

theorem a3k_Zinf_mem_basicOpen (c : g3c_P 1) (h1 : c ∈ a3m_Zinf) :
    c ∈ Proj.basicOpen (UniversalGrading.{0} 1) (X 0) := by
  obtain ⟨q, rfl, -⟩ := h1
  exact a3k_mem_basicOpen_X0 _ ⟨q, rfl⟩

end coordinate

section divT
variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProper X.hom]

theorem a3k_serreMult_symm (Y : Scheme.{0}) (z u v : Y) :
    a3i_serreMult Y z u v = a3i_serreMult Y z v u := by
  unfold a3i_serreMult a3i_torModule
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [a3l_length_tor_symm]

theorem a3k_coheight_genericPoint (Y : Scheme.{0}) [IsIntegral Y] :
    coheight (genericPoint Y) = 0 :=
  Order.coheight_eq_zero.mpr fun y _ => genericPoint_specializes y

omit [IsProper X.hom] in
/-- `X × ℙ¹` dominates `ℙ¹`. -/
theorem a3k_hη : a3n_h X (genericPoint (a3n_T X).left) = genericPoint (g3c_P 1) :=
  a3k_h_eq_generic X (genericPoint_specializes (a3n_σ X 0 (genericPoint X.left)))
    (genericPoint_specializes (a3n_σ X 1 (genericPoint X.left)))

/-- `[div t]` on `X × ℙ¹`.
Source: Fulton, *Intersection Theory*, second edition, §1.6 (the coordinate `t` on `X × ℙ¹`). -/
abbrev a3k_cycT : AlgebraicCycle (a3n_T X).left ℚ :=
  a3o_cyc X (genericPoint (a3n_T X).left) (a3k_hη X)

example : a3k_cycT X = a3o_cyc X (genericPoint (a3n_T X).left) (a3k_hη X) := rfl

omit [IsProper X.hom] in
theorem a3k_coheight_σ_generic (c : ℂ) :
    coheight (a3n_σ X c (genericPoint X.left)) = 1 := by
  rw [a3n_coheight_σ, a3k_coheight_genericPoint, zero_add]

/-- `[div t]` lives on `X × {0}` and `X × {1}`. -/
theorem a3k_cycT_supp (d : (a3n_T X).left) (hd : a3k_cycT X d ≠ 0) :
    d = a3n_σ X 0 (genericPoint X.left) ∨ d = a3n_σ X 1 (genericPoint X.left) := by
  obtain ⟨D, hD, hD1, -⟩ := a3z_principalCycle_ne_zero (a3n_T X).left _ _
    (a3o_φ_ne_zero X _ (a3k_hη X)) d hd
  have hcoh : coheight d = 1 := by
    rw [← hD, (a3y_coheight_eq_one_iff (a3n_T X) _ D).1 hD1, a3k_coheight_genericPoint, zero_add]
  have key : ∀ (c : ℂ) (e : X.left), a3n_σ X c e = d → e = genericPoint X.left := by
    intro c e he
    rw [← he, a3n_coheight_σ] at hcoh
    have h0 : coheight e = 0 := by
      have hne := a3c_coheight_ne_top X.left e
      obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hne
      rw [← hn] at hcoh ⊢
      norm_cast at hcoh ⊢
      omega
    have hmax : IsMax e := Order.coheight_eq_zero.1 h0
    have h1 : e ≤ genericPoint X.left := by
      rw [Scheme.le_iff_specializes]; exact genericPoint_specializes e
    have h2 := hmax h1
    rw [Scheme.le_iff_specializes] at h1 h2
    exact (h2.antisymm h1).eq
  rcases a3o_cyc_supp X _ (a3k_hη X) d hd with ⟨e, he⟩ | ⟨e, he⟩
  · exact Or.inl (by rw [← he, key 0 e he])
  · exact Or.inr (by rw [← he, key 1 e he])

/-- The coefficient of `[div t]` along `X × {0}` is positive. -/
theorem a3k_cycT_pos : 0 < a3k_cycT X (a3n_σ X 0 (genericPoint X.left)) := by
  obtain ⟨D, hD⟩ := a3z_exists_pt (genericPoint (a3n_T X).left)
    (genericPoint_specializes (a3n_σ X 0 (genericPoint X.left)))
  have hD1 : coheight D = 1 := by
    rw [a3y_coheight_eq_one_iff (a3n_T X), hD, a3k_coheight_genericPoint, zero_add,
      a3k_coheight_σ_generic]
  have e1 : a3k_cycT X (a3n_σ X 0 (genericPoint X.left)) =
      ((cycleComponent (a3n_T X).left _).ord (a3o_φ X _ (a3k_hη X)) D : ℚ) := by
    rw [← hD]
    exact a3y_principalCycle_apply _ _ _ (a3o_φ_ne_zero X _ (a3k_hη X)) D
  rw [e1]
  have hZ0 : a3n_h X (cycleComponentι (a3n_T X).left _ D) ∈ a3m_Z0 := by
    rw [hD]; exact a3n_h_σ0 X _
  obtain ⟨a, ha, hat⟩ := a3m_P1curve.zero _ hZ0
  exact_mod_cast a3m_ord_pullbackFF_pos (cycleComponentι (a3n_T X).left _ ≫ a3n_h X)
    (a3o_hgen X _ (a3k_hη X)) a3m_P1curve.t a3m_P1curve.t_ne_zero D hD1 a ha hat

omit [IsProper X.hom] in
/-- The components of `closure {u} ∩ closure {D}` for the generic point `u` of `T`. -/
theorem a3k_comps_generic (D : (a3n_T X).left) :
    a3y_comps (genericPoint (a3n_T X).left) D = {D} := by
  ext z
  rw [Set.mem_singleton_iff]
  constructor
  · intro hz
    obtain ⟨-, hDz, hmin⟩ := a3y_comps_spec _ _ hz
    exact (hmin D (genericPoint_specializes D) specializes_rfl hDz).symm
  · intro h
    subst h
    obtain ⟨z', hz', hz'D⟩ := a3y_exists_comp (genericPoint (a3n_T X).left) z
      (genericPoint_specializes z) specializes_rfl
    obtain ⟨-, hDz', -⟩ := a3y_comps_spec _ _ hz'
    rwa [(hz'D.antisymm hDz').eq] at hz'

open Classical in
/-- **`[div (t|_D)] = [div t] · [D]`** on `X × ℙ¹` for `D` dominating `ℙ¹`: the cycle form of
Fulton, Theorem 2.4, for `t` on `X × ℙ¹` met with `D`.
Source: Fulton, *Intersection Theory*, second edition, Theorem 2.4 and §1.6. -/
theorem a3k_cyc_eq_intersect (D : (a3n_T X).left) (hD : a3n_h X D = genericPoint (g3c_P 1)) :
    a3o_cyc X D hD = a3i_intersect (a3n_T X).left (a3k_cycT X)
      (Function.locallyFinsuppWithin.single D 1) := by
  set η := genericPoint (a3n_T X).left
  have hcomps := a3k_comps_generic X D
  have hWV : a3i_MeetProperly (a3n_T X).left η D := by
    intro w hw
    have hz : (ccm3_primeIdeal (a3n_T X).left η ⊔ ccm3_primeIdeal (a3n_T X).left D).subschemeι w ∈
        a3y_comps η D := ⟨w, hw, rfl⟩
    rw [hcomps, Set.mem_singleton_iff] at hz
    rw [hz, a3k_coheight_genericPoint, zero_add]
  have hDd : ∀ d, a2_principalCycle (a3n_T X).left ℚ η (a3o_φ X η (a3k_hη X)) d ≠ 0 →
      a3i_MeetProperly (a3n_T X).left d D := by
    intro d hd
    have hσ : ∀ c : ℂ, (c = 0 ∨ c = 1) → d = a3n_σ X c (genericPoint X.left) →
        a3i_MeetProperly (a3n_T X).left d D := by
      intro c hc hdc w hw
      have hz : (ccm3_primeIdeal (a3n_T X).left d ⊔ ccm3_primeIdeal (a3n_T X).left D).subschemeι w ∈
          a3y_comps d D := ⟨w, hw, rfl⟩
      set z := (ccm3_primeIdeal (a3n_T X).left d ⊔ ccm3_primeIdeal (a3n_T X).left D).subschemeι w
      obtain ⟨hdz, hDz, -⟩ := a3y_comps_spec _ _ hz
      have hzr : z ∈ Set.range (a3n_σ X c) := a3n_mem_range_σ_of_specializes X c (hdc ▸ hdz)
      have hne : D ≠ z := fun h => a3k_not_mem_range_σ X hD c hc (h ▸ hzr)
      have hlt := Order.add_one_le_of_lt (a3y_coheight_lt hDz hne)
      have hle := a3k_coheight_comps_le X hz
      rw [hdc, a3k_coheight_σ_generic] at hle ⊢
      rw [add_comm] at hlt
      exact le_antisymm hle hlt
    rcases a3k_cycT_supp X d hd with h | h
    · exact hσ 0 (Or.inl rfl) h
    · exact hσ 1 (Or.inr rfl) h
  let ψ : (z : (a3n_T X).left) → (cycleComponent (a3n_T X).left z).functionField :=
    fun z => if h : a3n_h X z = genericPoint (g3c_P 1) then a3o_φ X z h else 0
  have hψD : ψ D = a3o_φ X D hD := by
    simp only [ψ]
    split_ifs with h
    · rfl
    · exact absurd hD h
  have hψ : ∀ z ∈ a3y_comps η D, a3z_IsRestriction η (a3o_φ X η (a3k_hη X)) z (ψ z) := by
    intro z hz
    rw [hcomps, Set.mem_singleton_iff] at hz
    subst hz
    rw [hψD]
    obtain ⟨zW, hzW⟩ := a3z_exists_pt η (genericPoint_specializes z)
    have h0 : a3n_h X z ∉ a3m_Z0 := by rw [hD]; exact a3k_generic_not_mem_Z0
    have h1 : a3n_h X z ∉ a3m_Zinf := by rw [hD]; exact a3k_generic_not_mem_Zinf
    obtain ⟨a₀, ha₀, hat⟩ := a3m_P1curve.unit _ h0 h1
    refine ⟨zW, hzW, (a3n_h X).stalkMap z a₀, 1, ?_, ?_, ?_, ?_⟩
    · rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
      exact ha₀.map _
    · rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
      exact isUnit_one
    · rw [map_one, mul_one]
      exact a3o_germ_pullback X η (a3k_hη X) z zW hzW a₀ hat
    · rw [map_one, mul_one]
      exact a3o_germ_pullback X z hD z _ (a3m_cycleComponentι_genericPoint _ z) a₀ hat
  have e2 := a3z_principal_intersect (a3n_T X) η D hWV _ (a3o_φ_ne_zero X η (a3k_hη X)) hDd ψ hψ
  symm
  refine e2.trans ?_
  have hfin : (a3y_comps_finite η D).toFinset = {D} := by
    ext z
    rw [Set.Finite.mem_toFinset, Finset.mem_singleton, show η = genericPoint _ from rfl, hcomps,
      Set.mem_singleton_iff]
  rw [hfin, Finset.sum_singleton, hψD, a3k_serreMult_symm, a3c_serreMult_self_genericPoint]
  ext x
  simp [Function.locallyFinsuppWithin.mapRange_apply, a3o_cyc]

end divT

end HodgeLean.Adapters
