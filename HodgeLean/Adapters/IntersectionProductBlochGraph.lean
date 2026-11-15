import HodgeLean.Adapters.IntersectionProductBlochLine

/-! # Rational equivalence through `X × ℙ¹`: every cycle rationally equivalent to zero is a
boundary

Stage A3.3. Fulton's Proposition 1.6 in the direction needed here: for a subvariety
`W = closure {w}` of `X` and a nonzero rational function `θ` on `W`, `[div θ]` is the boundary
`a3k_bd X Z` of a chain `Z` on `T = X × ℙ¹` whose members dominate `ℙ¹` (`a3k_principal_mem_bd`),
so every cycle rationally equivalent to zero is such a boundary (`a3k_ratAll_bd`).

The chain is read off a rational function on `W × ℙ¹ = closure {b_w}` (`b_w = a3n_b X w`): with
the coordinate `t₁` of `ℙ¹` and the pull-back of `θ`, `F = θ + (1 - θ) t₁` is a unit along
`W × {0}` with restriction `θ` and along `W × {1}` with restriction `1`. The cycle form of
Fulton, Theorem 2.4 (`a3z_principal_intersect`) gives `[div F] · [X × {0}] = [div θ]` (on
`W × {0} ≅ W`) and `[div F] · [X × {1}] = 0`. Writing `[div t] = m₀ [X × {0}] + m₁ [X × {1}]` on
`T` with `m₀ > 0` (`a3k_cycT_pos`) and using `[div (t|_D)] = [div t] · [D]` for every component
`D` of `div F` dominating `ℙ¹` (`a3k_cyc_eq_intersect`), the chain `Z = m₀⁻¹ Σ_D ord_D(F) [D]`
has boundary `[div θ]`; the components of `div F` not dominating `ℙ¹` do not meet `X × {0}` or
`X × {1}`. No normality of `W` is used.

Source: Fulton, *Intersection Theory*, second edition, Proposition 1.6, Theorem 2.4 and §1.6;
Serre, *Algèbre locale, multiplicités*, Chapitre V. HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Order
open AlgebraicGeometry.ComplexProjectiveSpace HodgeLean.Foundations
open scoped MonoidalCategory Pointwise

set_option backward.isDefEq.respectTransparency false

namespace HodgeLean.Adapters

attribute [local instance] MvPolynomial.gradedAlgebra

section general
variable {Y : Scheme.{0}}

/-- The intersection product is symmetric. -/
theorem a3k_intersectPrime_symm (u v : Y) :
    a3i_intersectPrime Y u v = a3i_intersectPrime Y v u := by
  classical
  have key : ∀ J K : Y.IdealSheafData, J = K → ∀ m₁ m₂ : Y → ℚ, m₁ = m₂ →
      (∑ᶠ y : J.subscheme, if closure ({y} : Set J.subscheme) ∈ irreducibleComponents J.subscheme
        then Function.locallyFinsuppWithin.single (J.subschemeι y) (m₁ (J.subschemeι y)) else 0) =
      ∑ᶠ y : K.subscheme, if closure ({y} : Set K.subscheme) ∈ irreducibleComponents K.subscheme
        then Function.locallyFinsuppWithin.single (K.subschemeι y) (m₂ (K.subschemeι y)) else 0 := by
    rintro J K rfl m _ rfl
    rfl
  exact key _ _ (sup_comm _ _) (fun z => ((a3i_serreMult Y z u v : ℤ) : ℚ))
    (fun z => ((a3i_serreMult Y z v u : ℤ) : ℚ)) (funext fun z => by rw [a3k_serreMult_symm])

theorem a3k_intersect_symm [IsNoetherian Y] (c d : AlgebraicCycle Y ℚ) :
    a3i_intersect Y c d = a3i_intersect Y d c := by
  classical
  let s := (a3c_support_finite c).toFinset
  let t := (a3c_support_finite d).toFinset
  have hs : ∀ u ∉ s, c u = 0 := fun u hu => by simpa [s] using hu
  have ht : ∀ v ∉ t, d v = 0 := fun v hv => by simpa [t] using hv
  rw [a3c_intersect_eq_sum Y c d s t hs ht, a3c_intersect_eq_sum Y d c t s ht hs, Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun u _ => ?_
  rw [a3k_intersectPrime_symm u v]
  ext x
  simp only [Function.locallyFinsuppWithin.mapRange_apply]
  ring

/-- Push-forward commutes with rational multiples. -/
theorem a3k_pushforward_smul {Y' : Scheme.{0}} [IsNoetherian Y] (f : Y ⟶ Y') [QuasiCompact f]
    (r : ℚ) (c : AlgebraicCycle Y ℚ) :
    a1p_pushforward f (a3m_smul r c) = a3m_smul r (a1p_pushforward f c) := by
  classical
  ext y
  set t := (a3m_support_finite c).toFinset.filter (fun x => f x = y)
  have h₁ : ∀ c' : AlgebraicCycle Y ℚ, (∀ x, c x = 0 → c' x = 0) →
      f ⁻¹' {y} ∩ Function.support c' ⊆ t := by
    intro c' hc' x ⟨hx, hxc⟩
    simp only [t, Finset.coe_filter, Set.Finite.mem_toFinset, Function.mem_support,
      Set.mem_ofPred_eq]
    exact ⟨fun h => hxc (hc' x h), hx⟩
  have h₂ : (t : Set Y) ⊆ f ⁻¹' {y} := fun x hx => by
    simp only [t, Finset.coe_filter, Set.mem_ofPred_eq] at hx
    exact hx.2
  rw [a3m_smul_apply, a1p_pushforward_apply_eq_sum f _ y t
      (h₁ _ fun x hx => by rw [a3m_smul_apply, hx, mul_zero]) h₂,
    a1p_pushforward_apply_eq_sum f c y t (h₁ c fun _ h => h) h₂, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [a3m_smul_apply, mul_assoc]

theorem a3k_pushforward_zero {Y' : Scheme.{0}} (f : Y ⟶ Y') [QuasiCompact f] :
    a1p_pushforward f (0 : AlgebraicCycle Y ℚ) = 0 := by
  have h := a1p_pushforward_add f (0 : AlgebraicCycle Y ℚ) 0
  rw [add_zero] at h
  exact left_eq_add.mp h

theorem a3k_pushforward_sum {Y' : Scheme.{0}} (f : Y ⟶ Y') [QuasiCompact f] {ι : Type*}
    (s : Finset ι) (F : ι → AlgebraicCycle Y ℚ) :
    a1p_pushforward f (∑ i ∈ s, F i) = ∑ i ∈ s, a1p_pushforward f (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h := a1p_pushforward_add f (0 : AlgebraicCycle Y ℚ) 0
    rw [add_zero] at h
    simpa using h
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, a1p_pushforward_add, ih]

/-- Restrictions to the function field of `closure {z}` are onto. -/
theorem a3k_germZ_surjective (z : Y) : Function.Surjective (a3z_germZ z) := by
  have key : ∀ (T : Y) (h : cycleComponentι Y z (genericPoint (cycleComponent Y z)) = T),
      Function.Surjective (a3y_germ z (genericPoint (cycleComponent Y z)) h) := by
    intro T h
    subst h
    intro φ
    obtain ⟨a, ha⟩ :=
      (cycleComponentι Y z).stalkMap_surjective (genericPoint (cycleComponent Y z)) φ
    refine ⟨a, ?_⟩
    rw [a3y_germ_self, ha]
    change ((cycleComponent Y z).presheaf.stalkSpecializes _) φ = φ
    rw [TopCat.Presheaf.stalkSpecializes_refl]
    rfl
  exact key _ _

/-- The divisor of a rational function that is a unit at `z` vanishes at `z`. -/
theorem a3k_principalCycle_eq_zero_of_unitAt [IsNoetherian Y] (w : Y)
    (φ : (cycleComponent Y w).functionField) (hφ : φ ≠ 0) (z : Y) (h : a3z_UnitAt w φ z) :
    a2_principalCycle Y ℚ w φ z = 0 := by
  by_contra hne
  obtain ⟨D, hD, hD1, heq⟩ := a3z_principalCycle_ne_zero Y w φ hφ z hne
  obtain ⟨zW, hz, a, b, ha, hb, hab⟩ := h
  have hzD : zW = D := (cycleComponentι Y w).isClosedEmbedding.injective (hz.trans hD.symm)
  subst hzD
  have hunit : ∀ r : Y.presheaf.stalk z, r ∉ IsLocalRing.maximalIdeal _ →
      (cycleComponent Y w).ord (a3y_germ w zW hz r) zW = 0 := by
    intro r hr
    subst hz
    rw [a3y_germ_self]
    refine a3m_ord_algebraMap_of_isUnit zW _ ?_
    have hr' : IsUnit r := by
      rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hr
    exact hr'.map ((cycleComponentι Y w).stalkMap zW).hom
  have hb0 : a3y_germ w zW hz b ≠ 0 := by
    intro h0
    rw [a3y_germ_eq_zero_iff] at h0
    exact hb (a3z_stalkIdeal_le_maximalIdeal w (hz ▸ a3z_specializes_pt w zW) h0)
  have hord := Scheme.ord_mul (x := zW) hφ hb0
  rw [← hab, hunit a ha, hunit b hb, add_zero] at hord
  exact hne (by rw [heq, ← hord]; simp)

/-- The divisor of `1` is zero. -/
theorem a3k_principalCycle_one [IsNoetherian Y] (w : Y) : a2_principalCycle Y ℚ w 1 = 0 := by
  ext z
  by_cases hz : z ∈ Set.range (cycleComponentι Y w)
  · obtain ⟨D, rfl⟩ := hz
    rw [a3y_principalCycle_apply _ _ _ one_ne_zero]
    have h := Scheme.ord_mul (x := D) (one_ne_zero (α := (cycleComponent Y w).functionField))
      one_ne_zero
    rw [mul_one, left_eq_add] at h
    simp [h]
  · rw [a3y_principalCycle_apply_of_not_mem _ _ _ _ hz]
    rfl

end general

section herbrandRetract
universe u
variable {A B : Type u} [CommRing A] [CommRing B]

theorem a3k_kerSMul_eq_bot (I : Ideal A) [I.IsPrime] (r : A) (hr : r ∉ I) :
    a3e_kerSMul r (A ⧸ I) = ⊥ := by
  rw [eq_bot_iff]
  intro m hm
  obtain ⟨m, rfl⟩ := Ideal.Quotient.mk_surjective m
  rw [LinearMap.mem_ker, LinearMap.lsmul_apply, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
    ← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hm
  rw [Submodule.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
  exact (Ideal.IsPrime.mem_or_mem ‹_› hm).resolve_left hr

/-- The Herbrand difference of `r ∉ I` on `A ⧸ I`, `I` prime, is the length of
`A ⧸ (r, I)`. -/
theorem a3k_herbrand_quot (I : Ideal A) [I.IsPrime] (r : A) (hr : r ∉ I) :
    a3e_herbrand r (A ⧸ I) = ((Module.length A (A ⧸ (Ideal.span {r} ⊔ I))).toNat : ℤ) := by
  have e₁ : QuotSMulTop r (A ⧸ I) ≃ₗ[A] A ⧸ (Ideal.span {r} ⊔ I) :=
    (Submodule.quotEquivOfEq (r • (⊤ : Submodule A (A ⧸ I)))
      ((Ideal.span {r}) • (⊤ : Submodule A (A ⧸ I)))
      (Submodule.ideal_span_singleton_smul r ⊤).symm).trans (a3c_quotSMulEquiv _ _)
  rw [a3e_herbrand, e₁.length_eq, a3k_kerSMul_eq_bot I r hr, Module.length_bot]
  simp

/-- Herbrand differences along a ring map with a retraction. -/
theorem a3k_herbrand_retract (f : A →+* B) (g : B →+* A) (hg : ∀ a, g (f a) = a)
    (𝔭 : Ideal A) [𝔭.IsPrime] (a : A) (ha : a ∉ 𝔭) :
    a3e_herbrand (f a) (B ⧸ 𝔭.comap g) = a3e_herbrand a (A ⧸ 𝔭) := by
  have hsurj : Function.Surjective g := fun a => ⟨f a, hg a⟩
  have hfa : f a ∉ 𝔭.comap g := by rwa [Ideal.mem_comap, hg]
  rw [a3k_herbrand_quot _ _ hfa, a3k_herbrand_quot _ _ ha]
  set J := Ideal.span {f a} ⊔ 𝔭.comap g
  have hJ : RingHom.ker g ≤ J := fun b hb =>
    Ideal.mem_sup_right (Ideal.mem_comap.2 (by rw [RingHom.mem_ker.1 hb]; exact 𝔭.zero_mem))
  have hmap : J.map g = Ideal.span {a} ⊔ 𝔭 := by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton, hg,
      Ideal.map_comap_of_surjective g hsurj]
  have hkill : ∀ b ∈ RingHom.ker g, ∀ x : ModuleCat.of B (B ⧸ J), b • x = 0 := by
    intro b hb x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk J (b * x) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact J.mul_mem_right _ (hJ hb)
  have h1 := a3f_length_eq f g hg (ModuleCat.of B (B ⧸ J)) hkill
  have h2 := (a3f_quotEquiv f g hg J hJ).toLinearEquiv.length_eq
  change Module.length B (B ⧸ J) = _ at h1
  rw [h1, h2]
  change ((Module.length A (A ⧸ J.map g)).toNat : ℤ) = _
  rw [hmap]

end herbrandRetract

section bw
variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
  (w : X.left)

omit [IsProjective X.hom] in
theorem a3k_b_σ (c : ℂ) : a3n_b X w ⤳ a3n_σ X c w := by
  rw [a3n_b_specializes_iff, a3n_q_σ_apply]

omit [IsProjective X.hom] in
theorem a3k_h_b : a3n_h X (a3n_b X w) = genericPoint (g3c_P 1) :=
  a3k_h_eq_generic X (a3k_b_σ X w 0) (a3k_b_σ X w 1)

omit [Smooth X.hom] [IsProjective X.hom] in
theorem a3k_σ_generic_specializes (c : ℂ) (x : X.left) :
    a3n_σ X c (genericPoint X.left) ⤳ a3n_σ X c x :=
  (genericPoint_specializes x).map (a3n_σ X c).continuous

omit [IsProjective X.hom] in
theorem a3k_mem_comps_b_σ (c : ℂ) {z : (a3n_T X).left}
    (hz : z ∈ a3y_comps (a3n_b X w) (a3n_σ X c (genericPoint X.left))) : z = a3n_σ X c w := by
  obtain ⟨hbz, hsz, hmin⟩ := a3y_comps_spec _ _ hz
  obtain ⟨e, rfl⟩ := a3n_mem_range_σ_of_specializes X c hsz
  have hwe : w ⤳ e := by rwa [a3n_b_specializes_iff, a3n_q_σ_apply] at hbz
  exact (hmin _ (a3k_b_σ X w c) (a3k_σ_generic_specializes X c w)
    (hwe.map (a3n_σ X c).continuous)).symm

omit [IsProjective X.hom] in
/-- `(W × ℙ¹) ∩ (X × {c}) = W × {c}`. -/
theorem a3k_comps_b_σ (c : ℂ) :
    a3y_comps (a3n_b X w) (a3n_σ X c (genericPoint X.left)) = {a3n_σ X c w} := by
  ext z
  rw [Set.mem_singleton_iff]
  refine ⟨a3k_mem_comps_b_σ X w c, ?_⟩
  rintro rfl
  obtain ⟨z, hz, -⟩ := a3y_exists_comp _ _ (a3k_b_σ X w c) (a3k_σ_generic_specializes X c w)
  rwa [a3k_mem_comps_b_σ X w c hz] at hz

/-- `W × ℙ¹` has the codimension of `W`. -/
theorem a3k_coheight_b : coheight (a3n_b X w) = coheight w := by
  refine le_antisymm (a3k_coheight_b_le X w) ?_
  have hz : a3n_σ X 0 w ∈ a3y_comps (a3n_b X w) (a3n_σ X 0 (genericPoint X.left)) := by
    rw [a3k_comps_b_σ X w 0]; exact Set.mem_singleton _
  have h := a3k_coheight_comps_le X hz
  rw [a3n_coheight_σ, a3k_coheight_σ_generic] at h
  exact (WithTop.add_le_add_iff_right (by decide : (1 : ℕ∞) ≠ ⊤)).1 h

theorem a3k_meet_b_σ (c : ℂ) :
    a3i_MeetProperly (a3n_T X).left (a3n_b X w) (a3n_σ X c (genericPoint X.left)) := by
  intro v hv
  have hz : (ccm3_primeIdeal (a3n_T X).left (a3n_b X w) ⊔ ccm3_primeIdeal (a3n_T X).left
      (a3n_σ X c (genericPoint X.left))).subschemeι v ∈
        a3y_comps (a3n_b X w) (a3n_σ X c (genericPoint X.left)) := ⟨v, hv, rfl⟩
  rw [a3k_mem_comps_b_σ X w c hz, a3n_coheight_σ, a3k_coheight_b, a3k_coheight_σ_generic]

omit [IsProjective X.hom] in
theorem a3k_serreMult_b_σ (c : ℂ) :
    a3i_serreMult (a3n_T X).left (a3n_σ X c w) (a3n_b X w)
      (a3n_σ X c (genericPoint X.left)) = 1 := by
  rw [a3k_serreMult_symm, a3n_serreMult_σ X c w (genericPoint X.left) w
    (genericPoint_specializes w) specializes_rfl, a3k_serreMult_symm,
    a3c_serreMult_self_genericPoint]

end bw

section F
variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
  (w : X.left)

theorem a3k_generic_mem_basicOpen :
    genericPoint (g3c_P 1) ∈ Proj.basicOpen (UniversalGrading.{0} 1) (MvPolynomial.X 0) :=
  a3k_mem_basicOpen_X0 _ ⟨a3m_bot1, by rw [a3m_genericPoint_P1]; rfl⟩

/-- A local homomorphism maps the maximal ideal into the maximal ideal. -/
theorem a3k_map_mem_maximalIdeal {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R]
    [IsLocalRing S] (φ : R →+* S) [IsLocalHom φ] {r : R} (hr : r ∈ IsLocalRing.maximalIdeal R) :
    φ r ∈ IsLocalRing.maximalIdeal S := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hr ⊢
  exact fun hu => hr (isUnit_of_map_unit φ r hu)

/-- The germ of `t₁` at a point of `X × ℙ¹` over `D₊(s₀)`.
Source: Hartshorne, *Algebraic Geometry*, II, §2 (stalk maps). -/
def a3k_t1 (τ : (a3n_T X).left)
    (hτ : a3n_h X τ ∈ Proj.basicOpen (UniversalGrading.{0} 1) (MvPolynomial.X 0)) :
    (a3n_T X).left.presheaf.stalk τ :=
  (a3n_h X).stalkMap τ ((g3c_P 1).presheaf.germ _ (a3n_h X τ) hτ a3k_S1)

example (τ : (a3n_T X).left)
    (hτ : a3n_h X τ ∈ Proj.basicOpen (UniversalGrading.{0} 1) (MvPolynomial.X 0)) :
    (a3n_T X).left.presheaf.stalk τ := a3k_t1 X τ hτ

omit [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] in
theorem a3k_t1_specializes {τ τ' : (a3n_T X).left} (h : τ' ⤳ τ)
    (hτ : a3n_h X τ ∈ Proj.basicOpen (UniversalGrading.{0} 1) (MvPolynomial.X 0))
    (hτ' : a3n_h X τ' ∈ Proj.basicOpen (UniversalGrading.{0} 1) (MvPolynomial.X 0)) :
    (a3n_T X).left.presheaf.stalkSpecializes h (a3k_t1 X τ hτ) = a3k_t1 X τ' hτ' := by
  rw [a3k_t1, a3k_t1, ← Scheme.Hom.stalkSpecializes_stalkMap_apply]
  congr 1
  exact TopCat.Presheaf.germ_stalkSpecializes_apply (g3c_P 1).presheaf hτ _ a3k_S1

omit [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] in
theorem a3k_t1_σ0
    (hτ : a3n_h X (a3n_σ X 0 w) ∈ Proj.basicOpen (UniversalGrading.{0} 1) (MvPolynomial.X 0)) :
    a3k_t1 X (a3n_σ X 0 w) hτ ∈ IsLocalRing.maximalIdeal _ :=
  a3k_map_mem_maximalIdeal _ (a3k_germ_S1_mem_Z0 _ (a3n_h_σ0 X w) hτ)

omit [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] in
theorem a3k_t1_σ1
    (hτ : a3n_h X (a3n_σ X 1 w) ∈ Proj.basicOpen (UniversalGrading.{0} 1) (MvPolynomial.X 0)) :
    a3k_t1 X (a3n_σ X 1 w) hτ - 1 ∈ IsLocalRing.maximalIdeal _ := by
  have h := a3k_map_mem_maximalIdeal ((a3n_h X).stalkMap (a3n_σ X 1 w)).hom
    (a3k_germ_S1_mem_Zinf _ (a3n_h_σ1 X w) hτ)
  rwa [map_sub, map_one] at h

/-- The pull-back to `𝒪_{X×ℙ¹, b_w}` of an element of `𝒪_{X,w}`.
Source: Hartshorne, *Algebraic Geometry*, II, §2 (stalk maps). -/
def a3k_qb (θ : X.left.presheaf.stalk w) : (a3n_T X).left.presheaf.stalk (a3n_b X w) :=
  (a3n_q X).left.stalkMap (a3n_b X w)
    (X.left.presheaf.stalkSpecializes (specializes_of_eq (a3n_q_b X w)) θ)

example (θ : X.left.presheaf.stalk w) : (a3n_T X).left.presheaf.stalk (a3n_b X w) :=
  a3k_qb X w θ

omit [IsProjective X.hom] in
theorem a3k_f_specializes (c : ℂ) (θ : X.left.presheaf.stalk w) :
    (a3n_T X).left.presheaf.stalkSpecializes (a3k_b_σ X w c) (a3n_f X c w θ) = a3k_qb X w θ := by
  change (a3n_T X).left.presheaf.stalkSpecializes _ ((a3n_q X).left.stalkMap (a3n_σ X c w)
    ((X.left.presheaf.stalkCongr (.of_eq (a3n_qσ X c w))).inv θ)) = _
  rw [← Scheme.Hom.stalkSpecializes_stalkMap_apply, a3k_qb]
  congr 1
  dsimp only [TopCat.Presheaf.stalkCongr]
  rw [TopCat.Presheaf.stalkSpecializes_comp_apply]

omit [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] in
theorem a3k_mem_basicOpen_σ (c : ℂ) (hc : c = 0 ∨ c = 1) :
    a3n_h X (a3n_σ X c w) ∈ Proj.basicOpen (UniversalGrading.{0} 1) (MvPolynomial.X 0) := by
  rcases hc with rfl | rfl
  · exact a3k_Z0_mem_basicOpen _ (a3n_h_σ0 X w)
  · exact a3k_Zinf_mem_basicOpen _ (a3n_h_σ1 X w)

omit [IsProjective X.hom] in
theorem a3k_mem_basicOpen_b :
    a3n_h X (a3n_b X w) ∈ Proj.basicOpen (UniversalGrading.{0} 1) (MvPolynomial.X 0) := by
  rw [a3k_h_b X w]; exact a3k_generic_mem_basicOpen

/-- `θ + (1 - θ) t₁` at `σ_c(w)`.
Source: Fulton, *Intersection Theory*, second edition, §1.6. -/
def a3k_a (c : ℂ) (hc : c = 0 ∨ c = 1) (θ : X.left.presheaf.stalk w) :
    (a3n_T X).left.presheaf.stalk (a3n_σ X c w) :=
  a3n_f X c w θ + (1 - a3n_f X c w θ) * a3k_t1 X (a3n_σ X c w) (a3k_mem_basicOpen_σ X w c hc)

example (θ : X.left.presheaf.stalk w) : (a3n_T X).left.presheaf.stalk (a3n_σ X 0 w) :=
  a3k_a X w 0 (Or.inl rfl) θ

/-- `θ + (1 - θ) t₁` at `b_w`.
Source: Fulton, *Intersection Theory*, second edition, §1.6. -/
def a3k_A (θ : X.left.presheaf.stalk w) : (a3n_T X).left.presheaf.stalk (a3n_b X w) :=
  a3k_qb X w θ + (1 - a3k_qb X w θ) * a3k_t1 X (a3n_b X w) (a3k_mem_basicOpen_b X w)

example (θ : X.left.presheaf.stalk w) : (a3n_T X).left.presheaf.stalk (a3n_b X w) :=
  a3k_A X w θ

omit [IsProjective X.hom] in
theorem a3k_a_specializes (c : ℂ) (hc : c = 0 ∨ c = 1) (θ : X.left.presheaf.stalk w) :
    (a3n_T X).left.presheaf.stalkSpecializes (a3k_b_σ X w c) (a3k_a X w c hc θ) =
      a3k_A X w θ := by
  rw [a3k_a, a3k_A, map_add, map_mul, map_sub, map_one, a3k_f_specializes, a3k_t1_specializes]

/-- The rational function `F = θ + (1 - θ) t₁` on `W × ℙ¹`.
Source: Fulton, *Intersection Theory*, second edition, §1.6 and Theorem 2.4. -/
def a3k_F (θ : X.left.presheaf.stalk w) :
    (cycleComponent (a3n_T X).left (a3n_b X w)).functionField :=
  a3z_germZ (a3n_b X w) (a3k_A X w θ)

example (θ : X.left.presheaf.stalk w) : a3k_F X w θ = a3z_germZ (a3n_b X w) (a3k_A X w θ) := rfl

omit [IsProjective X.hom] in
theorem a3k_germ_a (c : ℂ) (hc : c = 0 ∨ c = 1) (θ : X.left.presheaf.stalk w)
    (zW : cycleComponent (a3n_T X).left (a3n_b X w))
    (hz : cycleComponentι (a3n_T X).left (a3n_b X w) zW = a3n_σ X c w) :
    a3y_germ (a3n_b X w) zW hz (a3k_a X w c hc θ) = a3k_F X w θ := by
  rw [a3z_germ_specializes (a3n_b X w) (genericPoint _) zW
    (a3m_cycleComponentι_genericPoint _ _) hz (a3k_b_σ X w c), a3k_a_specializes]
  rfl

omit [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] in
theorem a3k_a_not_mem (c : ℂ) (hc : c = 0 ∨ c = 1) (θ : X.left.presheaf.stalk w)
    (hθ : θ ∉ IsLocalRing.maximalIdeal _) :
    a3k_a X w c hc θ ∉ IsLocalRing.maximalIdeal _ := by
  intro hm
  have h1 := a3k_map_mem_maximalIdeal (a3n_g X c w).hom hm
  have hg : ∀ a, (a3n_g X c w).hom (a3n_f X c w a) = a := a3n_g_f X c w
  rw [a3k_a, map_add, map_mul, map_sub, map_one, hg] at h1
  rcases hc with rfl | rfl
  · have h2 := a3k_map_mem_maximalIdeal (a3n_g X 0 w).hom (a3k_t1_σ0 X w
      (a3k_mem_basicOpen_σ X w 0 (Or.inl rfl)))
    have := Ideal.sub_mem _ h1 (Ideal.mul_mem_left _ (1 - θ) h2)
    rw [add_sub_cancel_right] at this
    exact hθ this
  · have h2 := a3k_map_mem_maximalIdeal (a3n_g X 1 w).hom (a3k_t1_σ1 X w
      (a3k_mem_basicOpen_σ X w 1 (Or.inr rfl)))
    rw [map_sub, map_one] at h2
    have := Ideal.sub_mem _ h1 (Ideal.mul_mem_left _ (1 - θ) h2)
    have h3 : θ + (1 - θ) * (a3n_g X 1 w).hom (a3k_t1 X (a3n_σ X 1 w)
        (a3k_mem_basicOpen_σ X w 1 (Or.inr rfl))) - (1 - θ) *
        ((a3n_g X 1 w).hom (a3k_t1 X (a3n_σ X 1 w) (a3k_mem_basicOpen_σ X w 1 (Or.inr rfl))) - 1) =
        1 := by ring
    rw [h3] at this
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (Ideal.eq_top_of_isUnit_mem _ this isUnit_one)

omit [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] in
theorem a3k_germZ_a0 (θ : X.left.presheaf.stalk w) :
    a3z_germZ (a3n_σ X 0 w) (a3k_a X w 0 (Or.inl rfl) θ) =
      a3z_germZ (a3n_σ X 0 w) (a3n_f X 0 w θ) := by
  have h0 := (a3z_germZ_eq_zero_iff _ _).2 (a3k_t1_σ0 X w (a3k_mem_basicOpen_σ X w 0 (Or.inl rfl)))
  rw [a3k_a, map_add, map_mul, h0, mul_zero, add_zero]

omit [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] in
theorem a3k_germZ_a1 (θ : X.left.presheaf.stalk w) :
    a3z_germZ (a3n_σ X 1 w) (a3k_a X w 1 (Or.inr rfl) θ) = 1 := by
  have h1 := (a3z_germZ_eq_zero_iff _ _).2 (a3k_t1_σ1 X w (a3k_mem_basicOpen_σ X w 1 (Or.inr rfl)))
  rw [map_sub, map_one, sub_eq_zero] at h1
  rw [a3k_a, map_add, map_mul, h1, mul_one, map_sub, map_one, add_sub_cancel]

omit [IsProjective X.hom] in
theorem a3k_isRestriction (c : ℂ) (hc : c = 0 ∨ c = 1) (θ : X.left.presheaf.stalk w)
    (hθ : θ ∉ IsLocalRing.maximalIdeal _) :
    a3z_IsRestriction (a3n_b X w) (a3k_F X w θ) (a3n_σ X c w)
      (a3z_germZ (a3n_σ X c w) (a3k_a X w c hc θ)) := by
  obtain ⟨zW, hz⟩ := a3z_exists_pt _ (a3k_b_σ X w c)
  refine ⟨zW, hz, a3k_a X w c hc θ, 1, a3k_a_not_mem X w c hc θ hθ, ?_, ?_, ?_⟩
  · rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
    exact isUnit_one
  · rw [map_one, mul_one, a3k_germ_a]
  · rw [map_one, mul_one]

omit [IsProjective X.hom] in
theorem a3k_F_ne_zero (θ : X.left.presheaf.stalk w) (hθ : θ ∉ IsLocalRing.maximalIdeal _) :
    a3k_F X w θ ≠ 0 := by
  obtain ⟨zW, hz⟩ := a3z_exists_pt _ (a3k_b_σ X w 0)
  rw [← a3k_germ_a X w 0 (Or.inl rfl) θ zW hz]
  intro h0
  rw [a3y_germ_eq_zero_iff] at h0
  exact a3k_a_not_mem X w 0 (Or.inl rfl) θ hθ
    (a3z_stalkIdeal_le_maximalIdeal (a3n_b X w) (a3k_b_σ X w 0) h0)

/-- The components of `div F` meet `X × {0}` and `X × {1}` properly. -/
theorem a3k_meet_divF (c : ℂ) (hc : c = 0 ∨ c = 1) (θ : X.left.presheaf.stalk w)
    (hθ : θ ∉ IsLocalRing.maximalIdeal _) (d : (a3n_T X).left)
    (hd : a2_principalCycle (a3n_T X).left ℚ (a3n_b X w) (a3k_F X w θ) d ≠ 0) :
    a3i_MeetProperly (a3n_T X).left d (a3n_σ X c (genericPoint X.left)) := by
  obtain ⟨D, hD, hD1, -⟩ := a3z_principalCycle_ne_zero _ (a3n_b X w) _ (a3k_F_ne_zero X w θ hθ)
    d hd
  have hbd : a3n_b X w ⤳ d := hD ▸ a3z_specializes_pt (a3n_b X w) D
  have hcoh : coheight d = coheight w + 1 := by
    rw [← hD, (a3y_coheight_eq_one_iff (a3n_T X) (a3n_b X w) D).1 hD1, a3k_coheight_b]
  have hnot : d ∉ Set.range (a3n_σ X c) := by
    rintro ⟨e, rfl⟩
    have hwe : w ⤳ e := by rwa [a3n_b_specializes_iff, a3n_q_σ_apply] at hbd
    rw [a3n_coheight_σ] at hcoh
    have hee : coheight e = coheight w :=
      WithTop.add_right_cancel (by decide : (1 : ℕ∞) ≠ ⊤) hcoh
    have hew : w = e := a3y_eq_of_specializes hwe hee.le
    subst hew
    exact hd (a3k_principalCycle_eq_zero_of_unitAt (a3n_b X w) _ (a3k_F_ne_zero X w θ hθ) _
      (a3z_isRestriction_unitAt (a3n_b X w) (a3k_isRestriction X w c hc θ hθ)))
  intro v hv
  have hz : (ccm3_primeIdeal (a3n_T X).left d ⊔ ccm3_primeIdeal (a3n_T X).left
      (a3n_σ X c (genericPoint X.left))).subschemeι v ∈
        a3y_comps d (a3n_σ X c (genericPoint X.left)) := ⟨v, hv, rfl⟩
  set z := (ccm3_primeIdeal (a3n_T X).left d ⊔ ccm3_primeIdeal (a3n_T X).left
      (a3n_σ X c (genericPoint X.left))).subschemeι v
  obtain ⟨hdz, hsz, -⟩ := a3y_comps_spec _ _ hz
  have hzr : z ∈ Set.range (a3n_σ X c) := a3n_mem_range_σ_of_specializes X c hsz
  have hne : d ≠ z := fun h => hnot (h ▸ hzr)
  have hlt := Order.add_one_le_of_lt (a3y_coheight_lt hdz hne)
  have hle := a3k_coheight_comps_le X hz
  rw [a3k_coheight_σ_generic] at hle ⊢
  exact le_antisymm hle hlt

open Classical in
/-- **`[div F] · [X × {c}] = [div (F|_{W × {c}})]`.** -/
theorem a3k_divF_σ (c : ℂ) (hc : c = 0 ∨ c = 1) (θ : X.left.presheaf.stalk w)
    (hθ : θ ∉ IsLocalRing.maximalIdeal _) :
    a3i_intersect (a3n_T X).left (a2_principalCycle (a3n_T X).left ℚ (a3n_b X w) (a3k_F X w θ))
        (Function.locallyFinsuppWithin.single (a3n_σ X c (genericPoint X.left)) 1) =
      a2_principalCycle (a3n_T X).left ℚ (a3n_σ X c w)
        (a3z_germZ (a3n_σ X c w) (a3k_a X w c hc θ)) := by
  let ψ : (z : (a3n_T X).left) → (cycleComponent (a3n_T X).left z).functionField := fun z =>
    if h : z = a3n_σ X c w then
      a3z_germZ z ((a3n_T X).left.presheaf.stalkSpecializes (specializes_of_eq h)
        (a3k_a X w c hc θ))
    else 0
  have hψσ : ψ (a3n_σ X c w) = a3z_germZ (a3n_σ X c w) (a3k_a X w c hc θ) := by
    simp only [ψ, dite_true, TopCat.Presheaf.stalkSpecializes_refl]
    rfl
  have hψ : ∀ z ∈ a3y_comps (a3n_b X w) (a3n_σ X c (genericPoint X.left)),
      a3z_IsRestriction (a3n_b X w) (a3k_F X w θ) z (ψ z) := by
    intro z hz
    rw [a3k_comps_b_σ, Set.mem_singleton_iff] at hz
    subst hz
    rw [hψσ]
    exact a3k_isRestriction X w c hc θ hθ
  rw [a3z_principal_intersect (a3n_T X) (a3n_b X w) _ (a3k_meet_b_σ X w c) _
    (a3k_F_ne_zero X w θ hθ) (a3k_meet_divF X w c hc θ hθ) ψ hψ]
  have hfin : (a3y_comps_finite (a3n_b X w) (a3n_σ X c (genericPoint X.left))).toFinset =
      {a3n_σ X c w} := by
    ext z
    rw [Set.Finite.mem_toFinset, Finset.mem_singleton, a3k_comps_b_σ, Set.mem_singleton_iff]
  rw [hfin, Finset.sum_singleton, hψσ, a3k_serreMult_b_σ]
  ext x
  simp [Function.locallyFinsuppWithin.mapRange_apply]

end F

section transport
variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
  (c : ℂ) (w : X.left)

omit [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] in
/-- The pull-back along `q` commutes with specialization along the section `σ_c`. -/
theorem a3k_f_natural {x : X.left} (hwx : w ⤳ x) (α : X.left.presheaf.stalk x) :
    a3n_f X c w (X.left.presheaf.stalkSpecializes hwx α) =
      (a3n_T X).left.presheaf.stalkSpecializes (hwx.map (a3n_σ X c).continuous)
        (a3n_f X c x α) := by
  change (a3n_q X).left.stalkMap (a3n_σ X c w)
      ((X.left.presheaf.stalkCongr (.of_eq (a3n_qσ X c w))).inv
        (X.left.presheaf.stalkSpecializes hwx α)) =
    (a3n_T X).left.presheaf.stalkSpecializes _ ((a3n_q X).left.stalkMap (a3n_σ X c x)
      ((X.left.presheaf.stalkCongr (.of_eq (a3n_qσ X c x))).inv α))
  rw [← Scheme.Hom.stalkSpecializes_stalkMap_apply]
  congr 1
  dsimp only [TopCat.Presheaf.stalkCongr]
  rw [TopCat.Presheaf.stalkSpecializes_comp_apply, TopCat.Presheaf.stalkSpecializes_comp_apply]

omit [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] in
theorem a3k_f_mem_maximalIdeal {x : X.left} {m : X.left.presheaf.stalk x}
    (hm : m ∈ IsLocalRing.maximalIdeal _) : a3n_f X c x m ∈ IsLocalRing.maximalIdeal _ := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hm ⊢
  intro hu
  apply hm
  have := hu.map (a3n_g X c x).hom
  rwa [show (a3n_g X c x).hom (a3n_f X c x m) = m from a3n_g_f X c x m] at this

omit [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] in
/-- Restrictions to `W` transport to restrictions to `σ_c(W)`. -/
theorem a3k_germ_transport (θ : X.left.presheaf.stalk w) (xW : cycleComponent X.left w)
    (D : cycleComponent (a3n_T X).left (a3n_σ X c w))
    (hD : cycleComponentι (a3n_T X).left (a3n_σ X c w) D =
      a3n_σ X c (cycleComponentι X.left w xW))
    (α β : X.left.presheaf.stalk (cycleComponentι X.left w xW))
    (hab : a3y_germ w xW rfl α = a3z_germZ w θ * a3y_germ w xW rfl β) :
    a3y_germ (a3n_σ X c w) D hD (a3n_f X c _ α) =
      a3z_germZ (a3n_σ X c w) (a3n_f X c w θ) * a3y_germ (a3n_σ X c w) D hD (a3n_f X c _ β) := by
  set x := cycleComponentι X.left w xW
  have hwx : w ⤳ x := a3z_specializes_pt w xW
  have hσ : a3n_σ X c w ⤳ a3n_σ X c x := hwx.map (a3n_σ X c).continuous
  have hW : ∀ r, a3y_germ w xW rfl r = a3z_germZ w (X.left.presheaf.stalkSpecializes hwx r) :=
    fun r => a3z_germ_specializes w _ xW (a3m_cycleComponentι_genericPoint _ w) rfl hwx r
  have hT : ∀ r, a3y_germ (a3n_σ X c w) D hD r =
      a3z_germZ (a3n_σ X c w) ((a3n_T X).left.presheaf.stalkSpecializes hσ r) :=
    fun r => a3z_germ_specializes (a3n_σ X c w) _ D (a3m_cycleComponentι_genericPoint _ _) hD hσ r
  rw [hW, hW, ← map_mul, ← sub_eq_zero, ← map_sub, a3z_germZ_eq_zero_iff] at hab
  have hm := a3k_f_mem_maximalIdeal X c hab
  rw [map_sub, map_mul] at hm
  rw [hT, hT, ← a3k_f_natural, ← a3k_f_natural, ← map_mul, ← sub_eq_zero, ← map_sub,
    a3z_germZ_eq_zero_iff]
  exact hm

omit [IsIntegral X.left] in
/-- The order of a restriction along `σ_c(W)` is the order along `W`. -/
theorem a3k_ord_transport (xW : cycleComponent X.left w)
    (D : cycleComponent (a3n_T X).left (a3n_σ X c w))
    (hD : cycleComponentι (a3n_T X).left (a3n_σ X c w) D =
      a3n_σ X c (cycleComponentι X.left w xW))
    (hx1 : coheight xW = 1) (hD1 : coheight D = 1)
    (α : X.left.presheaf.stalk (cycleComponentι X.left w xW))
    (hα : α ∉ a3i_stalkIdeal X.left (cycleComponentι X.left w xW) w) :
    (cycleComponent (a3n_T X).left (a3n_σ X c w)).ord
        (a3y_germ (a3n_σ X c w) D hD (a3n_f X c _ α)) D =
      (cycleComponent X.left w).ord (a3y_germ w xW rfl α) xW := by
  have hwx : w ⤳ cycleComponentι X.left w xW := a3z_specializes_pt w xW
  have : (a3i_stalkIdeal X.left (cycleComponentι X.left w xW) w).IsPrime :=
    a3q_stalkIdeal_isPrime X.left hwx
  have hfα : a3n_f X c _ α ∉ a3i_stalkIdeal (a3n_T X).left
      (a3n_σ X c (cycleComponentι X.left w xW)) (a3n_σ X c w) := by
    rw [a3n_stalkIdeal_σ X c _ w hwx, Ideal.mem_comap,
      show (a3n_g X c _).hom (a3n_f X c _ α) = α from a3n_g_f X c _ α]
    exact hα
  rw [a3y_ord_germ_self (a3n_σ X c w) D hD hD1 _ hfα, a3y_ord_germ_self w xW rfl hx1 _ hα,
    a3n_stalkIdeal_σ X c _ w hwx]
  exact a3k_herbrand_retract (a3n_f X c _).hom (a3n_g X c _).hom (a3n_g_f X c _) _ α hα

/-- **Transport along `σ_c`**: `q_*[div (θ|_{σ_c(W)})] = [div θ]`. -/
theorem a3k_push_σ (θ : X.left.presheaf.stalk w) (hθ : θ ∉ IsLocalRing.maximalIdeal _) :
    a1p_pushforward (a3n_q X).left (a2_principalCycle (a3n_T X).left ℚ (a3n_σ X c w)
      (a3z_germZ (a3n_σ X c w) (a3n_f X c w θ))) =
      a2_principalCycle X.left ℚ w (a3z_germZ w θ) := by
  classical
  have : IsNoetherian X.left := by
    have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
    have : CompactSpace X.left := by
      have h := QuasiCompact.isCompact_preimage (f := X.hom) _ isOpen_univ isCompact_univ
      rw [Set.preimage_univ] at h
      exact isCompact_univ_iff.mp h
    exact ⟨⟩
  set ψ := a3z_germZ (a3n_σ X c w) (a3n_f X c w θ)
  have hψ : ψ ≠ 0 := fun h0 =>
    ((a3z_germZ_eq_zero_iff _ _).1 h0) |> fun hm => hθ (by
      have := a3k_map_mem_maximalIdeal (a3n_g X c w).hom hm
      rwa [show (a3n_g X c w).hom (a3n_f X c w θ) = θ from a3n_g_f X c w θ] at this)
  have hθ' : a3z_germZ w θ ≠ 0 := fun h0 => hθ ((a3z_germZ_eq_zero_iff _ _).1 h0)
  ext x
  rw [a1p_pushforward_apply_eq_sum _ _ x {a3n_σ X c x}]
  rotate_left
  · rintro y ⟨hy, hyc⟩
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hy
    have hr : y ∈ Set.range (cycleComponentι (a3n_T X).left (a3n_σ X c w)) := by
      by_contra hr
      exact hyc (a3y_principalCycle_apply_of_not_mem _ _ _ _ hr)
    obtain ⟨Y, rfl⟩ := hr
    obtain ⟨e, he⟩ := a3n_mem_range_σ_of_specializes X c (a3z_specializes_pt _ Y)
    rw [Finset.coe_singleton, Set.mem_singleton_iff, ← he, ← hy, ← he, a3n_q_σ_apply]
  · intro y hy
    rw [Finset.coe_singleton, Set.mem_singleton_iff] at hy
    rw [hy, Set.mem_preimage, Set.mem_singleton_iff, a3n_q_σ_apply]
  rw [Finset.sum_singleton, a3n_degree_q_σ, Nat.cast_one, mul_one]
  by_cases hwx : w ⤳ x
  · obtain ⟨xW, rfl⟩ := a3z_exists_pt w hwx
    obtain ⟨D, hD⟩ := a3z_exists_pt (a3n_σ X c w) (hwx.map (a3n_σ X c).continuous)
    rw [← hD, a3y_principalCycle_apply _ _ _ hψ D, a3y_principalCycle_apply _ _ _ hθ' xW]
    congr 1
    have hcoh : coheight D = 1 ↔ coheight xW = 1 := by
      rw [a3y_coheight_eq_one_iff (a3n_T X), a3y_coheight_eq_one_iff X, hD, a3n_coheight_σ,
        a3n_coheight_σ]
      exact ⟨fun h => WithTop.add_right_cancel (by decide : (1 : ℕ∞) ≠ ⊤) h,
        fun h => by rw [h]⟩
    by_cases h1 : coheight xW = 1
    · have hD1 := hcoh.2 h1
      -- write `θ` as a quotient of germs at `x`
      obtain ⟨n, d, hd, hnd⟩ := IsFractionRing.div_surjective
        (A := (cycleComponent X.left w).presheaf.stalk xW) (a3z_germZ w θ)
      obtain ⟨α, hα⟩ := (cycleComponentι X.left w).stalkMap_surjective xW n
      obtain ⟨β, hβ⟩ := (cycleComponentι X.left w).stalkMap_surjective xW d
      have hd0 : algebraMap _ (cycleComponent X.left w).functionField d ≠ 0 :=
        IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
      have hgα : a3y_germ w xW rfl α = algebraMap _ _ n := by rw [a3y_germ_self, hα]
      have hgβ : a3y_germ w xW rfl β = algebraMap _ _ d := by rw [a3y_germ_self, hβ]
      have hab : a3y_germ w xW rfl α = a3z_germZ w θ * a3y_germ w xW rfl β := by
        rw [hgα, hgβ, ← hnd, div_mul_cancel₀ _ hd0]
      have hβ0 : a3y_germ w xW rfl β ≠ 0 := by rw [hgβ]; exact hd0
      have hα0 : a3y_germ w xW rfl α ≠ 0 := by rw [hab]; exact mul_ne_zero hθ' hβ0
      have hαp : α ∉ a3i_stalkIdeal X.left _ w := fun h =>
        hα0 ((a3y_germ_eq_zero_iff w xW rfl α).2 h)
      have hβp : β ∉ a3i_stalkIdeal X.left _ w := fun h =>
        hβ0 ((a3y_germ_eq_zero_iff w xW rfl β).2 h)
      have hrel := a3k_germ_transport X c w θ xW D hD α β hab
      have hfβ0 : a3y_germ (a3n_σ X c w) D hD (a3n_f X c _ β) ≠ 0 := by
        intro h0
        have h := a3k_ord_transport X c w xW D hD h1 hD1 β hβp
        rw [h0] at h
        rw [a3y_germ_eq_zero_iff] at h0
        rw [a3n_stalkIdeal_σ X c _ w (a3z_specializes_pt w xW), Ideal.mem_comap,
          show (a3n_g X c _).hom (a3n_f X c _ β) = β from a3n_g_f X c _ β] at h0
        exact hβp h0
      have e1 := Scheme.ord_mul (x := D) hψ hfβ0
      have e2 := Scheme.ord_mul (x := xW) hθ' hβ0
      rw [← hrel, a3k_ord_transport X c w xW D hD h1 hD1 α hαp,
        a3k_ord_transport X c w xW D hD h1 hD1 β hβp] at e1
      rw [← hab] at e2
      exact_mod_cast (by linarith : (cycleComponent (a3n_T X).left (a3n_σ X c w)).ord ψ D =
        (cycleComponent X.left w).ord (a3z_germZ w θ) xW)
    · rw [Scheme.ord_eq_zero_of_coheight_neq_one h1,
        Scheme.ord_eq_zero_of_coheight_neq_one (fun h => h1 (hcoh.1 h))]
  · rw [a3y_principalCycle_apply_of_not_mem X.left w (a3z_germZ w θ) x (fun ⟨xW, hxW⟩ =>
      hwx (hxW ▸ a3z_specializes_pt w xW))]
    rw [a3y_principalCycle_apply_of_not_mem (a3n_T X).left (a3n_σ X c w) ψ (a3n_σ X c x)
      (fun ⟨D, hD⟩ => hwx (by
        have := (a3z_specializes_pt _ D).map (a3n_q X).left.continuous
        rwa [hD, a3n_q_σ_apply, a3n_q_σ_apply] at this))]

end transport

section assemble
variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
  (w : X.left)

/-- The components of `div F` with a nonzero coefficient avoid `X × {0}` and `X × {1}`. -/
theorem a3k_divF_not_mem_range (θ : X.left.presheaf.stalk w)
    (hθ : θ ∉ IsLocalRing.maximalIdeal _) (c : ℂ) (hc : c = 0 ∨ c = 1) (d : (a3n_T X).left)
    (hd : a2_principalCycle (a3n_T X).left ℚ (a3n_b X w) (a3k_F X w θ) d ≠ 0) :
    d ∉ Set.range (a3n_σ X c) := by
  obtain ⟨D, hD, hD1, -⟩ := a3z_principalCycle_ne_zero _ (a3n_b X w) _ (a3k_F_ne_zero X w θ hθ)
    d hd
  have hbd : a3n_b X w ⤳ d := hD ▸ a3z_specializes_pt (a3n_b X w) D
  have hcoh : coheight d = coheight w + 1 := by
    rw [← hD, (a3y_coheight_eq_one_iff (a3n_T X) (a3n_b X w) D).1 hD1, a3k_coheight_b]
  rintro ⟨e, rfl⟩
  have hwe : w ⤳ e := by rwa [a3n_b_specializes_iff, a3n_q_σ_apply] at hbd
  rw [a3n_coheight_σ] at hcoh
  have hee : coheight e = coheight w := WithTop.add_right_cancel (by decide : (1 : ℕ∞) ≠ ⊤) hcoh
  have hew : w = e := a3y_eq_of_specializes hwe hee.le
  subst hew
  exact hd (a3k_principalCycle_eq_zero_of_unitAt (a3n_b X w) _ (a3k_F_ne_zero X w θ hθ) _
    (a3z_isRestriction_unitAt (a3n_b X w) (a3k_isRestriction X w c hc θ hθ)))

/-- A component of `div F` not dominating `ℙ¹` does not meet `X × {0}` or `X × {1}`. -/
theorem a3k_intersectPrime_nondom (θ : X.left.presheaf.stalk w)
    (hθ : θ ∉ IsLocalRing.maximalIdeal _) (D : (a3n_T X).left)
    (hD : a2_principalCycle (a3n_T X).left ℚ (a3n_b X w) (a3k_F X w θ) D ≠ 0)
    (hdom : a3n_h X D ≠ genericPoint (g3c_P 1)) (c : ℂ) (hc : c = 0 ∨ c = 1)
    (τ : (a3n_T X).left) :
    a3i_intersectPrime (a3n_T X).left (a3n_σ X c (genericPoint X.left)) D τ = 0 := by
  by_contra hne
  obtain ⟨hsτ, hDτ, -⟩ := a3y_comps_spec _ _ (a3z_intersectPrime_ne_zero _ _ _ τ hne)
  obtain ⟨e, rfl⟩ := a3n_mem_range_σ_of_specializes X c hsτ
  have hp := hDτ.map (a3n_p X).continuous
  rw [a3k_p_σ] at hp
  by_cases heq : a3n_p X D = a3n_pt c a3n_o
  · apply a3k_divF_not_mem_range X w θ hθ c hc D hD
    rcases hc with rfl | rfl
    · refine ⟨_, (a3n_eq_σ0 X D ?_).symm⟩
      change a3n_π (a3n_p X D) ∈ a3m_Z0
      rw [heq, ← a3k_p_σ X 0 e]
      exact a3n_h_σ0 X e
    · refine ⟨_, (a3n_eq_σ1 X D ?_).symm⟩
      change a3n_π (a3n_p X D) ∈ a3m_Zinf
      rw [heq, ← a3k_p_σ X 1 e]
      exact a3n_h_σ1 X e
  · apply hdom
    change a3n_π (a3n_p X D) = _
    rw [a3k_P1_eq_generic hp heq, a3k_π_generic]

open Classical in
theorem a3k_intersect_nondom (θ : X.left.presheaf.stalk w)
    (hθ : θ ∉ IsLocalRing.maximalIdeal _) (D : (a3n_T X).left)
    (hD : a2_principalCycle (a3n_T X).left ℚ (a3n_b X w) (a3k_F X w θ) D ≠ 0)
    (hdom : a3n_h X D ≠ genericPoint (g3c_P 1)) :
    a3i_intersect (a3n_T X).left (a3k_cycT X) (Function.locallyFinsuppWithin.single D 1) = 0 := by
  classical
  set s₀ := a3n_σ X 0 (genericPoint X.left)
  set s₁ := a3n_σ X 1 (genericPoint X.left)
  have hs : ∀ u ∉ ({s₀, s₁} : Finset (a3n_T X).left), a3k_cycT X u = 0 := by
    intro u hu
    by_contra h
    rcases a3k_cycT_supp X u h with rfl | rfl <;> simp [s₀, s₁] at hu
  ext τ
  rw [a3z_intersect_single_apply _ _ D {s₀, s₁} hs τ]
  refine Finset.sum_eq_zero fun u hu => ?_
  rw [Finset.mem_insert, Finset.mem_singleton] at hu
  rcases hu with rfl | rfl
  · rw [a3k_intersectPrime_nondom X w θ hθ D hD hdom 0 (Or.inl rfl) τ, mul_zero]
  · rw [a3k_intersectPrime_nondom X w θ hθ D hD hdom 1 (Or.inr rfl) τ, mul_zero]

/-- **Fulton, Proposition 1.6**: `[div θ]` is the boundary of a chain of members dominating
`ℙ¹`.
Source: Fulton, *Intersection Theory*, second edition, Proposition 1.6. -/
theorem a3k_principal_mem_bd (φ : (cycleComponent X.left w).functionField) (hφ : φ ≠ 0) :
    ∃ Z : AlgebraicCycle (a3n_T X).left ℚ,
      (∀ y, Z y ≠ 0 → a3n_h X y = genericPoint (g3c_P 1)) ∧
        a3k_bd X Z = a2_principalCycle X.left ℚ w φ := by
  classical
  obtain ⟨θ, rfl⟩ := a3k_germZ_surjective w φ
  have hθ : θ ∉ IsLocalRing.maximalIdeal _ := fun h => hφ ((a3z_germZ_eq_zero_iff _ _).2 h)
  set P := a2_principalCycle (a3n_T X).left ℚ (a3n_b X w) (a3k_F X w θ)
  set s := (a3m_support_finite P).toFinset
  have hs : ∀ D ∉ s, P D = 0 := fun D hD => by simpa [s] using hD
  set sd := s.filter (fun D => a3n_h X D = genericPoint (g3c_P 1))
  set Z₀ : AlgebraicCycle (a3n_T X).left ℚ :=
    ∑ D ∈ sd, a3m_smul (P D) (Function.locallyFinsuppWithin.single D 1)
  have hZ₀ : ∀ D, Z₀ D = if D ∈ sd then P D else 0 := by
    intro D
    rw [a3m_sum_apply]
    simp only [a3m_smul_apply, Function.locallyFinsuppWithin.single_apply, mul_ite, mul_one,
      mul_zero]
    rw [Finset.sum_ite_eq]
  set m₀ := a3k_cycT X (a3n_σ X 0 (genericPoint X.left))
  have hm₀ : m₀ ≠ 0 := (a3k_cycT_pos X).ne'
  refine ⟨a3m_smul m₀⁻¹ Z₀, fun y hy => ?_, ?_⟩
  · rw [a3m_smul_apply, hZ₀] at hy
    split_ifs at hy with h
    · exact (Finset.mem_filter.1 h).2
    · simp at hy
  -- the boundary
  have hbd : a3k_bd X Z₀ =
      a1p_pushforward (a3n_q X).left (a3i_intersect (a3n_T X).left (a3k_cycT X) P) := by
    rw [a3k_bd_eq_sum X Z₀ sd (fun D hD => by rw [hZ₀]; simp [hD]),
      a3o_intersect_eq_sum_right (a3n_T X).left _ P s hs, a3k_pushforward_sum,
      ← Finset.sum_filter_add_sum_filter_not s (fun D => a3n_h X D = genericPoint (g3c_P 1))]
    rw [Finset.sum_eq_zero (s := s.filter (fun D => ¬a3n_h X D = genericPoint (g3c_P 1))),
      add_zero]
    · refine Finset.sum_congr rfl fun D hD => ?_
      have hDdom := (Finset.mem_filter.1 hD).2
      have hZD : Z₀ D = P D := by
        rw [hZ₀]
        split_ifs with h
        · rfl
        · exact absurd hD h
      rw [hZD, a3k_piece_of_dom X D hDdom, a3k_cyc_eq_intersect X D hDdom,
        a3k_pushforward_smul]
    · intro D hD
      obtain ⟨hDs, hDdom⟩ := Finset.mem_filter.1 hD
      have hPD : P D ≠ 0 := by simpa [s] using hDs
      rw [a3k_intersect_nondom X w θ hθ D hPD hDdom,
        show a3m_smul (P D) (0 : AlgebraicCycle (a3n_T X).left ℚ) = 0 by ext; simp,
        a3k_pushforward_zero]
  have hsupp : ∀ u ∉ ({a3n_σ X 0 (genericPoint X.left), a3n_σ X 1 (genericPoint X.left)} :
      Finset (a3n_T X).left), a3k_cycT X u = 0 := by
    intro u hu
    by_contra h
    rcases a3k_cycT_supp X u h with rfl | rfl <;> simp at hu
  have hne : a3n_σ X 0 (genericPoint X.left) ≠ a3n_σ X 1 (genericPoint X.left) :=
    a3n_σ0_ne_σ1 X _ _
  rw [a3k_bd_smul, hbd, a3k_intersect_symm, a3o_intersect_eq_sum_right (a3n_T X).left P _ _ hsupp,
    Finset.sum_pair hne, a3k_divF_σ X w 0 (Or.inl rfl) θ hθ, a3k_divF_σ X w 1 (Or.inr rfl) θ hθ,
    a3k_germZ_a0, a3k_germZ_a1, a3k_principalCycle_one, a1p_pushforward_add,
    a3k_pushforward_smul, a3k_pushforward_smul, a3k_push_σ X 0 w θ hθ]
  ext x
  have h0 : a1p_pushforward (a3n_q X).left (0 : AlgebraicCycle (a3n_T X).left ℚ) = 0 := by
    have h := a1p_pushforward_add (a3n_q X).left (0 : AlgebraicCycle (a3n_T X).left ℚ) 0
    rw [add_zero] at h
    exact (left_eq_add.mp h)
  rw [h0]
  have hinv : m₀⁻¹ * a3k_cycT X (a3n_σ X 0 (genericPoint X.left)) = 1 := inv_mul_cancel₀ hm₀
  simp only [a3m_smul_apply, Function.locallyFinsuppWithin.coe_add, Pi.add_apply,
    Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply, mul_zero, add_zero, ← mul_assoc, hinv,
    one_mul]

/-- Every cycle rationally equivalent to zero is the boundary of a chain of members dominating
`ℙ¹`.
Source: Fulton, *Intersection Theory*, second edition, Proposition 1.6. -/
theorem a3k_ratAll_bd (γ : AlgebraicCycle X.left ℚ) (hγ : γ ∈ a3i_ratAll X.left) :
    ∃ Z : AlgebraicCycle (a3n_T X).left ℚ,
      (∀ y, Z y ≠ 0 → a3n_h X y = genericPoint (g3c_P 1)) ∧ a3k_bd X Z = γ := by
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  let B : AddSubgroup (AlgebraicCycle X.left ℚ) :=
    { carrier := {γ | ∃ Z : AlgebraicCycle (a3n_T X).left ℚ,
        (∀ y, Z y ≠ 0 → a3n_h X y = genericPoint (g3c_P 1)) ∧ a3k_bd X Z = γ}
      add_mem' := by
        rintro _ _ ⟨Z, hZ, rfl⟩ ⟨Z', hZ', rfl⟩
        refine ⟨Z + Z', fun y hy => ?_, a3k_bd_add X Z Z'⟩
        by_cases h : Z y = 0
        · rw [Function.locallyFinsuppWithin.coe_add, Pi.add_apply, h, zero_add] at hy
          exact hZ' y hy
        · exact hZ y h
      zero_mem' := ⟨0, fun _ h => (h rfl).elim, a3k_bd_zero X⟩
      neg_mem' := by
        rintro _ ⟨Z, hZ, rfl⟩
        exact ⟨-Z, fun y hy => hZ y (by simpa using hy), a3k_bd_neg X Z⟩ }
  have hle : a3i_ratAll X.left ≤ B := iSup_le fun k => (AddSubgroup.closure_le _).2 (by
    rintro _ ⟨w, φ, r, -, hφ, rfl⟩
    obtain ⟨Z, hZ, hbd⟩ := a3k_principal_mem_bd X w φ hφ
    refine ⟨a3m_smul r Z, fun y hy => hZ y (fun h => hy (by rw [a3m_smul_apply, h, mul_zero])), ?_⟩
    rw [a3k_bd_smul, hbd]
    rfl)
  exact hle hγ

end assemble

end HodgeLean.Adapters
