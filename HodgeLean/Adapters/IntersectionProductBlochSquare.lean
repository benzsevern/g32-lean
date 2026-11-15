import HodgeLean.Adapters.IntersectionProductBlochRetract
import HodgeLean.Foundations.SegreProjective

/-! # Chains on `X × ℙ¹ × ℙ¹` and the faces `t = a`

Stage A3.3, the relative moving step. A two-parameter chain is a rational cycle `W` on
`T₂ = (X × ℙ¹_t) × ℙ¹_s = a3n_T (a3n_T X)`. Its boundary in `s` is the chain `a3k_bd (a3n_T X) W`
on `X × ℙ¹_t`; its boundary in `t` is a chain on `X × ℙ¹_s`, read through the closed immersions
`ι_a : X × ℙ¹_s → T₂`, `(x, s) ↦ ((x, a), s)` (`a3k_ι`), and the projection
`ρ : T₂ → X × ℙ¹_s` forgetting `t` (`a3k_ρ`), a retraction of each `ι_a`.

This file collects:
* `X × ℙ¹` is projective when `X` is (`a3k_T_projective`), so the facts on `X × ℙ¹` apply to
  `T₂ = (X × ℙ¹) × ℙ¹`;
* every element of `a3k_G X β` meets `β` properly (`a3k_G_le_proper`);
* the maps `ι_a` and `ρ`: `ι_a ≫ ρ = 𝟙`, both commute with the projections to `ℙ¹_s`, the image
  of `ι_a` is the fibre `t = a` (`a3k_range_ι`), and `ρ` has degree `1` along it.

Source: S. Bloch, *The moving lemma for higher Chow groups*, J. Algebraic Geom. 3 (1994),
537–568, §1 (the cubical complex `z^p(X, •)` and its faces); Hartshorne, *Algebraic Geometry*,
II, Theorem 3.3 and Exercise II.4.9. HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Order
open AlgebraicGeometry.ComplexProjectiveSpace HodgeLean.Foundations
open scoped MonoidalCategory

set_option backward.isDefEq.respectTransparency false

namespace HodgeLean.Adapters

section projective

/-- `ℙ¹_ℂ` is projective over `ℂ`, through the identity presentation.
Source: Hartshorne, *Algebraic Geometry*, II, §4 (projective morphisms). -/
instance a3k_P1_projective : IsProjective a3n_P1.hom :=
  ⟨⟨{ ambientDimension := 1, immersion := 𝟙 _, immersion_toBase := Category.id_comp _ }⟩⟩

/-- `X × ℙ¹` is projective when `X` is.
Source: Hartshorne, *Algebraic Geometry*, Exercise II.4.9 (the Segre embedding). -/
instance a3k_T_projective (X : Over (Spec ↧ℂ)) [IsProjective X.hom] :
    IsProjective (a3n_T X).hom :=
  spec_g3c_isProjective_pullback _ _

end projective

section proper
variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

/-- A component of `σ_c(U)` meeting `V × ℙ¹` properly comes from `U` meeting `V` properly. -/
theorem a3k_meetProperly_of_σ (c : ℂ) (u v : X.left)
    (h : a3i_MeetProperly (a3n_T X).left (a3n_σ X c u) (a3n_b X v)) :
    a3i_MeetProperly X.left u v := by
  intro w hw
  have hz : (ccm3_primeIdeal X.left u ⊔ ccm3_primeIdeal X.left v).subschemeι w ∈
      a3y_comps u v := ⟨w, hw, rfl⟩
  have hz' := (a3n_mem_comps_σ_iff X c u v _).2 hz
  have e := a3y_coheight_comps _ _ h hz'
  rw [a3n_coheight_σ, a3n_coheight_σ, a3k_coheight_b, add_right_comm] at e
  exact WithTop.add_right_cancel (by decide : (1 : ℕ∞) ≠ ⊤) e

/-- The cycles meeting `β` properly.
Source: Fulton, *Intersection Theory*, second edition, §7.1 (proper intersection). -/
def a3k_properSub (β : AlgebraicCycle X.left ℚ) : AddSubgroup (AlgebraicCycle X.left ℚ) where
  carrier := {c | a3i_CyclesMeetProperly X.left c β}
  zero_mem' := fun _ _ h => (h rfl).elim
  add_mem' {c d} hc hd u v huv hv := by
    by_cases hcu : c u = 0
    · refine hd u v (fun h0 => huv ?_) hv
      rw [Function.locallyFinsuppWithin.coe_add, Pi.add_apply, hcu, h0, add_zero]
    · exact hc u v hcu hv
  neg_mem' {c} hc u v hu hv := hc u v (fun h0 => hu (by
    rw [Function.locallyFinsuppWithin.coe_neg, Pi.neg_apply, h0, neg_zero])) hv

example (β : AlgebraicCycle X.left ℚ) : (0 : AlgebraicCycle X.left ℚ) ∈ a3k_properSub X β :=
  zero_mem _

/-- **The boundaries of members in good position meet `β` properly.** -/
theorem a3k_G_le_proper (β : AlgebraicCycle X.left ℚ) : a3k_G X β ≤ a3k_properSub X β := by
  refine (AddSubgroup.closure_le _).2 ?_
  rintro _ ⟨y, hy, r, hgood, rfl⟩ u v hu hv
  have hu' : a1p_pushforward (a3n_q X).left (a3o_cyc X y hy) u ≠ 0 := fun h0 =>
    hu (by rw [a3m_smul_apply, h0, mul_zero])
  rw [a3o_pushforward_apply X _ (a3o_cyc_supp X y hy)] at hu'
  obtain ⟨-, hii, -⟩ := hgood v hv
  by_cases h0 : a3o_cyc X y hy (a3n_σ X 0 u) = 0
  · rw [h0, zero_add] at hu'
    exact a3k_meetProperly_of_σ X 1 u v (hii _ hu')
  · exact a3k_meetProperly_of_σ X 0 u v (hii _ h0)

end proper

section maps
variable (X : Over (Spec ↧ℂ))

/-- The section `σ_a` as a morphism over `ℂ`.
Source: Hartshorne, *Algebraic Geometry*, II, Theorem 3.3 (fibred products). -/
def a3k_σO (a : ℂ) : X ⟶ a3n_T X :=
  Over.homMk (a3n_σ X a) (by
    rw [← Over.w (a3n_q X), ← Category.assoc, a3n_σ_q, Category.id_comp])

example (a : ℂ) : (a3k_σO X a).left = a3n_σ X a := rfl

/-- `ι_a : X × ℙ¹_s → (X × ℙ¹_t) × ℙ¹_s`, `(x, s) ↦ ((x, a), s)`.
Source: Hartshorne, *Algebraic Geometry*, II, Theorem 3.3 (fibred products). -/
def a3k_ι (a : ℂ) : (a3n_T X).left ⟶ (a3n_T (a3n_T X)).left := ((a3k_σO X a) ▷ a3n_P1).left

example (a : ℂ) : a3k_ι X a = ((a3k_σO X a) ▷ a3n_P1).left := rfl

/-- `ρ : (X × ℙ¹_t) × ℙ¹_s → X × ℙ¹_s`, forgetting `t`.
Source: Hartshorne, *Algebraic Geometry*, II, Theorem 3.3 (fibred products). -/
def a3k_ρ : (a3n_T (a3n_T X)).left ⟶ (a3n_T X).left := ((a3n_q X) ▷ a3n_P1).left

example : a3k_ρ X = ((a3n_q X) ▷ a3n_P1).left := rfl

instance a3k_ρ_proper : IsProper (a3k_ρ X) := by
  rw [a3k_ρ, Over.whiskerRight_left]
  exact MorphismProperty.pullbackMap (P := @IsProper) (inferInstance : IsProper (a3n_q X).left)
    (inferInstance : IsProper (𝟙 a3n_P1.left)) (Over.w (a3n_q X)).symm (Category.id_comp _).symm

theorem a3k_σO_q (a : ℂ) : a3k_σO X a ≫ a3n_q X = 𝟙 X :=
  Over.OverMorphism.ext (a3n_σ_q X a)

theorem a3k_ι_ρ (a : ℂ) : a3k_ι X a ≫ a3k_ρ X = 𝟙 _ := by
  rw [a3k_ι, a3k_ρ, ← Over.comp_left, ← MonoidalCategory.comp_whiskerRight, a3k_σO_q,
    MonoidalCategory.id_whiskerRight, Over.id_left]

theorem a3k_ρ_ι_apply (a : ℂ) (x : (a3n_T X).left) : a3k_ρ X (a3k_ι X a x) = x :=
  a3k_ri _ _ (a3k_ι_ρ X a) x

theorem a3k_ρ_p : a3k_ρ X ≫ a3n_p X = a3n_p (a3n_T X) := by
  rw [a3k_ρ, Over.whiskerRight_left]
  exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)

theorem a3k_ι_p (a : ℂ) : a3k_ι X a ≫ a3n_p (a3n_T X) = a3n_p X := by
  rw [a3k_ι, Over.whiskerRight_left]
  exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)

theorem a3k_ι_q (a : ℂ) : a3k_ι X a ≫ (a3n_q (a3n_T X)).left = (a3n_q X).left ≫ a3n_σ X a := by
  rw [a3k_ι, Over.whiskerRight_left]
  exact pullback.lift_fst _ _ _

theorem a3k_ρ_q : a3k_ρ X ≫ (a3n_q X).left = (a3n_q (a3n_T X)).left ≫ (a3n_q X).left := by
  rw [a3k_ρ, Over.whiskerRight_left]
  exact pullback.lift_fst _ _ _

theorem a3k_ρ_h : a3k_ρ X ≫ a3n_h X = a3n_h (a3n_T X) := by
  rw [← Category.assoc, a3k_ρ_p]

theorem a3k_ρ_h_apply (τ : (a3n_T (a3n_T X)).left) : a3n_h X (a3k_ρ X τ) = a3n_h (a3n_T X) τ := by
  rw [← Scheme.Hom.comp_apply, a3k_ρ_h]

theorem a3k_isPullback (a : ℂ) :
    IsPullback (a3k_ι X a) (a3n_q X).left (a3n_q (a3n_T X)).left (a3n_σ X a) := by
  refine IsPullback.of_right (h₁₂ := a3n_p (a3n_T X)) (h₂₂ := (a3n_T X).hom)
    (v₁₃ := a3n_P1.hom) ?_ (a3k_ι_q X a) ?_
  · rw [a3k_ι_p, show a3n_σ X a ≫ (a3n_T X).hom = X.hom from (a3k_σO X a).w]
    exact (IsPullback.of_hasPullback X.hom a3n_P1.hom).flip
  · exact (IsPullback.of_hasPullback (a3n_T X).hom a3n_P1.hom).flip

/-- The image of `ι_a` is the fibre `t = a`. -/
theorem a3k_range_ι (a : ℂ) :
    Set.range (a3k_ι X a) = (a3n_q (a3n_T X)).left ⁻¹' Set.range (a3n_σ X a) := by
  have h := a3k_isPullback X a
  have e : a3k_ι X a = h.isoPullback.hom ≫ pullback.fst (a3n_q (a3n_T X)).left (a3n_σ X a) :=
    (h.isoPullback_hom_fst).symm
  rw [e, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.2 h.isoPullback.hom.surjective, Set.image_univ, Scheme.Pullback.range_fst]

theorem a3k_ι_cl (a : ℂ) (x : (a3n_T X).left) (τ : (a3n_T (a3n_T X)).left)
    (h : a3k_ι X a x ⤳ τ) : τ ∈ Set.range (a3k_ι X a) := by
  rw [a3k_range_ι]
  have h1 := h.map (a3n_q (a3n_T X)).left.continuous
  rw [← Scheme.Hom.comp_apply, a3k_ι_q, Scheme.Hom.comp_apply] at h1
  exact a3n_mem_range_σ_of_specializes X a h1

theorem a3k_ι_strictMono (a : ℂ) : StrictMono (a3k_ι X a) := by
  intro u v huv
  have h1 : v ⤳ u := Scheme.le_iff_specializes.1 huv.le
  refine lt_of_le_not_ge (Scheme.le_iff_specializes.2 (h1.map (a3k_ι X a).continuous)) ?_
  intro hle
  apply huv.not_ge
  have := (Scheme.le_iff_specializes.1 hle).map (a3k_ρ X).continuous
  rw [a3k_ρ_ι_apply, a3k_ρ_ι_apply] at this
  exact Scheme.le_iff_specializes.2 this

/-- `ι_a` preserves heights. -/
theorem a3k_height_ι (a : ℂ) (x : (a3n_T X).left) : height (a3k_ι X a x) = height x := by
  refine (Order.height_eq_of_strictMono (a3k_ι X a) (a3k_ι_strictMono X a) (fun u v hv => ?_)
    x).symm
  obtain ⟨u', rfl⟩ := a3k_ι_cl X a u v (Scheme.le_iff_specializes.1 hv.le)
  refine ⟨u', lt_of_le_not_ge ?_ ?_, rfl⟩
  · have := (Scheme.le_iff_specializes.1 hv.le).map (a3k_ρ X).continuous
    rw [a3k_ρ_ι_apply, a3k_ρ_ι_apply] at this
    exact Scheme.le_iff_specializes.2 this
  · intro hle
    exact hv.not_ge (Scheme.le_iff_specializes.2
      ((Scheme.le_iff_specializes.1 hle).map (a3k_ι X a).continuous))

/-- `codim ι_a(x) = codim x + 1`. -/
theorem a3k_coheight_ι [IsIntegral X.left] [LocallyOfFiniteType X.hom] (a : ℂ)
    (x : (a3n_T X).left) : coheight (a3k_ι X a x) = coheight x + 1 := by
  obtain ⟨-, n, hn, -⟩ := a1d_height_eq_trdeg (X := X) (genericPoint X.left)
  have hT := a3n_height_add_coheight_T X n hn (genericPoint (a3n_T X).left)
  rw [a3k_coheight_genericPoint, add_zero] at hT
  have h2 := a3n_height_add_coheight_T (a3n_T X) (n + 1) hT (a3k_ι X a x)
  have h1 := a3n_height_add_coheight_T X n hn x
  rw [a3k_height_ι] at h2
  have hfin : height x ≠ ⊤ := fun h => by rw [h, top_add] at h1; exact ENat.top_ne_natCast _ h1
  obtain ⟨h, hh⟩ := ENat.ne_top_iff_exists.1 hfin
  rw [← hh] at h1 h2
  have hc1 : coheight x ≠ ⊤ := fun h' => by rw [h', add_top] at h1; exact ENat.top_ne_natCast _ h1
  have hc2 : coheight (a3k_ι X a x) ≠ ⊤ := fun h' => by
    rw [h', add_top] at h2; exact ENat.top_ne_natCast _ h2
  obtain ⟨c₁, hc₁⟩ := ENat.ne_top_iff_exists.1 hc1
  obtain ⟨c₂, hc₂⟩ := ENat.ne_top_iff_exists.1 hc2
  rw [← hc₁] at h1 ⊢
  rw [← hc₂] at h2 ⊢
  have e1 : h + c₁ = n + 1 := by exact_mod_cast h1
  have e2 : h + c₂ = n + 1 + 1 := by exact_mod_cast h2
  norm_cast
  omega

end maps

section transport

/-- Germs pulled back along `h_B = r ≫ h_A`, read at `τ` with `r τ = w`. -/
theorem a3k_stalkMap_transport {A B P : Scheme.{0}} (r : B ⟶ A) (hA : A ⟶ P) (hB : B ⟶ P)
    (hh : r ≫ hA = hB) (τ : B) (w : A) (e : r τ = w) (a₀ : P.presheaf.stalk (hA w)) :
    ∃ a₁ : P.presheaf.stalk (hB τ),
      hB.stalkMap τ a₁ = r.stalkMap τ ((A.presheaf.stalkCongr (.of_eq e)).inv (hA.stalkMap w a₀)) ∧
      ∀ (g : P) (hg : g ⤳ hB τ) (hg' : g ⤳ hA w),
        P.presheaf.stalkSpecializes hg a₁ = P.presheaf.stalkSpecializes hg' a₀ := by
  subst hh e
  refine ⟨a₀, ?_, fun _ _ _ => rfl⟩
  rw [Scheme.Hom.stalkMap_comp]
  simp [TopCat.Presheaf.stalkCongr, TopCat.Presheaf.stalkSpecializes_refl]

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProper X.hom]

omit [IsIntegral X.left] [Smooth X.hom] [IsProper X.hom] in
theorem a3k_h_ι (a : ℂ) (w : (a3n_T X).left) :
    a3n_h (a3n_T X) (a3k_ι X a w) = a3n_h X w := by
  rw [← a3k_ρ_h_apply, a3k_ρ_ι_apply]

omit [Smooth X.hom] [IsProper X.hom] in
/-- `t|_Y` as the restriction of a germ pulled back from `ℙ¹`. -/
theorem a3k_φ_eq_germZ {Y : Over (Spec ↧ℂ)} (y : (a3n_T Y).left)
    (hy : a3n_h Y y = genericPoint (g3c_P 1))
    (a₀ : a3m_P1curve.C.presheaf.stalk (a3n_h Y y))
    (hat : a3m_P1curve.C.presheaf.stalkSpecializes (genericPoint_specializes _) a₀ =
      a3m_P1curve.t) :
    a3o_φ Y y hy = a3z_germZ y ((a3n_h Y).stalkMap y a₀) :=
  (a3o_germ_pullback Y y hy y _ (a3m_cycleComponentι_genericPoint _ y) a₀ hat).symm

/-- **Transport along `ι_a`**: `ρ_*[div (s|_{ι_a(Y)})] = [div (s|_Y)]` for `Y ⊆ X × ℙ¹_s`
dominating `ℙ¹_s`. -/
theorem a3k_push_ι (a : ℂ) (w : (a3n_T X).left) (hw : a3n_h X w = genericPoint (g3c_P 1)) :
    a1p_pushforward (a3k_ρ X) (a3o_cyc (a3n_T X) (a3k_ι X a w) ((a3k_h_ι X a w).trans hw)) =
      a3o_cyc X w hw := by
  have hw0 : a3n_h X w ∉ a3m_Z0 := by rw [hw]; exact a3k_generic_not_mem_Z0
  have hw1 : a3n_h X w ∉ a3m_Zinf := by rw [hw]; exact a3k_generic_not_mem_Zinf
  obtain ⟨a₀, ha₀, hat⟩ := a3m_P1curve.unit _ hw0 hw1
  set θ := (a3n_h X).stalkMap w a₀
  have hθ : θ ∉ IsLocalRing.maximalIdeal _ := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
    exact ha₀.map _
  obtain ⟨a₁, he, hsp⟩ := a3k_stalkMap_transport (a3k_ρ X) (a3n_h X) (a3n_h (a3n_T X))
    (a3k_ρ_h X) (a3k_ι X a w) w (a3k_ρ_ι_apply X a w) a₀
  have hat₁ : a3m_P1curve.C.presheaf.stalkSpecializes (genericPoint_specializes _) a₁ =
      a3m_P1curve.t := (hsp _ _ (genericPoint_specializes _)).trans hat
  have e1 := a3k_φ_eq_germZ w hw a₀ hat
  have e2 := a3k_φ_eq_germZ (Y := a3n_T X) (a3k_ι X a w) ((a3k_h_ι X a w).trans hw) a₁ hat₁
  rw [he] at e2
  unfold a3o_cyc
  rw [e1, e2]
  exact a3k_push_retract (A := a3n_T X) (B := a3n_T (a3n_T X)) (a3k_ι X a) (a3k_ρ X)
    (a3k_ι_ρ X a) (a3k_ι_cl X a) 1 (fun x => by rw [a3k_coheight_ι]; rfl) w θ hθ

end transport

section linear
variable (X : Over (Spec ↧ℂ)) [IsProper X.hom]

omit [IsProper X.hom] in
theorem a3k_pushforward_congr {Y Y' : Scheme.{0}} {f g : Y ⟶ Y'} [QuasiCompact f]
    [QuasiCompact g] (h : f = g) (c : AlgebraicCycle Y ℚ) :
    a1p_pushforward f c = a1p_pushforward g c := by
  subst h
  rfl

theorem a3k_bd_sum {ι : Type*} (s : Finset ι) (F : ι → AlgebraicCycle (a3n_T X).left ℚ) :
    a3k_bd X (∑ i ∈ s, F i) = ∑ i ∈ s, a3k_bd X (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using a3k_bd_zero X
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, a3k_bd_add, ih]

open Classical in
/-- An intersection cycle of two points is the sum of its components with their multiplicities. -/
theorem a3k_intersectPrime_eq_sum (Y : Scheme.{0}) [IsNoetherian Y] (u v : Y) :
    a3i_intersectPrime Y u v = ∑ z ∈ (a3y_comps_finite u v).toFinset,
      a3m_smul (a3i_serreMult Y z u v : ℚ) (Function.locallyFinsuppWithin.single z 1) := by
  ext x
  rw [a3y_intersectPrime_apply, a3m_sum_apply]
  simp only [a3m_smul_apply, Function.locallyFinsuppWithin.single_apply, mul_ite, mul_one,
    mul_zero]
  rw [Finset.sum_ite_eq]
  by_cases hx : x ∈ a3y_comps u v
  · have hx' : x ∈ (a3y_comps_finite u v).toFinset := (Set.Finite.mem_toFinset _).2 hx
    simp only [hx', ite_true]
    split_ifs with h
    · rfl
    · exact absurd hx h
  · have hx' : x ∉ (a3y_comps_finite u v).toFinset := fun h => hx ((Set.Finite.mem_toFinset _).1 h)
    simp only [hx', ite_false]
    split_ifs with h
    · exact absurd h hx
    · rfl

end linear

section square
variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

/-- The generic point of the face `t = a` of `(X × ℙ¹_t) × ℙ¹_s`, `(X × {a}) × ℙ¹`.
Source: Fulton, *Intersection Theory*, second edition, §1.6 (the fibres of `X × ℙ¹`). -/
abbrev a3k_E (a : ℂ) : (a3n_T (a3n_T X)).left :=
  a3n_b (a3n_T X) (a3n_σ X a (genericPoint X.left))

example (a : ℂ) : a3k_E X a = a3n_b (a3n_T X) (a3n_σ X a (genericPoint X.left)) := rfl

open Classical in
/-- The boundary in `t` of a two-parameter chain: `ρ_*(W · [div t])`, with
`[div t] = m₀ [t = 0] + m₁ [t = 1]` the divisor of the coordinate (`a3k_cycT`), read on
`X × ℙ¹_s`.
Source: S. Bloch, *The moving lemma for higher Chow groups*, J. Algebraic Geom. 3 (1994), §1
(the faces of the cubical complex `z^p(X, •)`); Fulton, *Intersection Theory*, second edition,
§1.6 and §2.3. -/
def a3k_dt (W : AlgebraicCycle (a3n_T (a3n_T X)).left ℚ) : AlgebraicCycle (a3n_T X).left ℚ :=
  a1p_pushforward (a3k_ρ X)
    (a3m_smul (a3k_cycT X (a3n_σ X 0 (genericPoint X.left)))
        (a3i_intersect (a3n_T (a3n_T X)).left W (Function.locallyFinsuppWithin.single (a3k_E X 0) 1)) +
      a3m_smul (a3k_cycT X (a3n_σ X 1 (genericPoint X.left)))
        (a3i_intersect (a3n_T (a3n_T X)).left W (Function.locallyFinsuppWithin.single (a3k_E X 1) 1)))

open Classical in
example : a3k_dt X 0 = 0 := by
  have h0 : a3i_intersect (a3n_T (a3n_T X)).left 0
      (Function.locallyFinsuppWithin.single (a3k_E X 0) 1) = 0 := a3o_intersect_zero_left _ _
  have h1 : a3i_intersect (a3n_T (a3n_T X)).left 0
      (Function.locallyFinsuppWithin.single (a3k_E X 1) 1) = 0 := a3o_intersect_zero_left _ _
  rw [a3k_dt, h0, h1]
  have : a3m_smul (a3k_cycT X (a3n_σ X 0 (genericPoint X.left)))
      (0 : AlgebraicCycle (a3n_T (a3n_T X)).left ℚ) +
      a3m_smul (a3k_cycT X (a3n_σ X 1 (genericPoint X.left))) 0 = 0 := by ext; simp
  rw [this, a3k_pushforward_zero]

/-- A member `W` of a two-parameter chain is in square position: it dominates `ℙ¹_s` and
`ℙ¹_t`, the components of `div (s|_W)` dominate `ℙ¹_t`, and no component of `W ∩ (t = a)`,
`a ∈ {0, 1}`, lies over `s ∈ {0, 1}`; so `W` meets the four corners properly.
Source: S. Bloch, *The moving lemma for higher Chow groups*, J. Algebraic Geom. 3 (1994), §1
(cycles meeting all faces properly). -/
structure a3k_SquarePos (w : (a3n_T (a3n_T X)).left) : Prop where
  dom_s : a3n_h (a3n_T X) w = genericPoint (g3c_P 1)
  dom_t : a3n_h X ((a3n_q (a3n_T X)).left w) = genericPoint (g3c_P 1)
  face_s : ∀ d, a3o_cyc (a3n_T X) w dom_s d ≠ 0 →
    a3n_h X ((a3n_q (a3n_T X)).left d) = genericPoint (g3c_P 1)
  face_t : ∀ a : ℂ, (a = 0 ∨ a = 1) → ∀ z ∈ a3y_comps w (a3k_E X a),
    a3n_h (a3n_T X) z ∉ a3m_Z0 ∧ a3n_h (a3n_T X) z ∉ a3m_Zinf

omit [IsProjective X.hom] in
open Classical in
/-- `[div t] = m₀ [X × {0}] + m₁ [X × {1}]` on `X × ℙ¹`. -/
theorem a3k_cycT_eq [IsProper X.hom] : a3k_cycT X =
    a3m_smul (a3k_cycT X (a3n_σ X 0 (genericPoint X.left)))
        (Function.locallyFinsuppWithin.single (a3n_σ X 0 (genericPoint X.left)) 1) +
      a3m_smul (a3k_cycT X (a3n_σ X 1 (genericPoint X.left)))
        (Function.locallyFinsuppWithin.single (a3n_σ X 1 (genericPoint X.left)) 1) := by
  classical
  have hne := a3n_σ0_ne_σ1 X (genericPoint X.left) (genericPoint X.left)
  ext d
  rw [Function.locallyFinsuppWithin.coe_add, Pi.add_apply, a3m_smul_apply, a3m_smul_apply,
    Function.locallyFinsuppWithin.single_apply, Function.locallyFinsuppWithin.single_apply]
  split_ifs with h0 h1 h1
  · exact absurd (h0.symm.trans h1) hne
  · subst h0; ring
  · subst h1; ring
  · rw [mul_zero, mul_zero, add_zero]
    by_contra hd
    rcases a3k_cycT_supp X d hd with h | h
    · exact h0 h
    · exact h1 h

/-- The boundary of a chain whose members dominate `ℙ¹` is `q_*([div t] · Z)`. -/
theorem a3k_bd_eq_push (c : AlgebraicCycle (a3n_T X).left ℚ)
    (hc : ∀ d, c d ≠ 0 → a3n_h X d = genericPoint (g3c_P 1)) :
    a3k_bd X c = a1p_pushforward (a3n_q X).left
      (a3i_intersect (a3n_T X).left (a3k_cycT X) c) := by
  classical
  set s := (a3m_support_finite c).toFinset
  have hs : ∀ d ∉ s, c d = 0 := fun d hd => by simpa [s] using hd
  rw [a3k_bd, a3o_intersect_eq_sum_right (a3n_T X).left _ c s hs, a3k_pushforward_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd' : c d ≠ 0 := by simpa [s] using hd
  rw [a3k_pushforward_smul, a3k_piece_of_dom X d (hc d hd'), a3k_cyc_eq_intersect X d (hc d hd')]

theorem a3k_coheight_E (a : ℂ) : coheight (a3k_E X a) = 1 := by
  rw [a3k_E, a3k_coheight_b (a3n_T X), a3k_coheight_σ_generic]

/-- The components of `U ∩ (t = a)` for `U` dominating `ℙ¹_t` have codimension one more. -/
theorem a3k_coheight_comps_E (u : (a3n_T (a3n_T X)).left)
    (hu : a3n_h X ((a3n_q (a3n_T X)).left u) = genericPoint (g3c_P 1)) (a : ℂ)
    (ha : a = 0 ∨ a = 1) {z : (a3n_T (a3n_T X)).left} (hz : z ∈ a3y_comps u (a3k_E X a)) :
    coheight z = coheight u + 1 := by
  obtain ⟨huz, hEz, -⟩ := a3y_comps_spec _ _ hz
  rw [a3n_b_specializes_iff] at hEz
  have hr := a3n_mem_range_σ_of_specializes X a hEz
  have hne : u ≠ z := by
    rintro rfl
    exact a3k_not_mem_range_σ X hu a ha hr
  refine le_antisymm ?_ (Order.add_one_le_of_lt (a3y_coheight_lt huz hne))
  have h := a3k_coheight_comps_le (a3n_T X) hz
  rwa [a3k_coheight_E] at h

theorem a3k_meet_E (u : (a3n_T (a3n_T X)).left)
    (hu : a3n_h X ((a3n_q (a3n_T X)).left u) = genericPoint (g3c_P 1)) (a : ℂ)
    (ha : a = 0 ∨ a = 1) : a3i_MeetProperly (a3n_T (a3n_T X)).left u (a3k_E X a) := by
  intro w hw
  rw [a3k_coheight_comps_E X u hu a ha ⟨w, hw, rfl⟩, a3k_coheight_E]

omit [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] in
/-- `t|_Z` is the restriction of `t|_W` for `Z ⊆ W` dominating `ℙ¹`. -/
theorem a3k_isRestriction_φ {Y : Over (Spec ↧ℂ)} (w z : (a3n_T Y).left)
    (hw : a3n_h Y w = genericPoint (g3c_P 1)) (hz : a3n_h Y z = genericPoint (g3c_P 1))
    (hwz : w ⤳ z) : a3z_IsRestriction w (a3o_φ Y w hw) z (a3o_φ Y z hz) := by
  obtain ⟨zW, hzW⟩ := a3z_exists_pt w hwz
  have h0 : a3n_h Y z ∉ a3m_Z0 := by rw [hz]; exact a3k_generic_not_mem_Z0
  have h1 : a3n_h Y z ∉ a3m_Zinf := by rw [hz]; exact a3k_generic_not_mem_Zinf
  obtain ⟨a₀, ha₀, hat⟩ := a3m_P1curve.unit _ h0 h1
  refine ⟨zW, hzW, (a3n_h Y).stalkMap z a₀, 1, ?_, ?_, ?_, ?_⟩
  · rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
    exact ha₀.map _
  · rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
    exact isUnit_one
  · rw [map_one, mul_one]
    exact a3o_germ_pullback Y w hw z zW hzW a₀ hat
  · rw [map_one, mul_one]
    exact a3o_germ_pullback Y z hz z _ (a3m_cycleComponentι_genericPoint _ z) a₀ hat

end square

section corner
variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

open Classical in
/-- The restrictions of `s|_W` used on the face `t = a`: `s|_Z` when `Z` dominates `ℙ¹_s`, and
some restriction otherwise. -/
def a3k_ψ (w : (a3n_T (a3n_T X)).left) (hw : a3n_h (a3n_T X) w = genericPoint (g3c_P 1))
    (z : (a3n_T (a3n_T X)).left) : (cycleComponent (a3n_T (a3n_T X)).left z).functionField :=
  if hz : a3n_h (a3n_T X) z = genericPoint (g3c_P 1) then a3o_φ (a3n_T X) z hz
  else if hr : ∃ ψ, ψ ≠ 0 ∧ a3z_IsRestriction w (a3o_φ (a3n_T X) w hw) z ψ then hr.choose
  else 0

example (w : (a3n_T (a3n_T X)).left) (hw : a3n_h (a3n_T X) w = genericPoint (g3c_P 1)) :
    a3k_ψ X w hw w = a3o_φ (a3n_T X) w hw := by
  rw [a3k_ψ, dite_eq_left hw]

theorem a3k_ψ_spec (w : (a3n_T (a3n_T X)).left) (hS : a3k_SquarePos X w) (a : ℂ)
    (ha : a = 0 ∨ a = 1) (z : (a3n_T (a3n_T X)).left) (hz : z ∈ a3y_comps w (a3k_E X a)) :
    a3k_ψ X w hS.dom_s z ≠ 0 ∧
      a3z_IsRestriction w (a3o_φ (a3n_T X) w hS.dom_s) z (a3k_ψ X w hS.dom_s z) := by
  have hwz := (a3y_comps_spec _ _ hz).1
  by_cases hd : a3n_h (a3n_T X) z = genericPoint (g3c_P 1)
  · rw [a3k_ψ, dite_eq_left hd]
    exact ⟨a3o_φ_ne_zero _ _ _, a3k_isRestriction_φ w z hS.dom_s hd hwz⟩
  · have hex : ∃ ψ, ψ ≠ 0 ∧ a3z_IsRestriction w (a3o_φ (a3n_T X) w hS.dom_s) z ψ :=
      a3z_exists_restriction w (a3o_unitAt (a3n_T X) w hS.dom_s z hwz
        (hS.face_t a ha z hz).1 (hS.face_t a ha z hz).2)
    rw [a3k_ψ, dite_eq_right hd, dite_eq_left hex]
    exact hex.choose_spec

omit [IsProjective X.hom] in
/-- A component of `W ∩ (t = a)` lies on the image of `ι_a`. -/
theorem a3k_comps_E_mem_range (w : (a3n_T (a3n_T X)).left) (a : ℂ)
    {z : (a3n_T (a3n_T X)).left} (hz : z ∈ a3y_comps w (a3k_E X a)) :
    z ∈ Set.range (a3k_ι X a) := by
  have hEz := (a3y_comps_spec _ _ hz).2.1
  rw [a3n_b_specializes_iff] at hEz
  rw [a3k_range_ι]
  exact a3n_mem_range_σ_of_specializes X a hEz

open Classical in
/-- The corner terms: on a component `Z` of `W ∩ (t = a)`, pushing `[div (s|_Z)]` to `X` is the
boundary of `ρ(Z)`, a member of a chain on `X × ℙ¹_s`. -/
theorem a3k_corner (w : (a3n_T (a3n_T X)).left) (hS : a3k_SquarePos X w) (a : ℂ)
    (ha : a = 0 ∨ a = 1) (z : (a3n_T (a3n_T X)).left) (hz : z ∈ a3y_comps w (a3k_E X a)) :
    a1p_pushforward (a3n_q X).left (a1p_pushforward (a3n_q (a3n_T X)).left
        (a2_principalCycle (a3n_T (a3n_T X)).left ℚ z (a3k_ψ X w hS.dom_s z))) =
      a3k_bd X (a1p_pushforward (a3k_ρ X) (Function.locallyFinsuppWithin.single z 1)) := by
  obtain ⟨z'', rfl⟩ := a3k_comps_E_mem_range X w a hz
  rw [a1p_pushforward_single, a3k_degree_r_i _ _ (a3k_ι_ρ X a), a3k_ρ_ι_apply, Nat.cast_one,
    one_mul, a3k_bd_single]
  by_cases hd : a3n_h X z'' = genericPoint (g3c_P 1)
  · have hd' : a3n_h (a3n_T X) (a3k_ι X a z'') = genericPoint (g3c_P 1) :=
      (a3k_h_ι X a z'').trans hd
    rw [a3k_ψ, dite_eq_left hd', a3k_piece_of_dom X z'' hd, ← a3k_push_ι X a z'' hd,
      ← a1p_pushforward_comp, ← a1p_pushforward_comp]
    exact a3k_pushforward_congr (a3k_ρ_q X).symm _
  · have hd' : a3n_h (a3n_T X) (a3k_ι X a z'') ≠ genericPoint (g3c_P 1) := by
      rwa [a3k_h_ι]
    have hpiece : a3k_piece X z'' = 0 := by
      unfold a3k_piece
      rw [dite_eq_right hd]
    rw [hpiece]
    obtain ⟨hψ0, hψ⟩ := a3k_ψ_spec X w hS a ha _ hz
    have hzero : a2_principalCycle (a3n_T (a3n_T X)).left ℚ (a3k_ι X a z'')
        (a3k_ψ X w hS.dom_s (a3k_ι X a z'')) = 0 := by
      ext τ
      rw [Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply]
      by_cases hzτ : a3k_ι X a z'' ⤳ τ
      · -- `τ` lies over the same point of `ℙ¹_s` as `Z`
        have hp : a3n_p (a3n_T X) (a3k_ι X a z'') = a3n_p (a3n_T X) τ := by
          by_contra hne
          have hgen := a3k_P1_eq_generic (hzτ.map (a3n_p (a3n_T X)).continuous) hne
          apply hd'
          change a3n_π (a3n_p (a3n_T X) (a3k_ι X a z'')) = _
          rw [hgen, a3k_π_generic]
        have hh : a3n_h (a3n_T X) τ = a3n_h (a3n_T X) (a3k_ι X a z'') := by
          change a3n_π (a3n_p (a3n_T X) τ) = a3n_π (a3n_p (a3n_T X) (a3k_ι X a z''))
          rw [hp]
        exact a3o_restriction_ord_zero (a3n_T X) w hS.dom_s (a3k_E X a) _ hz _ hψ hψ0 τ
          (hh ▸ (hS.face_t a ha _ hz).1) (hh ▸ (hS.face_t a ha _ hz).2)
      · refine a3y_principalCycle_apply_of_not_mem _ _ _ _ ?_
        rintro ⟨D, rfl⟩
        exact hzτ (a3z_specializes_pt _ D)
    rw [hzero, a3k_pushforward_zero, a3k_pushforward_zero]

end corner

section commute
variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

open Classical in
/-- One face: `q_*([t = a] · ∂_s W) = ∂_t` of the face `W ∩ (t = a)` read on `X × ℙ¹_s`. -/
theorem a3k_face (w : (a3n_T (a3n_T X)).left) (hS : a3k_SquarePos X w) (a : ℂ)
    (ha : a = 0 ∨ a = 1) :
    a1p_pushforward (a3n_q X).left (a3i_intersect (a3n_T X).left
        (Function.locallyFinsuppWithin.single (a3n_σ X a (genericPoint X.left)) 1)
        (a1p_pushforward (a3n_q (a3n_T X)).left (a3o_cyc (a3n_T X) w hS.dom_s))) =
      a3k_bd X (a1p_pushforward (a3k_ρ X) (a3i_intersectPrime (a3n_T (a3n_T X)).left w
        (a3k_E X a))) := by
  have hi : ∀ z ∈ a3y_comps w (a3k_E X a), a3n_p (a3n_T X) z ∈ Set.range (a3m_Pnκ 1 0) →
      coheight z = coheight w + coheight (a3k_E X a) := fun z hz _ => by
    rw [a3k_coheight_comps_E X w hS.dom_t a ha hz, a3k_coheight_E]
  have hii : ∀ d, a3o_cyc (a3n_T X) w hS.dom_s d ≠ 0 →
      a3i_MeetProperly (a3n_T (a3n_T X)).left d (a3k_E X a) := fun d hd =>
    a3k_meet_E X d (hS.face_s d hd) a ha
  rw [a3k_intersect_symm, ← a3o_push_intersect (a3n_T X) _ (a3o_cyc_supp _ w hS.dom_s),
    a3o_identity (a3n_T X) w hS.dom_s _ hi hii (a3k_ψ X w hS.dom_s)
      (fun z hz => a3k_ψ_spec X w hS a ha z hz),
    a3k_intersectPrime_eq_sum, a3k_pushforward_sum, a3k_pushforward_sum, a3k_pushforward_sum,
    a3k_bd_sum]
  refine Finset.sum_congr rfl fun z hz => ?_
  rw [Set.Finite.mem_toFinset] at hz
  change a1p_pushforward _ (a1p_pushforward _ (a3m_smul _ _)) = _
  rw [a3k_pushforward_smul, a3k_pushforward_smul, a3k_pushforward_smul, a3k_bd_smul,
    a3k_corner X w hS a ha z hz]

open Classical in
/-- **The boundary of the boundary of a member in square position**: `∂_t ∂_s W = ∂_s ∂_t W`. -/
theorem a3k_bd_piece (w : (a3n_T (a3n_T X)).left) (hS : a3k_SquarePos X w) :
    a3k_bd X (a3k_piece (a3n_T X) w) =
      a3m_smul (a3k_cycT X (a3n_σ X 0 (genericPoint X.left)))
          (a3k_bd X (a1p_pushforward (a3k_ρ X)
            (a3i_intersectPrime (a3n_T (a3n_T X)).left w (a3k_E X 0)))) +
        a3m_smul (a3k_cycT X (a3n_σ X 1 (genericPoint X.left)))
          (a3k_bd X (a1p_pushforward (a3k_ρ X)
            (a3i_intersectPrime (a3n_T (a3n_T X)).left w (a3k_E X 1)))) := by
  have hsupp : ∀ d, a1p_pushforward (a3n_q (a3n_T X)).left (a3o_cyc (a3n_T X) w hS.dom_s) d ≠ 0 →
      a3n_h X d = genericPoint (g3c_P 1) := by
    intro d hd
    rw [a3o_pushforward_apply (a3n_T X) _ (a3o_cyc_supp _ w hS.dom_s)] at hd
    by_cases h0 : a3o_cyc (a3n_T X) w hS.dom_s (a3n_σ (a3n_T X) 0 d) = 0
    · rw [h0, zero_add] at hd
      have := hS.face_s _ hd
      rwa [a3n_q_σ_apply] at this
    · have := hS.face_s _ h0
      rwa [a3n_q_σ_apply] at this
  rw [a3k_piece_of_dom (a3n_T X) w hS.dom_s, a3k_bd_eq_push X _ hsupp]
  conv_lhs => rw [a3k_cycT_eq X]
  rw [a3o_intersect_add_left, a3o_intersect_smul_left, a3o_intersect_smul_left,
    a1p_pushforward_add, a3k_pushforward_smul, a3k_pushforward_smul,
    a3k_face X w hS 0 (Or.inl rfl), a3k_face X w hS 1 (Or.inr rfl)]

open Classical in
/-- The intersection with a prime cycle is the sum over the members. -/
theorem a3k_intersect_single_eq_sum (Y : Scheme.{0}) (c : AlgebraicCycle Y ℚ) (v : Y)
    (s : Finset Y) (hs : ∀ u ∉ s, c u = 0) :
    a3i_intersect Y c (Function.locallyFinsuppWithin.single v 1) =
      ∑ u ∈ s, a3m_smul (c u) (a3i_intersectPrime Y u v) := by
  ext T
  rw [a3z_intersect_single_apply Y c v s hs T, a3m_sum_apply]
  rfl

/-- **`∂∂ = 0` for two-parameter chains in square position**: the boundary in `t` of the
boundary in `s` equals the boundary in `s` of the boundary in `t`.
Source: S. Bloch, *The moving lemma for higher Chow groups*, J. Algebraic Geom. 3 (1994), §1
(the cubical complex `z^p(X, •)`); Fulton, *Intersection Theory*, second edition, Theorem 2.4
(commutativity of intersecting with divisors). -/
theorem a3k_bd_bd (W : AlgebraicCycle (a3n_T (a3n_T X)).left ℚ)
    (hW : ∀ w, W w ≠ 0 → a3k_SquarePos X w) :
    a3k_bd X (a3k_bd (a3n_T X) W) = a3k_bd X (a3k_dt X W) := by
  classical
  set s := (a3m_support_finite W).toFinset
  have hs : ∀ w ∉ s, W w = 0 := fun w hw => by simpa [s] using hw
  have hmem : ∀ w ∈ s, a3k_SquarePos X w := fun w hw => hW w (by simpa [s] using hw)
  rw [show a3k_bd (a3n_T X) W = ∑ w ∈ s, a3m_smul (W w) (a3k_piece (a3n_T X) w) from rfl,
    a3k_bd_sum, a3k_dt, a3k_intersect_single_eq_sum _ W _ s hs,
    a3k_intersect_single_eq_sum _ W _ s hs, a3m_smul_sum, a3m_smul_sum, ← Finset.sum_add_distrib,
    a3k_pushforward_sum, a3k_bd_sum]
  refine Finset.sum_congr rfl fun w hw => ?_
  rw [a3k_bd_smul, a3k_bd_piece X w (hmem w hw), a1p_pushforward_add, a3k_pushforward_smul,
    a3k_pushforward_smul, a3k_pushforward_smul, a3k_pushforward_smul, a3k_bd_add, a3k_bd_smul,
    a3k_bd_smul, a3k_bd_smul, a3k_bd_smul]
  ext x
  simp only [a3m_smul_apply, Function.locallyFinsuppWithin.coe_add, Pi.add_apply]
  ring

end commute

end HodgeLean.Adapters
