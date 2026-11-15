import HodgeLean.Adapters.IntersectionProductBlochGraph

/-! # Principal cycles along a section of a retraction

Let `r : B → A` be a morphism of schemes with a section `i : A → B` (`i ≫ r = 𝟙`) whose image is
stable under specialization. At `i x` the retraction gives a local map
`f = r^# : 𝒪_{A,x} → 𝒪_{B,i x}` with `i^# ∘ f = id` (`a3k_rg_rf`), and the prime of `i e` at
`i x` is the preimage of the prime of `e` under `i^#` (`a3k_stalkIdeal_i`). For a point `w` of
`A` and a germ `θ ∉ 𝔪_w`, the principal cycle of `f θ` restricted to `closure {i w}` pushes
forward along `r` to the principal cycle of `θ` restricted to `closure {w}`
(`a3k_push_retract`). This generalizes `a3k_push_σ` from the sections `σ_c` of `X × ℙ¹ → X` to
any section of a retraction which shifts codimensions by a constant.

Source: Fulton, *Intersection Theory*, second edition, §1.4 and Proposition 1.4 (push-forward of
a principal divisor along a birational map of the supports); Hartshorne, *Algebraic Geometry*,
II, §2 (stalk maps). HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Order

set_option backward.isDefEq.respectTransparency false

namespace HodgeLean.Adapters

section stalks
variable {A B : Scheme.{0}} (i : A ⟶ B) (r : B ⟶ A) (hir : i ≫ r = 𝟙 A)

include hir in
theorem a3k_ri (x : A) : r (i x) = x := by
  rw [← Scheme.Hom.comp_apply, hir]
  rfl

/-- The stalk map of the retraction at `i x`, read from `𝒪_{A,x}`.
Source: Hartshorne, *Algebraic Geometry*, II, §2 (morphisms of locally ringed spaces). -/
def a3k_rf (x : A) : A.presheaf.stalk x ⟶ B.presheaf.stalk (i x) :=
  (A.presheaf.stalkCongr (.of_eq (a3k_ri i r hir x))).inv ≫ r.stalkMap (i x)

example (x : A) : A.presheaf.stalk x ⟶ B.presheaf.stalk (i x) := a3k_rf i r hir x

theorem a3k_stalkMap_r_i (x : A) :
    r.stalkMap (i x) ≫ i.stalkMap x =
      (A.presheaf.stalkCongr (.of_eq (a3k_ri i r hir x))).hom := by
  rw [← Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_congr_hom (i ≫ r) (𝟙 _) hir x,
    Scheme.Hom.stalkMap_id]
  erw [Category.comp_id]

theorem a3k_rg_rf (x : A) (a : A.presheaf.stalk x) : i.stalkMap x (a3k_rf i r hir x a) = a := by
  have h := a3k_stalkMap_r_i i r hir x
  change ((a3k_rf i r hir x) ≫ i.stalkMap x) a = a
  rw [a3k_rf, Category.assoc, h, Iso.inv_hom_id]
  rfl

omit hir in
/-- The prime of a point `i e` at `i x` is the preimage of the prime of `e`. -/
theorem a3k_stalkIdeal_i {e x : A} (he : e ⤳ x) :
    a3i_stalkIdeal B (i x) (i e) = (a3i_stalkIdeal A x e).comap (i.stalkMap x).hom :=
  (a3y_comap_stalkIdeal i he).symm

/-- The pull-back along the retraction commutes with specialization along the section. -/
theorem a3k_rf_natural {w x : A} (hwx : w ⤳ x) (α : A.presheaf.stalk x) :
    a3k_rf i r hir w (A.presheaf.stalkSpecializes hwx α) =
      B.presheaf.stalkSpecializes (hwx.map i.continuous) (a3k_rf i r hir x α) := by
  change r.stalkMap (i w) ((A.presheaf.stalkCongr (.of_eq (a3k_ri i r hir w))).inv
        (A.presheaf.stalkSpecializes hwx α)) =
    B.presheaf.stalkSpecializes _ (r.stalkMap (i x)
      ((A.presheaf.stalkCongr (.of_eq (a3k_ri i r hir x))).inv α))
  rw [← Scheme.Hom.stalkSpecializes_stalkMap_apply]
  congr 1
  dsimp only [TopCat.Presheaf.stalkCongr]
  rw [TopCat.Presheaf.stalkSpecializes_comp_apply, TopCat.Presheaf.stalkSpecializes_comp_apply]

theorem a3k_rf_mem_maximalIdeal {x : A} {m : A.presheaf.stalk x}
    (hm : m ∈ IsLocalRing.maximalIdeal _) : a3k_rf i r hir x m ∈ IsLocalRing.maximalIdeal _ := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hm ⊢
  intro hu
  apply hm
  have := hu.map (i.stalkMap x).hom
  rwa [show (i.stalkMap x).hom (a3k_rf i r hir x m) = m from a3k_rg_rf i r hir x m] at this

/-- Restrictions to `W` transport to restrictions to `i(W)`. -/
theorem a3k_germ_transport_i (w : A) (θ : A.presheaf.stalk w) (xW : cycleComponent A w)
    (D : cycleComponent B (i w))
    (hD : cycleComponentι B (i w) D = i (cycleComponentι A w xW))
    (α β : A.presheaf.stalk (cycleComponentι A w xW))
    (hab : a3y_germ w xW rfl α = a3z_germZ w θ * a3y_germ w xW rfl β) :
    a3y_germ (i w) D hD (a3k_rf i r hir _ α) =
      a3z_germZ (i w) (a3k_rf i r hir w θ) * a3y_germ (i w) D hD (a3k_rf i r hir _ β) := by
  set x := cycleComponentι A w xW
  have hwx : w ⤳ x := a3z_specializes_pt w xW
  have hσ : i w ⤳ i x := hwx.map i.continuous
  have hW : ∀ c, a3y_germ w xW rfl c = a3z_germZ w (A.presheaf.stalkSpecializes hwx c) :=
    fun c => a3z_germ_specializes w _ xW (a3m_cycleComponentι_genericPoint _ w) rfl hwx c
  have hT : ∀ c, a3y_germ (i w) D hD c =
      a3z_germZ (i w) (B.presheaf.stalkSpecializes hσ c) :=
    fun c => a3z_germ_specializes (i w) _ D (a3m_cycleComponentι_genericPoint _ _) hD hσ c
  rw [hW, hW, ← map_mul, ← sub_eq_zero, ← map_sub, a3z_germZ_eq_zero_iff] at hab
  have hm := a3k_rf_mem_maximalIdeal i r hir hab
  rw [map_sub, map_mul] at hm
  rw [hT, hT, ← a3k_rf_natural, ← a3k_rf_natural, ← map_mul, ← sub_eq_zero, ← map_sub,
    a3z_germZ_eq_zero_iff]
  exact hm

/-- The order of a restriction along `i(W)` is the order along `W`. -/
theorem a3k_ord_transport_i [IsLocallyNoetherian A] [IsLocallyNoetherian B] (w : A)
    (xW : cycleComponent A w) (D : cycleComponent B (i w))
    (hD : cycleComponentι B (i w) D = i (cycleComponentι A w xW))
    (hx1 : coheight xW = 1) (hD1 : coheight D = 1)
    (α : A.presheaf.stalk (cycleComponentι A w xW))
    (hα : α ∉ a3i_stalkIdeal A (cycleComponentι A w xW) w) :
    (cycleComponent B (i w)).ord (a3y_germ (i w) D hD (a3k_rf i r hir _ α)) D =
      (cycleComponent A w).ord (a3y_germ w xW rfl α) xW := by
  have hwx : w ⤳ cycleComponentι A w xW := a3z_specializes_pt w xW
  have : (a3i_stalkIdeal A (cycleComponentι A w xW) w).IsPrime :=
    a3q_stalkIdeal_isPrime A hwx
  have hfα : a3k_rf i r hir _ α ∉ a3i_stalkIdeal B (i (cycleComponentι A w xW)) (i w) := by
    rw [a3k_stalkIdeal_i i hwx, Ideal.mem_comap,
      show (i.stalkMap _).hom (a3k_rf i r hir _ α) = α from a3k_rg_rf i r hir _ α]
    exact hα
  rw [a3y_ord_germ_self (i w) D hD hD1 _ hfα, a3y_ord_germ_self w xW rfl hx1 _ hα,
    a3k_stalkIdeal_i i hwx]
  exact a3k_herbrand_retract (a3k_rf i r hir _).hom (i.stalkMap _).hom (a3k_rg_rf i r hir _) _ α hα

end stalks

section push
variable {A B : Over (Spec ↧ℂ)} [IsIntegral A.left] [LocallyOfFiniteType A.hom]
  [IsNoetherian A.left] [IsIntegral B.left] [LocallyOfFiniteType B.hom] [IsNoetherian B.left]
  (i : A.left ⟶ B.left) (r : B.left ⟶ A.left) [QuasiCompact r] (hir : i ≫ r = 𝟙 A.left)

omit [IsIntegral A.left] [LocallyOfFiniteType A.hom] [AlgebraicGeometry.IsNoetherian A.left]
  [IsIntegral B.left] [LocallyOfFiniteType B.hom] [AlgebraicGeometry.IsNoetherian B.left]
  [QuasiCompact r] in
include hir in
/-- The retraction has degree one along the section. -/
theorem a3k_degree_r_i (x : A.left) : a1p_degree r (i x) = 1 := by
  have h := a1p_degree_comp i r x
  rw [hir] at h
  have h1 : a1p_degree (𝟙 A.left) x = 1 := a3m_degree_closedImmersion (𝟙 A.left) x
  rw [h1] at h
  exact Nat.eq_one_of_mul_eq_one_right h.symm

/-- **Transport along a section of a retraction**: `r_*[div ((r^# θ)|_{i(W)})] = [div θ]`, when
the image of `i` is stable under specialization and `i` raises codimensions by `δ`. -/
theorem a3k_push_retract (hcl : ∀ (x : A.left) (τ : B.left), i x ⤳ τ → τ ∈ Set.range i)
    (δ : ℕ) (hδ : ∀ x, coheight (i x) = coheight x + δ) (w : A.left)
    (θ : A.left.presheaf.stalk w) (hθ : θ ∉ IsLocalRing.maximalIdeal _) :
    a1p_pushforward r (a2_principalCycle B.left ℚ (i w) (a3z_germZ (i w) (a3k_rf i r hir w θ))) =
      a2_principalCycle A.left ℚ w (a3z_germZ w θ) := by
  classical
  set ψ := a3z_germZ (i w) (a3k_rf i r hir w θ)
  have hψ : ψ ≠ 0 := fun h0 =>
    ((a3z_germZ_eq_zero_iff _ _).1 h0) |> fun hm => hθ (by
      have := a3k_map_mem_maximalIdeal (i.stalkMap w).hom hm
      rwa [show (i.stalkMap w).hom (a3k_rf i r hir w θ) = θ from a3k_rg_rf i r hir w θ] at this)
  have hθ' : a3z_germZ w θ ≠ 0 := fun h0 => hθ ((a3z_germZ_eq_zero_iff _ _).1 h0)
  have hinj : Function.Injective i := fun a b h => by
    rw [← a3k_ri i r hir a, ← a3k_ri i r hir b, h]
  ext x
  rw [a1p_pushforward_apply_eq_sum _ _ x {i x}]
  rotate_left
  · rintro y ⟨hy, hyc⟩
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hy
    have hr : y ∈ Set.range (cycleComponentι B.left (i w)) := by
      by_contra hr
      exact hyc (a3y_principalCycle_apply_of_not_mem _ _ _ _ hr)
    obtain ⟨Y, rfl⟩ := hr
    obtain ⟨e, he⟩ := hcl w _ (a3z_specializes_pt _ Y)
    rw [Finset.coe_singleton, Set.mem_singleton_iff, ← he, ← hy, ← he, a3k_ri i r hir]
  · intro y hy
    rw [Finset.coe_singleton, Set.mem_singleton_iff] at hy
    rw [hy, Set.mem_preimage, Set.mem_singleton_iff, a3k_ri i r hir]
  rw [Finset.sum_singleton, a3k_degree_r_i i r hir, Nat.cast_one, mul_one]
  by_cases hwx : w ⤳ x
  · obtain ⟨xW, rfl⟩ := a3z_exists_pt w hwx
    obtain ⟨D, hD⟩ := a3z_exists_pt (i w) (hwx.map i.continuous)
    rw [← hD, a3y_principalCycle_apply _ _ _ hψ D, a3y_principalCycle_apply _ _ _ hθ' xW]
    congr 1
    have hcoh : coheight D = 1 ↔ coheight xW = 1 := by
      rw [a3y_coheight_eq_one_iff B, a3y_coheight_eq_one_iff A, hD, hδ, hδ, add_right_comm]
      exact ⟨fun h => WithTop.add_right_cancel (ENat.natCast_ne_top δ) h, fun h => by rw [h]⟩
    by_cases h1 : coheight xW = 1
    · have hD1 := hcoh.2 h1
      obtain ⟨n, d, hd, hnd⟩ := IsFractionRing.div_surjective
        (A := (cycleComponent A.left w).presheaf.stalk xW) (a3z_germZ w θ)
      obtain ⟨α, hα⟩ := (cycleComponentι A.left w).stalkMap_surjective xW n
      obtain ⟨β, hβ⟩ := (cycleComponentι A.left w).stalkMap_surjective xW d
      have hd0 : algebraMap _ (cycleComponent A.left w).functionField d ≠ 0 :=
        IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
      have hgα : a3y_germ w xW rfl α = algebraMap _ _ n := by rw [a3y_germ_self, hα]
      have hgβ : a3y_germ w xW rfl β = algebraMap _ _ d := by rw [a3y_germ_self, hβ]
      have hab : a3y_germ w xW rfl α = a3z_germZ w θ * a3y_germ w xW rfl β := by
        rw [hgα, hgβ, ← hnd, div_mul_cancel₀ _ hd0]
      have hβ0 : a3y_germ w xW rfl β ≠ 0 := by rw [hgβ]; exact hd0
      have hα0 : a3y_germ w xW rfl α ≠ 0 := by rw [hab]; exact mul_ne_zero hθ' hβ0
      have hαp : α ∉ a3i_stalkIdeal A.left _ w := fun h =>
        hα0 ((a3y_germ_eq_zero_iff w xW rfl α).2 h)
      have hβp : β ∉ a3i_stalkIdeal A.left _ w := fun h =>
        hβ0 ((a3y_germ_eq_zero_iff w xW rfl β).2 h)
      have hrel := a3k_germ_transport_i i r hir w θ xW D hD α β hab
      have hfβ0 : a3y_germ (i w) D hD (a3k_rf i r hir _ β) ≠ 0 := by
        intro h0
        rw [a3y_germ_eq_zero_iff, a3k_stalkIdeal_i i (a3z_specializes_pt w xW), Ideal.mem_comap,
          show (i.stalkMap _).hom (a3k_rf i r hir _ β) = β from a3k_rg_rf i r hir _ β] at h0
        exact hβp h0
      have e1 := Scheme.ord_mul (x := D) hψ hfβ0
      have e2 := Scheme.ord_mul (x := xW) hθ' hβ0
      rw [← hrel, a3k_ord_transport_i i r hir w xW D hD h1 hD1 α hαp,
        a3k_ord_transport_i i r hir w xW D hD h1 hD1 β hβp] at e1
      rw [← hab] at e2
      exact_mod_cast (by linarith : (cycleComponent B.left (i w)).ord ψ D =
        (cycleComponent A.left w).ord (a3z_germZ w θ) xW)
    · rw [Scheme.ord_eq_zero_of_coheight_neq_one h1,
        Scheme.ord_eq_zero_of_coheight_neq_one (fun h => h1 (hcoh.1 h))]
  · rw [a3y_principalCycle_apply_of_not_mem A.left w (a3z_germZ w θ) x (fun ⟨xW, hxW⟩ =>
      hwx (hxW ▸ a3z_specializes_pt w xW))]
    rw [a3y_principalCycle_apply_of_not_mem B.left (i w) ψ (i x)
      (fun ⟨D, hD⟩ => hwx (by
        have := (a3z_specializes_pt _ D).map r.continuous
        rwa [hD, a3k_ri i r hir, a3k_ri i r hir] at this))]

end push

end HodgeLean.Adapters
