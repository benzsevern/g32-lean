import HodgeLean.Adapters.IntersectionProductDefs
import HodgeLean.Adapters.IntersectionProductStalk
import HodgeLean.Adapters.KleimanProduct

/-! # Supported sums for the Serre cycle-class comparison -/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.RealDefs

namespace HodgeLean.Adapters

open Classical in
theorem a3cc_cycleClass_single (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (q : ℕ) (x : X.left) (hx : Order.coheight x = q) (a : ℚ) :
    ccm3_cycleClass X q (Function.locallyFinsuppWithin.single x a) =
      a • cycleComponentSheafClass X x hx := by
  classical
  unfold ccm3_cycleClass
  change (∑ᶠ z : {z : X.left // Order.coheight z = q},
    (Function.locallyFinsuppWithin.single x a : AlgebraicCycle X.left ℚ) z.1 •
      (cycleComponentSheafClass X z.1 z.2 : HQ X (2 * q))) = _
  rw [finsum_eq_single _ ⟨x, hx⟩ (fun z hz => by
    rw [Function.locallyFinsuppWithin.single_apply,
      if_neg (fun h => hz (Subtype.ext h)), zero_smul])]
  rw [Function.locallyFinsuppWithin.single_apply, if_pos rfl]

theorem a3cc_intersection_support_le (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x y : X.left)
    (w : (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme) :
    cycleComponentAnalyticClosedSupport X
        ((ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι w) ≤
      cycleComponentAnalyticClosedSupport X x ⊓ cycleComponentAnalyticClosedSupport X y := by
  obtain ⟨hx, hy⟩ := a3l_specializes_of_subscheme x y w
  intro a ha
  exact ⟨specializes_iff_closure_subset.mp hx ha,
    specializes_iff_closure_subset.mp hy ha⟩

/-- The sum of supported component classes with prescribed rational coefficients.
Source: Fulton, *Intersection Theory*, second edition, §19.1, linear extension of cycle classes. -/
def a3cc_supportedIntersectionSum (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (r : ℕ) (x y : X.left)
    (hcodim : ∀ w : (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme,
      closure ({w} : Set (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme) ∈
        irreducibleComponents (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme →
      Order.coheight ((ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι w) = r)
    (m : (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme → ℚ) :
    H_[cycleComponentAnalyticClosedSupport X x ⊓
      cycleComponentAnalyticClosedSupport X y]^(2 * r)(X; ℚ) := by
  classical
  exact ∑ᶠ w : (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme,
    if hw : closure ({w} : Set (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme) ∈
        irreducibleComponents (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme then
      m w • supportEnlarge X (a3cc_intersection_support_le X x y w) (2 * r)
        (cycleComponentSupportedInjectiveClass X
          ((ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι w) (hcodim w hw))
    else 0

open Classical in
theorem a3cc_forget_supportedIntersectionSum (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (r : ℕ) (x y : X.left)
    (hcodim : ∀ w : (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme,
      closure ({w} : Set (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme) ∈
        irreducibleComponents (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme →
      Order.coheight ((ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι w) = r)
    (m : (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme → ℚ) :
    (HQ.linearEquiv X (2 * r)).symm
      (forgetSupport ℚ X (cycleComponentAnalyticClosedSupport X x ⊓
        cycleComponentAnalyticClosedSupport X y) (2 * r)
        (a3cc_supportedIntersectionSum X r x y hcodim m)) =
      ccm3_cycleClass X r
        (∑ᶠ w : (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme,
          if closure ({w} : Set (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme) ∈
              irreducibleComponents (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme
          then Function.locallyFinsuppWithin.single
            ((ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι w) (m w)
          else 0) := by
  classical
  let L : AlgebraicCycle X.left ℚ →+ HQ X (2 * r) :=
    { toFun := ccm3_cycleClass X r
      map_zero' := by
        unfold ccm3_cycleClass
        apply finsum_eq_zero_of_forall_eq_zero
        intro z
        exact zero_smul ℚ _
      map_add' := fun a b => (ccm6_cycleClass_linear X r 0 a b).1 }
  let := ccm12_isNoetherian X
  have hS := ccm11_intersection_components_finite X.left (ccm3_primeIdeal X.left x)
    (ccm3_primeIdeal X.left y)
  let s := hS.toFinset
  unfold a3cc_supportedIntersectionSum
  rw [finsum_eq_sum_of_support_subset (s := s), finsum_eq_sum_of_support_subset (s := s)]
  · change forgetSupport ℚ X _ _ (∑ w ∈ s, _) = L (∑ w ∈ s, _)
    rw [map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro w _
    by_cases hw : closure ({w} : Set (ccm3_primeIdeal X.left x ⊔
        ccm3_primeIdeal X.left y).subscheme) ∈ irreducibleComponents (ccm3_primeIdeal X.left x ⊔
          ccm3_primeIdeal X.left y).subscheme
    · rw [dif_pos hw, if_pos hw, map_rat_smul, ← forgetSupport_restrict]
      exact (a3cc_cycleClass_single X r _ (hcodim w hw) _).symm
    · simp only [dif_neg hw, if_neg hw, map_zero]
      rfl
  · intro w hw
    by_contra hws
    apply hw
    have hnot : ¬ closure ({w} : Set (ccm3_primeIdeal X.left x ⊔
        ccm3_primeIdeal X.left y).subscheme) ∈ irreducibleComponents (ccm3_primeIdeal X.left x ⊔
          ccm3_primeIdeal X.left y).subscheme :=
      fun h => hws (hS.mem_toFinset.mpr h)
    simp only [if_neg hnot]
  · intro w hw
    by_contra hws
    apply hw
    have hnot : ¬ closure ({w} : Set (ccm3_primeIdeal X.left x ⊔
        ccm3_primeIdeal X.left y).subscheme) ∈ irreducibleComponents (ccm3_primeIdeal X.left x ⊔
          ccm3_primeIdeal X.left y).subscheme :=
      fun h => hws (hS.mem_toFinset.mpr h)
    simp only [dif_neg hnot]

/-- Serre multiplicities weight the supported classes of the intersection components.
Source: Serre, *Algèbre locale, multiplicités*, Chapitre V; Fulton,
*Intersection Theory*, second edition, §19.1 and §20.4. -/
def a3cc_supportedSerreClass (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (p q : ℕ) (x y : X.left) (hx : Order.coheight x = p) (hy : Order.coheight y = q)
    (hxy : a3i_MeetProperly X.left x y) :
    H_[cycleComponentAnalyticClosedSupport X x ⊓
      cycleComponentAnalyticClosedSupport X y]^(2 * (p + q))(X; ℚ) :=
  a3cc_supportedIntersectionSum X (p + q) x y
    (fun w hw => by simpa only [hx, hy, Nat.cast_add] using hxy w hw)
    (fun w => (a3i_serreMult X.left
      ((ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι w) x y : ℚ))

theorem a3cc_forget_supportedSerreClass (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (p q : ℕ) (x y : X.left) (hx : Order.coheight x = p) (hy : Order.coheight y = q)
    (hxy : a3i_MeetProperly X.left x y) :
    (HQ.linearEquiv X (2 * (p + q))).symm
      (forgetSupport ℚ X (cycleComponentAnalyticClosedSupport X x ⊓
        cycleComponentAnalyticClosedSupport X y) (2 * (p + q))
        (a3cc_supportedSerreClass X p q x y hx hy hxy)) =
      ccm3_cycleClass X (p + q) (a3i_intersectPrime X.left x y) := by
  exact a3cc_forget_supportedIntersectionSum X (p + q) x y
    (fun w hw => by simpa only [hx, hy, Nat.cast_add] using hxy w hw)
    (fun w => (a3i_serreMult X.left
      ((ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι w) x y : ℚ))

set_option maxRecDepth 4000 in
set_option backward.isDefEq.respectTransparency false in
theorem a3cc_supportedIntersectionSum_germ (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (r : ℕ) (x y : X.left)
    (hcodim : ∀ w : (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme,
      closure ({w} : Set (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme) ∈
        irreducibleComponents (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme →
      Order.coheight ((ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι w) = r)
    (m : (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme → ℤ)
    (w : (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme)
    (hw : closure ({w} : Set (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme) ∈
      irreducibleComponents (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme)
    (a : ComplexPoint X)
    (hother : ∀ w' : (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme,
      closure ({w'} : Set (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme) ∈
        irreducibleComponents (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme →
      w' ≠ w → a ∉ cycleComponentAnalyticClosedSupport X
        ((ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι w')) :
    ccm5_supportGerm X (cycleComponentAnalyticClosedSupport X x ⊓
        cycleComponentAnalyticClosedSupport X y) (2 * r) a
        (a3cc_supportedIntersectionSum X r x y hcodim (fun w => (m w : ℚ))) =
      m w • ccm5_supportGerm X (cycleComponentAnalyticClosedSupport X x ⊓
        cycleComponentAnalyticClosedSupport X y) (2 * r) a
        (supportEnlarge X (a3cc_intersection_support_le X x y w) (2 * r)
          (cycleComponentSupportedInjectiveClass X
            ((ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι w) (hcodim w hw))) := by
  classical
  have hfin := hc9k_components_finite X x y
  unfold a3cc_supportedIntersectionSum
  rw [map_finsum _ (hfin.subset fun w' hw' => by
    by_contra hn
    exact hw' (dite_eq_right_iff.mpr fun h => absurd h hn))]
  rw [finsum_eq_single _ w (fun w' hne => by
    by_cases hc : closure ({w'} : Set (ccm3_primeIdeal X.left x ⊔
        ccm3_primeIdeal X.left y).subscheme) ∈ irreducibleComponents (ccm3_primeIdeal X.left x ⊔
          ccm3_primeIdeal X.left y).subscheme
    · rw [dif_pos hc, Int.cast_smul_eq_zsmul ℚ, map_zsmul,
        hc9k_supportGerm_enlarge_eq_zero_of_not_mem X _ _ a (hother w' hc hne), zsmul_zero]
    · rw [dif_neg hc, map_zero])]
  rw [dif_pos hw, Int.cast_smul_eq_zsmul ℚ, map_zsmul]

/-- Each intersection component has a smooth complex point away from the other components.
Source: generic smoothness and `hc9k_exists_complexPoint_closure_diff`. -/
theorem a3cc_exists_intersection_component_point
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (x y : X.left)
    (c : {w : (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme //
      closure ({w} : Set (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme) ∈
        irreducibleComponents (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme})
    [Fintype {w : (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme //
      closure ({w} : Set (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme) ∈
        irreducibleComponents (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme}] :
    ∃ a : ComplexPoint X, a ∈ cycleComponentAnalyticClosedSupport X
        ((ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι c.1) ∧
      (∀ c' : {w : (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme //
        closure ({w} : Set (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme) ∈
          irreducibleComponents (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme},
        c' ≠ c → a ∉ cycleComponentAnalyticClosedSupport X
          ((ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι c'.1)) ∧
      a ∉ cycleComponentSingularAnalyticClosedFiltration X
        ((ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι c.1) 0 := by
  classical
  let J := ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y
  let B : Closeds X.left :=
    (⨆ c' : {w : J.subscheme // closure ({w} : Set J.subscheme) ∈
        irreducibleComponents J.subscheme},
      if c' = c then ⊥ else ⟨closure {J.subschemeι c'.1}, isClosed_closure⟩) ⊔
    cycleComponentSingularAmbientClosedFiltration X (J.subschemeι c.1) 0
  have hB : J.subschemeι c.1 ∉ B := by
    intro hm
    simp only [B, ← SetLike.mem_coe, Closeds.coe_sup, Set.mem_union] at hm
    rcases hm with h1 | h2
    · obtain ⟨c', hc'⟩ := (ccm5_mem_finite_iSup _ _).mp h1
      by_cases he : c' = c
      · simp only [he, ↓reduceIte] at hc'
        exact hc'
      · simp only [he, ↓reduceIte] at hc'
        exact he (Subtype.ext (hc9k_component_eq_of_mem_closure X x y c.1 c'.1 c.2 hc')).symm
    · exact ccm5_generic_not_mem_singularBoundary X _ h2
  obtain ⟨a, ha1, ha2⟩ := hc9k_exists_complexPoint_closure_diff X _ B hB
  refine ⟨a, ha1, fun c' hc' hm => ha2 ?_, fun hm => ha2 ?_⟩
  · simp only [B, ← SetLike.mem_coe, Closeds.coe_sup, Set.mem_union]
    refine Or.inl ((ccm5_mem_finite_iSup _ _).mpr ⟨c', ?_⟩)
    simp only [hc', ↓reduceIte]
    exact hm
  · simp only [B, ← SetLike.mem_coe, Closeds.coe_sup, Set.mem_union]
    exact Or.inr hm

end HodgeLean.Adapters
