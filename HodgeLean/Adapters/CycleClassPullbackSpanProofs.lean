import HodgeLean.Adapters.CycleClassFlatComparison
import HodgeLean.Adapters.CycleClassPullback

/-! # From supported prime pullback to the powers span

These statements give the implication from smooth pullback comparison to ordinary
cycle and span compatibility. The endpoint uses the existing abelian power data.
No multiplicativity statement is claimed. HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj
open HodgeLean.RealDefs
namespace HodgeLean.Adapters

/-- Forgetting the weighted supported sum gives the constructed cycle class.
Source: Fulton, Intersection Theory, second edition, §19.1; forgetSupport_restrict. -/
theorem ccm6_forgetSupport_sum_aux {X Z : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (f : X ⟶ Z) [Flat f.left] (q : ℕ) (x : Z.left)
    (hx : Order.coheight x = q) :
    ComplexPoint.forgetSupport ℚ X
      (ccm4_inverseAnalyticSupport f (cycleComponentAnalyticClosedSupport Z x)) (2 * q)
      (∑ᶠ z : {z : X.left // ccm3_flatPullbackPrime f.left x z ≠ 0},
        ccm3_flatPullbackPrime f.left x z.1 •
          supportEnlarge X (ccm4_flatPullbackPrime_support_le f x z.1 z.2) (2 * q)
            (cycleComponentSupportedInjectiveClass X z.1
              (ccm3_flatPullbackPrime_codimension f q x hx z.1 z.2))) =
      ccm3_cycleClass X q (ccm3_flatPullbackPrime f.left x) :=
  by
    calc
      _ = (∑ᶠ z : {z : X.left // ccm3_flatPullbackPrime f.left x z ≠ 0},
          ccm3_flatPullbackPrime f.left x z.1 • cycleComponentSheafClass X z.1
            (ccm3_flatPullbackPrime_codimension f q x hx z.1 z.2) : H^(2 * q)(X; ℚ)) := by
        rw [map_finsum _ (Set.toFinite _)]
        apply finsum_congr
        intro z
        rw [map_rat_smul, ← forgetSupport_restrict X
          (ccm4_flatPullbackPrime_support_le f x z.1 z.2) (2 * q)]
        rfl
      _ = _ := by
        have hreindex :
            (∑ᶠ z : {z : X.left // ccm3_flatPullbackPrime f.left x z ≠ 0},
              ccm3_flatPullbackPrime f.left x z.1 • cycleComponentSheafClass X z.1
                (ccm3_flatPullbackPrime_codimension f q x hx z.1 z.2) : H^(2 * q)(X; ℚ)) =
            ∑ᶠ z : {z : X.left // Order.coheight z = q},
              ccm3_flatPullbackPrime f.left x z.1 • cycleComponentSheafClass X z.1 z.2 := by
          let e : {z : X.left // ccm3_flatPullbackPrime f.left x z ≠ 0} ≃
            {z : {z : X.left // Order.coheight z = q} //
              ccm3_flatPullbackPrime f.left x z.1 ≠ 0} := {
            toFun z := ⟨⟨z.1, ccm3_flatPullbackPrime_codimension f q x hx z.1 z.2⟩, z.2⟩
            invFun z := ⟨z.1.1, z.2⟩
            left_inv z := rfl
            right_inv z := by ext; rfl }
          calc
            _ = ∑ᶠ z : {z : {z : X.left // Order.coheight z = q} //
                  ccm3_flatPullbackPrime f.left x z.1 ≠ 0},
                ccm3_flatPullbackPrime f.left x z.1.1 •
                  cycleComponentSheafClass X z.1.1 z.1.2 := by
                convert (finsum_comp_equiv e (f := fun z =>
                    ccm3_flatPullbackPrime f.left x z.1.1 •
                      cycleComponentSheafClass X z.1.1 z.1.2)) using 1
            _ = ∑ᶠ z : {z : X.left // Order.coheight z = q},
                  ∑ᶠ _ : ccm3_flatPullbackPrime f.left x z.1 ≠ 0,
                    ccm3_flatPullbackPrime f.left x z.1 •
                      cycleComponentSheafClass X z.1 z.2 := by
              exact finsum_subtype_eq_finsum_cond
                (M := H^(2 * q)(X; ℚ))
                (f := fun z : {z : X.left // Order.coheight z = q} =>
                  ccm3_flatPullbackPrime f.left x z.1 • cycleComponentSheafClass X z.1 z.2)
                (fun z => ccm3_flatPullbackPrime f.left x z.1 ≠ 0)
            _ = _ := by
              apply finsum_congr
              intro z
              by_cases hz : ccm3_flatPullbackPrime f.left x z.1 ≠ 0
              · simp [hz]
              · have hz0 : ccm3_flatPullbackPrime f.left x z.1 = 0 := not_ne_iff.mp hz
                rw [hz0, zero_smul]
                simp
        unfold ccm3_cycleClass
        exact hreindex

/-- Ordinary smooth pullback agrees with the inverse-image prime cycle class.
Source: Voisin, Hodge Theory and Complex Algebraic Geometry I, §11; ccm4_supportedPullback_prime. -/
theorem ccm6_homPullback_prime_aux {X Z : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (f : X ⟶ Z) [Smooth f.left] (q : ℕ) (x : Z.left)
    (hx : Order.coheight x = q) :
    homPullback f (2 * q) (cycleComponentSheafClass Z x hx) =
      ccm3_cycleClass X q (ccm3_flatPullbackPrime f.left x) :=
  by
    change homPullback f (2 * q)
      (ComplexPoint.forgetSupport ℚ Z (cycleComponentAnalyticClosedSupport Z x) (2 * q)
        (cycleComponentSupportedInjectiveClass Z x hx)) = _
    rw [← ccm4_forgetSupport_supportedPullback f
      (cycleComponentAnalyticClosedSupport Z x) (2 * q)
      (cycleComponentSupportedInjectiveClass Z x hx)]
    rw [ccm4_supportedPullback_prime f q x hx]
    exact ccm6_forgetSupport_sum_aux f q x hx

/-- Constructed cycle pullback respects rational scaling.
Source: Fulton, Intersection Theory, second edition, §1.7, linear extension. -/
theorem ccm6_flatPullback_smul_aux {X Z : Over (Spec ↧ℂ)}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (f : X ⟶ Z) (a : ℚ) (c : AlgebraicCycle Z.left ℚ) :
    ccm3_flatPullback f.left (c.mapRange (a * ·) (mul_zero a)) =
      (ccm3_flatPullback f.left c).mapRange (a * ·) (mul_zero a) :=
  by
    letI : CompactSpace Z.left := QuasiCompact.compactSpace_of_compactSpace Z.hom
    unfold ccm3_flatPullback
    have hfin : Function.HasFiniteSupport (fun x : Z.left ↦
        (ccm3_flatPullbackPrime f.left x).mapRange (c x * ·) (mul_zero _)) :=
      c.finite_support.subset fun x hx h ↦ hx (by
        apply Function.locallyFinsuppWithin.ext
        intro z
        simp only [Function.locallyFinsuppWithin.mapRange_apply, h, zero_mul]
        rfl)
    have hfina : Function.HasFiniteSupport (fun x : Z.left ↦
        (ccm3_flatPullbackPrime f.left x).mapRange
          ((c.mapRange (a * ·) (mul_zero a)) x * ·) (mul_zero _)) :=
      c.finite_support.subset fun x hx h ↦ hx (by
        apply Function.locallyFinsuppWithin.ext
        intro z
        simp only [Function.locallyFinsuppWithin.mapRange_apply, h, zero_mul, mul_zero]
        rfl)
    apply Function.locallyFinsuppWithin.ext
    intro z
    let ev : AlgebraicCycle X.left ℚ →+ ℚ :=
      { toFun := fun e ↦ e z
        map_zero' := rfl
        map_add' := fun _ _ ↦ rfl }
    change ev (∑ᶠ x : Z.left, _) = ev
      (Function.locallyFinsuppWithin.mapRange (a * ·) (mul_zero a) (∑ᶠ x : Z.left, _))
    rw [ev.map_finsum hfina]
    simp only [Function.locallyFinsuppWithin.mapRange_apply]
    change _ = a * ev (∑ᶠ x : Z.left, _)
    rw [ev.map_finsum hfin]
    change (∑ᶠ x : Z.left, a * c x * ccm3_flatPullbackPrime f.left x z) =
      a * ∑ᶠ x : Z.left, c x * ccm3_flatPullbackPrime f.left x z
    have hcoeff : Function.HasFiniteSupport (fun x : Z.left ↦
        c x * ccm3_flatPullbackPrime f.left x z) :=
      c.finite_support.subset fun x hx h ↦ hx (by simp only [h, zero_mul])
    rw [mul_comm a, finsum_mul' (fun x : Z.left ↦
      c x * ccm3_flatPullbackPrime f.left x z) a hcoeff]
    apply finsum_congr
    intro x
    ring

private theorem ccm6_cycleClass_summand_finite (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (q : ℕ) (e : AlgebraicCycle X.left ℚ) :
    Function.HasFiniteSupport (fun z : {z : X.left // Order.coheight z = q} ↦
      e z.1 • cycleComponentSheafClass X z.1 z.2) := by
  letI : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  exact (e.finite_support.preimage
    (Set.injOn_of_injective Subtype.val_injective)).subset
      (fun z hz h ↦ hz (by simp only [h, zero_smul]))

/-- The codimension part of the cycle-class realization is rational linear.
Source: Fulton, Intersection Theory, second edition, §19.1, linear extension. -/
theorem ccm6_cycleClass_linear_aux (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (q : ℕ) (a : ℚ) (c d : AlgebraicCycle X.left ℚ) :
    ccm3_cycleClass X q (c + d) = ccm3_cycleClass X q c + ccm3_cycleClass X q d ∧
      ccm3_cycleClass X q (c.mapRange (a * ·) (mul_zero a)) = a • ccm3_cycleClass X q c :=
  by
    letI : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
    constructor
    · unfold ccm3_cycleClass
      rw [show (fun z : {z : X.left // Order.coheight z = q} ↦
          (c + d) z.1 • cycleComponentSheafClass X z.1 z.2) =
          fun z ↦ c z.1 • cycleComponentSheafClass X z.1 z.2 +
            d z.1 • cycleComponentSheafClass X z.1 z.2 by
        funext z
        simp only [Function.locallyFinsuppWithin.coe_add, Pi.add_apply, add_smul]]
      exact finsum_add_distrib (ccm6_cycleClass_summand_finite X q c)
        (ccm6_cycleClass_summand_finite X q d)
    · unfold ccm3_cycleClass
      have hs : a • (∑ᶠ z : {z : X.left // Order.coheight z = q},
          c z.1 • cycleComponentSheafClass X z.1 z.2) =
          ∑ᶠ z : {z : X.left // Order.coheight z = q},
            a • (c z.1 • cycleComponentSheafClass X z.1 z.2) :=
        smul_finsum' a (ccm6_cycleClass_summand_finite X q c)
      calc
        _ = ∑ᶠ z : {z : X.left // Order.coheight z = q},
            a • (c z.1 • cycleComponentSheafClass X z.1 z.2) := by
          apply finsum_congr
          intro z
          simp only [Function.locallyFinsuppWithin.mapRange_apply, smul_smul]
        _ = _ := hs.symm

private theorem ccm6_cycle_single_eq {X : Over (Spec ↧ℂ)}
    [DecidableEq X.left]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (q : ℕ) (x : X.left) (hx : Order.coheight x = q) (a : ℚ) :
    ccm3_cycleClass X q
        ((Function.locallyFinsuppWithin.single x a).restrict (Set.subset_univ _)) =
      a • cycleComponentSheafClass X x hx := by
  classical
  unfold ccm3_cycleClass
  change (∑ᶠ z : {z : X.left // Order.coheight z = q},
    ((Function.locallyFinsuppWithin.single x a).restrict (Set.subset_univ _)) z.1 •
      (cycleComponentSheafClass X z.1 z.2 : HQ X (2 * q))) = _
  rw [finsum_eq_single _ ⟨x, hx⟩ (fun z hz ↦ by
    simp only [Function.locallyFinsuppWithin.restrict_apply,
      Set.mem_univ, ↓reduceIte, Function.locallyFinsuppWithin.single_apply]
    rw [if_neg]
    · exact zero_smul _ _
    · intro hzx
      exact hz (Subtype.ext hzx))]
  simp only [Function.locallyFinsuppWithin.restrict_apply,
    Set.mem_univ, Function.locallyFinsuppWithin.single_apply, ↓reduceIte]

private theorem ccm6_flatPullback_single_eq {X Z : Over (Spec ↧ℂ)}
    [DecidableEq Z.left]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (f : X ⟶ Z) (x : Z.left) (a : ℚ) :
    ccm3_flatPullback f.left
        ((Function.locallyFinsuppWithin.single x a).restrict (Set.subset_univ _)) =
      (ccm3_flatPullbackPrime f.left x).mapRange (a * ·) (mul_zero a) := by
  classical
  unfold ccm3_flatPullback
  rw [finsum_eq_single _ x (fun y hy ↦ by
    apply Function.locallyFinsuppWithin.ext
    intro z
    simp only [Function.locallyFinsuppWithin.mapRange_apply,
      Function.locallyFinsuppWithin.restrict_apply,
      Function.locallyFinsuppWithin.single_apply]
    simp only [hy, ↓reduceIte, Set.mem_univ, zero_mul]
    rfl)]
  apply Function.locallyFinsuppWithin.ext
  intro z
  simp only [Function.locallyFinsuppWithin.mapRange_apply,
    Function.locallyFinsuppWithin.restrict_apply,
    Function.locallyFinsuppWithin.single_apply, Set.mem_univ, ↓reduceIte]

private theorem ccm6_mapRange_zero {X : Scheme} (c : AlgebraicCycle X ℚ) :
    c.mapRange ((0 : ℚ) * ·) (mul_zero 0) = 0 := by
  apply Function.locallyFinsuppWithin.ext
  intro x
  simp only [Function.locallyFinsuppWithin.mapRange_apply, zero_mul, Pi.zero_apply]
  rfl

private theorem ccm6_cycleClass_zero (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (q : ℕ) :
    ccm3_cycleClass X q 0 = 0 := by
  have h := (ccm6_cycleClass_linear_aux X q 0 0 0).2
  rw [ccm6_mapRange_zero, zero_smul] at h
  exact h

private theorem ccm6_flatPullback_zero {X Z : Over (Spec ↧ℂ)}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] (f : X ⟶ Z) :
    ccm3_flatPullback f.left 0 = 0 := by
  have h := ccm6_flatPullback_smul_aux f 0 0
  rw [ccm6_mapRange_zero, ccm6_mapRange_zero] at h
  exact h

/-- Smooth pullback comparison for a cycle pure of the specified codimension.
Source: Fulton, Intersection Theory, second edition, §1.7 and §19.1; Voisin, §11. -/
theorem ccm6_homPullback_cycleClass_aux {X Z : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (f : X ⟶ Z) [Smooth f.left] (q : ℕ)
    (c : AlgebraicCycle Z.left ℚ)
    (hc : ∀ x : Z.left, c x ≠ 0 → Order.coheight x = q) :
    homPullback f (2 * q) (ccm3_cycleClass Z q c) =
      ccm3_cycleClass X q (ccm3_flatPullback f.left c) :=
  by
    classical
    letI : CompactSpace Z.left := QuasiCompact.compactSpace_of_compactSpace Z.hom
    let g : Z.left → AlgebraicCycle Z.left ℚ := fun x ↦
      (Function.locallyFinsuppWithin.single x (c x)).restrict (Set.subset_univ _)
    have hsum : ∑ᶠ x, g x = c :=
      Function.locallyFinsuppWithin.sum_apply_smul_single_eq_self c.finite_support
    rw [← hsum]
    apply finsum_induction (p := fun d : AlgebraicCycle Z.left ℚ ↦
      homPullback f (2 * q) (ccm3_cycleClass Z q d) =
        ccm3_cycleClass X q (ccm3_flatPullback f.left d))
    · rw [ccm6_cycleClass_zero Z q, map_zero, ccm6_flatPullback_zero f,
        ccm6_cycleClass_zero X q]
    · intro d e hd he
      rw [(ccm6_cycleClass_linear_aux Z q 0 d e).1, map_add, hd, he,
        ccm3_flatPullback_add, (ccm6_cycleClass_linear_aux X q 0
          (ccm3_flatPullback f.left d) (ccm3_flatPullback f.left e)).1]
    · intro x
      by_cases hcx : c x = 0
      · have hgx : g x = 0 := by
          apply Function.locallyFinsuppWithin.ext
          intro y
          simp only [g, Function.locallyFinsuppWithin.restrict_apply,
            Function.locallyFinsuppWithin.single_apply, hcx, Pi.zero_apply]
          change (if y = x then (0 : ℚ) else 0) = 0
          split <;> rfl
        rw [hgx]
        rw [ccm6_cycleClass_zero Z q, map_zero, ccm6_flatPullback_zero f,
          ccm6_cycleClass_zero X q]
      · have hx : Order.coheight x = q := hc x hcx
        rw [show g x =
            (Function.locallyFinsuppWithin.single x (c x)).restrict
              (Set.subset_univ _) from rfl,
          ccm6_cycle_single_eq (X := Z) q x hx (c x)]
        change homPullback f (2 * q)
            ((c x) • (cycleComponentSheafClass Z x hx : HQ Z (2 * q))) = _
        rw [show homPullback f (2 * q)
              ((c x) • (cycleComponentSheafClass Z x hx : HQ Z (2 * q))) =
            (c x) • homPullback f (2 * q)
              (cycleComponentSheafClass Z x hx : HQ Z (2 * q)) from
              (homPullback f (2 * q)).map_smul (c x)
                (cycleComponentSheafClass Z x hx : HQ Z (2 * q)),
          ccm6_homPullback_prime_aux f q x hx,
          ccm6_flatPullback_single_eq f x (c x)]
        exact (ccm6_cycleClass_linear_aux X q (c x)
          (ccm3_flatPullbackPrime f.left x) 0).2.symm

private theorem ccm6_cycleClass_mem_algebraicCycleClassSpan (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (q : ℕ) (c : AlgebraicCycle X.left ℚ) :
    ccm3_cycleClass X q c ∈ algebraicCycleClassSpan X q := by
  letI : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let g : {z : X.left // Order.coheight z = q} → HQ X (2 * q) :=
    fun z ↦ c z.1 • cycleComponentSheafClass X z.1 z.2
  have hfin : (Function.support g).Finite := by
    apply (c.finite_support.preimage (Set.injOn_of_injective Subtype.val_injective)).subset
    intro z hz
    intro hcz
    apply hz
    simp only [g, hcz, zero_smul]
    rfl
  unfold ccm3_cycleClass
  rw [finsum_eq_sum_of_support_subset g (s := hfin.toFinset) (by
    intro z hz
    exact hfin.mem_toFinset.mpr hz)]
  apply Submodule.sum_mem
  intro z hz
  apply Submodule.smul_mem
  unfold algebraicCycleClassSpan
  apply le_sSup (s := {Submodule.span ℚ {cycleComponentSheafClass X y hy} |
    (y : X.left) (hy : Order.coheight y = q)})
  exact ⟨z.1, z.2, rfl⟩
  exact Submodule.subset_span (Set.mem_singleton _)

/-- Nonzero powers sum maps preserve the algebraic cycle-class span.
Source: ccm3_pwSumMap_smooth_of_ne_zero; Fulton, Intersection Theory, second edition, §19.1. -/
theorem ccm6_pwSumMap_span_of_ne_zero_aux {A Y : Over (Spec ↧ℂ)} [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    {L : Type*} [Field L] [Algebra ℚ L] {r : ℕ}
    (P : AbelianPowerData A Y r) (θ : L →ₐ[ℚ] AbelianEnd0 A) (a : Fin r → pwOrder A θ)
    (ha : a ≠ 0) (q : ℕ) :
    (algebraicCycleClassSpan A q).map (homPullback (P.pwSumMap θ a) (2 * q)) ≤
      algebraicCycleClassSpan Y q :=
  by
    letI : Smooth (P.pwSumMap θ a).left := ccm3_pwSumMap_smooth_of_ne_zero P θ a ha
    apply Submodule.map_le_iff_le_comap.mpr
    rw [algebraicCycleClassSpan]
    refine sSup_le ?_
    rintro _ ⟨x, hx, rfl⟩
    apply (Submodule.span_singleton_le_iff_mem _ _).mpr
    change homPullback (P.pwSumMap θ a) (2 * q) (cycleComponentSheafClass A x hx) ∈
      algebraicCycleClassSpan Y q
    rw [ccm6_homPullback_prime_aux (P.pwSumMap θ a) q x hx]
    exact ccm6_cycleClass_mem_algebraicCycleClassSpan Y q _

/-- The exact powers pullback premise, including the zero tuple.
Source: ccm2_hPull_of_zero_or_nonzero; PW v0.3, proof of Theorem 4.2. -/
theorem ccm6_hPull_aux {A Y : Over (Spec ↧ℂ)} [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    {L : Type*} [Field L] [Algebra ℚ L] {r : ℕ}
    (P : AbelianPowerData A Y r) (θ : L →ₐ[ℚ] AbelianEnd0 A) :
    ∀ (a : Fin r → pwOrder A θ) (q : ℕ),
      (algebraicCycleClassSpan A q).map (homPullback (P.pwSumMap θ a) (2 * q)) ≤
      algebraicCycleClassSpan Y q :=
  ccm2_hPull_of_zero_or_nonzero P θ fun a ha q ↦
    ccm6_pwSumMap_span_of_ne_zero_aux P θ a ha q

end HodgeLean.Adapters
