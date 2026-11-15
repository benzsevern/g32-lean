import HodgeLean.Foundations.Program.SchoenTowerGeometryDefs
import HodgeLean.Foundations.Program.SchoenTowerL1bResidualDivisor
import HodgeLean.Foundations.Program.SchoenTowerL1bWeightedProducts

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
/-- The support of an ideal sheaf in its actual affine section coordinates. -/
theorem s2v_l1b_fromSpec_support
    {X : Scheme} (I : X.IdealSheafData) (U : X.affineOpens) :
    U.2.fromSpec ⁻¹' (I.support : Set X) =
      PrimeSpectrum.zeroLocus (I.ideal U : Set Γ(X, U)) := by
  apply U.2.fromSpec.isOpenEmbedding.injective.image_injective
  rw [Set.image_preimage_eq_inter_range, IsAffineOpen.range_fromSpec,
    IsAffineOpen.fromSpec_image_zeroLocus, Scheme.IdealSheafData.coe_support_inter]

set_option backward.isDefEq.respectTransparency false in
/-- A prime residual equation in an affine blowup chart gives the actual reduced strict transform. -/
theorem s2v_l1b_strictTransform_prime_chart
    {X Y : Scheme} (f : X ⟶ Y) (D K : Y.IdealSheafData)
    (U : X.affineOpens) (s e : Γ(X, U))
    [hs : (Ideal.span {s}).IsPrime] (he : e ∉ Ideal.span {s})
    (hD : (D.comap f).ideal U = Ideal.span {s * e})
    (hK : (K.comap f).ideal U = Ideal.span {e}) :
    (s2c_strictTransform f D K).ideal U = Ideal.span {s} := by
  rw [s2c_strictTransform, Scheme.IdealSheafData.vanishingIdeal_ideal]
  change PrimeSpectrum.vanishingIdeal (U.2.fromSpec ⁻¹'
    closure (f ⁻¹' ((D.support : Set Y) \ (K.support : Set Y)))) = _
  rw [U.2.fromSpec.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
    U.2.fromSpec.continuous]
  have hpre (I : Y.IdealSheafData) :
      U.2.fromSpec ⁻¹' (f ⁻¹' (I.support : Set Y)) =
        PrimeSpectrum.zeroLocus ((I.comap f).ideal U : Set Γ(X, U)) := by
    rw [← s2v_l1b_fromSpec_support (I.comap f) U,
      Scheme.IdealSheafData.support_comap]
    rfl
  rw [Set.preimage_diff, Set.preimage_diff, hpre D, hpre K, hD, hK,
    PrimeSpectrum.zeroLocus_span, PrimeSpectrum.zeroLocus_span]
  exact s2v_l1b_residual_prime_equation s e he

set_option backward.isDefEq.respectTransparency false in
/-- A branch whose total equation is the exceptional equation has no residual divisor in this chart. -/
theorem s2v_l1b_strictTransform_exceptional_chart
    {X Y : Scheme} (f : X ⟶ Y) (D K : Y.IdealSheafData)
    (U : X.affineOpens)
    (hDK : (D.comap f).ideal U = (K.comap f).ideal U) :
    (s2c_strictTransform f D K).ideal U = ⊤ := by
  rw [s2c_strictTransform, Scheme.IdealSheafData.vanishingIdeal_ideal]
  change PrimeSpectrum.vanishingIdeal (U.2.fromSpec ⁻¹'
    closure (f ⁻¹' ((D.support : Set Y) \ (K.support : Set Y)))) = _
  rw [U.2.fromSpec.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
    U.2.fromSpec.continuous]
  have hpre (I : Y.IdealSheafData) :
      U.2.fromSpec ⁻¹' (f ⁻¹' (I.support : Set Y)) =
        PrimeSpectrum.zeroLocus ((I.comap f).ideal U : Set Γ(X, U)) := by
    rw [← s2v_l1b_fromSpec_support (I.comap f) U,
      Scheme.IdealSheafData.support_comap]
    rfl
  rw [Set.preimage_sdiff, Set.preimage_sdiff, hpre D, hpre K, hDK,
    Set.sdiff_self, closure_empty, PrimeSpectrum.vanishingIdeal_empty]

/-- The two selected branches contribute the entire covering degree on a prime residual chart. -/
theorem s2v_l1b_weighted_strictTransform_chart
    {X Y : Scheme} (f : X ⟶ Y) (D₁ D₂ K : Y.IdealSheafData)
    (U : X.affineOpens) (s e : Γ(X, U))
    [(Ideal.span {s}).IsPrime] (he : e ∉ Ideal.span {s})
    (hD₁ : (D₁.comap f).ideal U = Ideal.span {s * e})
    (hD₂ : (D₂.comap f).ideal U = Ideal.span {e})
    (hK : (K.comap f).ideal U = Ideal.span {e})
    (a b m : ℕ) (hab : a + b = m) :
    ((D₁.comap f).ideal U) ^ a * ((D₂.comap f).ideal U) ^ b =
      ((s2c_strictTransform f D₁ K).ideal U) ^ a *
        ((s2c_strictTransform f D₂ K).ideal U) ^ b *
          ((K.comap f).ideal U) ^ m := by
  rw [s2v_l1b_strictTransform_prime_chart f D₁ K U s e he hD₁ hK,
    s2v_l1b_strictTransform_exceptional_chart f D₂ K U (hD₂.trans hK.symm),
    hD₁, hD₂, hK, ← Ideal.span_singleton_mul_span_singleton, mul_pow,
    ← Ideal.one_eq_top, one_pow, mul_one, mul_assoc, ← pow_add, hab]

set_option backward.isDefEq.respectTransparency false in
/-- A prime total pullback is unchanged by the reduced strict transform if the centre misses its generic point. -/
theorem s2v_l1b_strictTransform_prime_unchanged
    {X Y : Scheme} (f : X ⟶ Y) (D K : Y.IdealSheafData)
    (U : X.affineOpens) [hD : ((D.comap f).ideal U).IsPrime]
    (hK : ¬ (K.comap f).ideal U ≤ (D.comap f).ideal U) :
    (s2c_strictTransform f D K).ideal U = (D.comap f).ideal U := by
  rw [s2c_strictTransform, Scheme.IdealSheafData.vanishingIdeal_ideal]
  change PrimeSpectrum.vanishingIdeal (U.2.fromSpec ⁻¹'
    closure (f ⁻¹' ((D.support : Set Y) \ (K.support : Set Y)))) = _
  rw [U.2.fromSpec.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
    U.2.fromSpec.continuous]
  have hpre (I : Y.IdealSheafData) :
      U.2.fromSpec ⁻¹' (f ⁻¹' (I.support : Set Y)) =
        PrimeSpectrum.zeroLocus ((I.comap f).ideal U : Set Γ(X, U)) := by
    rw [← s2v_l1b_fromSpec_support (I.comap f) U,
      Scheme.IdealSheafData.support_comap]
    rfl
  rw [Set.preimage_sdiff, Set.preimage_sdiff, hpre D, hpre K,
    s2v_l1b_prime_divisor_dense_off_centre _ _ hK,
    PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical, hD.isRadical.radical]

/-- A chart calculation for the selected pair extends to every branch when the other transforms are unchanged. -/
theorem s2v_l1b_weighted_all_branches_chart
    {X Y : Scheme} (f : X ⟶ Y) {J : Type*} [Fintype J] [DecidableEq J]
    (D : J → Y.IdealSheafData) (K : Y.IdealSheafData)
    (U : X.affineOpens) (s e : Γ(X, U))
    [(Ideal.span {s}).IsPrime] (he : e ∉ Ideal.span {s})
    (p q : J) (hpq : p ≠ q)
    (hDp : ((D p).comap f).ideal U = Ideal.span {s * e})
    (hDq : ((D q).comap f).ideal U = Ideal.span {e})
    (hK : (K.comap f).ideal U = Ideal.span {e})
    (hrest : ∀ j, j ≠ p → j ≠ q →
      (s2c_strictTransform f (D j) K).ideal U = ((D j).comap f).ideal U)
    (n : J → ℕ) (m : ℕ) (hn : n p + n q = m) :
    (∏ j, (((D j).comap f).ideal U) ^ n j) =
      (∏ j, ((s2c_strictTransform f (D j) K).ideal U) ^ n j) *
        ((K.comap f).ideal U) ^ m := by
  let A := fun j => ((D j).comap f).ideal U
  let T := fun j => (s2c_strictTransform f (D j) K).ideal U
  let E := (K.comap f).ideal U
  have hfactor (j : J) : A j = T j * E ^
      (if j = p then 1 else if j = q then 1 else 0) := by
    by_cases hjp : j = p
    · subst j
      dsimp only [A, T, E]
      rw [if_pos rfl, pow_one,
        s2v_l1b_strictTransform_prime_chart f (D p) K U s e he hDp hK,
        hDp, hK, Ideal.span_singleton_mul_span_singleton]
    · by_cases hjq : j = q
      · subst j
        dsimp only [A, T, E]
        rw [if_neg hjp, if_pos rfl, pow_one,
          s2v_l1b_strictTransform_exceptional_chart f (D q) K U (hDq.trans hK.symm),
          ← Ideal.one_eq_top, one_mul, hDq, hK]
      · rw [if_neg hjp, if_neg hjq, pow_zero, mul_one]
        exact (hrest j hjp hjq).symm
  have H := s2v_l1b_paired_product_transport A T (fun _ : Unit => E) n
    (fun _ => p) (fun _ => q) (fun _ => hpq) m (fun _ => hn)
    (fun j => by simpa only [Fintype.prod_unique] using hfactor j)
  simpa only [Fintype.prod_unique] using H

set_option backward.isDefEq.respectTransparency false in
/-- The strict-transform ideal on any affine chart is computed from the two actual total-pullback ideals. -/
theorem s2v_l1b_strictTransform_affine_formula
    {X Y : Scheme} (f : X ⟶ Y) (D K : Y.IdealSheafData)
    (U : X.affineOpens) :
    (s2c_strictTransform f D K).ideal U =
      PrimeSpectrum.vanishingIdeal (closure
        (PrimeSpectrum.zeroLocus ((D.comap f).ideal U : Set Γ(X, U)) \
          PrimeSpectrum.zeroLocus ((K.comap f).ideal U : Set Γ(X, U)))) := by
  rw [s2c_strictTransform, Scheme.IdealSheafData.vanishingIdeal_ideal]
  change PrimeSpectrum.vanishingIdeal (U.2.fromSpec ⁻¹'
    closure (f ⁻¹' ((D.support : Set Y) \ (K.support : Set Y)))) = _
  rw [U.2.fromSpec.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
    U.2.fromSpec.continuous]
  have hpre (I : Y.IdealSheafData) :
      U.2.fromSpec ⁻¹' (f ⁻¹' (I.support : Set Y)) =
        PrimeSpectrum.zeroLocus ((I.comap f).ideal U : Set Γ(X, U)) := by
    rw [← s2v_l1b_fromSpec_support (I.comap f) U,
      Scheme.IdealSheafData.support_comap]
    rfl
  rw [Set.preimage_sdiff, Set.preimage_sdiff, hpre D, hpre K]

/-- An absent total branch remains absent after taking the reduced strict transform. -/
theorem s2v_l1b_strictTransform_unit_chart
    {X Y : Scheme} (f : X ⟶ Y) (D K : Y.IdealSheafData)
    (U : X.affineOpens) (hD : (D.comap f).ideal U = ⊤) :
    (s2c_strictTransform f D K).ideal U = ⊤ := by
  have hzero : PrimeSpectrum.zeroLocus ((⊤ : Ideal Γ(X, U)) : Set Γ(X, U)) = ∅ :=
    PrimeSpectrum.zeroLocus_empty_iff_eq_top.mpr rfl
  rw [s2v_l1b_strictTransform_affine_formula, hD, hzero, Set.empty_sdiff,
    closure_empty, PrimeSpectrum.vanishingIdeal_empty]

/-- Away from the centre, the strict transform is the radical of the actual total branch ideal. -/
theorem s2v_l1b_strictTransform_off_centre_chart
    {X Y : Scheme} (f : X ⟶ Y) (D K : Y.IdealSheafData)
    (U : X.affineOpens) (hK : (K.comap f).ideal U = ⊤) :
    (s2c_strictTransform f D K).ideal U = ((D.comap f).ideal U).radical := by
  have hzero : PrimeSpectrum.zeroLocus ((⊤ : Ideal Γ(X, U)) : Set Γ(X, U)) = ∅ :=
    PrimeSpectrum.zeroLocus_empty_iff_eq_top.mpr rfl
  rw [s2v_l1b_strictTransform_affine_formula, hK, hzero, Set.sdiff_empty,
    (PrimeSpectrum.isClosed_zeroLocus _).closure_eq,
    PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical]

end HodgeLean.Foundations.Program
