import HodgeLean.Adapters.CupLeftTransportDefs

/-! # Proof obligations for `CupLeftTransport`

One `_aux` per statement of `HodgeLean.Adapters.CupLeftTransport`, all open.
HC no distance; AV milestone no distance.
-/

noncomputable section

-- Boundary conversions between HQ and upstream sheaf cohomology have deep instance terms.
set_option maxRecDepth 4000

open CategoryTheory AlgebraicGeometry ComplexPoint
open HodgeLean.RealDefs HodgeLean.Foundations
open scoped TensorProduct

namespace HodgeLean.Adapters

theorem spec_cohomologyBaseChange_cup_left_aux (Y : TopCat.{0})
    (ψ : AlgebraicTopology.Simplicial.Cocycle ℚ (TopCat.toSSet.obj Y) 1)
    (Ψ : AlgebraicTopology.Simplicial.Cocycle ℂ (TopCat.toSSet.obj Y) 1)
    (h : Ψ.1 = cochainBaseChange _ 1 ψ.1) (k : ℕ)
    (v : AlgebraicTopology.Singular.Cohomology ℚ Y k) :
    cohomologyBaseChange Y (1 + k)
        (1 ⊗ₜ Singular.cup Y rfl (Singular.cohomologyClass Y 1 ψ) v) =
      Singular.cup Y rfl (Singular.cohomologyClass Y 1 Ψ) (cohomologyBaseChange Y k (1 ⊗ₜ v)) := by
  obtain ⟨φ, rfl⟩ := Singular.cohomologyClass_surjective Y k v
  rw [cup_cohomologyClass_cupLeftCocycle,
    spec_cohomologyBaseChange_tmul_cohomologyClass Y k φ (cocycleBaseChange _ k φ) rfl,
    cup_cohomologyClass_cupLeftCocycle]
  refine spec_cohomologyBaseChange_tmul_cohomologyClass Y (1 + k) _ _ ?_
  refine cupLeft_cochain_ext _ _ fun σ => ?_
  change Singular.cupCochain Y 1 k Ψ.1 (cochainBaseChange _ k φ.1) _ =
    cochainBaseChange _ (1 + k) (Singular.cupCochain Y 1 k ψ.1 φ.1) _
  simp only [Singular.cupCochain_apply_simplex, cochainBaseChange_chainOfSimplex, h,
    Rat.cast_mul]

theorem spec_complexSingularClass_cupC_aux (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (k : ℕ)
    (x : ℂ ⊗[ℚ] HQ X 1) (y : ℂ ⊗[ℚ] HQ X k) :
    complexSingularClass X (1 + k) ((cupProductOf X).cupC rfl x y) =
      Singular.cup (TopCat.of (ComplexPoint X)) rfl (complexSingularClass X 1 x)
        (complexSingularClass X k y) := by
  have key : ∀ (z w : ℂ) (u : HQ X 1) (v : HQ X k),
      complexSingularClass X (1 + k) ((cupProductOf X).cupC rfl (z ⊗ₜ u) (w ⊗ₜ v)) =
        Singular.cup (TopCat.of (ComplexPoint X)) rfl (complexSingularClass X 1 (z ⊗ₜ u))
          (complexSingularClass X k (w ⊗ₜ v)) := by
    intro z w u v
    obtain ⟨ψ, hψ⟩ := Singular.cohomologyClass_surjective _ 1 (cupComparison X 1 u)
    have hs : ∀ (n : ℕ) (c : ℂ)
        (b : AlgebraicTopology.Singular.Cohomology ℚ (TopCat.of (ComplexPoint X)) n),
        cohomologyBaseChange (TopCat.of (ComplexPoint X)) n (c ⊗ₜ b) =
          c • cohomologyBaseChange (TopCat.of (ComplexPoint X)) n (1 ⊗ₜ b) := by
      intro n c b
      rw [← LinearMap.map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [CupProduct.cupC_tmul]
    change cohomologyBaseChange _ (1 + k) ((z * w) ⊗ₜ cupComparison X (1 + k) _) =
      Singular.cup _ rfl (cohomologyBaseChange _ 1 (z ⊗ₜ cupComparison X 1 u))
        (cohomologyBaseChange _ k (w ⊗ₜ cupComparison X k v))
    rw [cupComparison_cup, hs, hs 1, hs k, LinearMap.map_smul₂, LinearMap.map_smul, smul_smul,
      ← hψ,
      spec_cohomologyBaseChange_cup_left_aux _ ψ (cocycleBaseChange _ 1 ψ) rfl,
      spec_cohomologyBaseChange_tmul_cohomologyClass _ 1 ψ (cocycleBaseChange _ 1 ψ) rfl]
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | add x₁ x₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]
  | tmul z u =>
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add y₁ y₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    | tmul w v => exact key z w u v

set_option maxHeartbeats 400000 in
theorem spec_cupLeftHypercohomology_transport_rat_aux (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : HQ X 1)
    (a : AlgebraicTopology.Simplicial.Cocycle ℚ (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1)
    (ha : Singular.cohomologyClass _ 1 a = cupComparison X 1 x)
    (k : ℕ) (h : 1 + (k : ℤ) = ((1 + k : ℕ) : ℤ)) (v : HQ X k) :
    sheafHypercohomologyFieldEquiv ℚ X (1 + k)
        (cupLeftHypercohomology X a h
          ((sheafHypercohomologyFieldEquiv ℚ X k).symm (HQ.linearEquiv X k v))) =
      HQ.linearEquiv X (1 + k) ((cupProductOf X).cup rfl x v) := by
  obtain ⟨r, hr, hcmp⟩ := exists_cupComparison_eq_smul X
  have hS : ∀ n (u : HQ X n) (s : ℚ), sheafHypercohomologyFieldEquiv ℚ X n
      (singularToSheafHypercohomology X ℚ n (s • cupComparison X n u)) =
      (s * r) • HQ.linearEquiv X n u := by
    intro n u s
    change singularToFieldCohomology ℚ X n _ = _
    rw [hcmp, smul_smul, map_rat_smul,
      singularToFieldCohomology_rationalCohomologyLinearEquivSingular]
  have hw : (sheafHypercohomologyFieldEquiv ℚ X k).symm (HQ.linearEquiv X k v) =
      singularToSheafHypercohomology X ℚ k (r⁻¹ • cupComparison X k v) := by
    rw [AddEquiv.symm_apply_eq, hS, inv_mul_cancel₀ hr, one_smul]
  have e1 := spec_cupLeftHypercohomology_singularToSheafHypercohomology ℚ X a k h
    (r⁻¹ • cupComparison X k v)
  have e2 := cupComparison_cup X (rfl : 1 + k = 1 + k) x v
  rw [ha, LinearMap.map_smul, ← e2] at e1
  rw [hw, e1, hS, inv_mul_cancel₀ hr, one_smul]

theorem spec_cupLeftHypercohomology_transport_complex_aux (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : ℂ ⊗[ℚ] HQ X 1)
    (a : AlgebraicTopology.Simplicial.Cocycle ℂ (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1)
    (ha : Singular.cohomologyClass _ 1 a = complexSingularClass X 1 x)
    (k : ℕ) (h : 1 + (k : ℤ) = ((1 + k : ℕ) : ℤ)) (y : ℂ ⊗[ℚ] HQ X k) :
    cupLeftHypercohomology X a h (singularToSheafHypercohomology X ℂ k (complexSingularClass X k y)) =
      singularToSheafHypercohomology X ℂ (1 + k)
        (complexSingularClass X (1 + k) ((cupProductOf X).cupC rfl x y)) := by
  rw [spec_cupLeftHypercohomology_singularToSheafHypercohomology ℂ X a k h, ha,
    spec_complexSingularClass_cupC_aux X k x y]

/-- If the rational comparison of `U1` is a uniform multiple `r`, so is the comparison of
`cupComparison` in every degree. -/
theorem singularToFieldCohomology_cupComparison_of_smul (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (r : ℚ)
    (hcmp : ∀ (n : ℕ) (v : HQ X n), cupComparison X n v =
      r • Foundations.rationalCohomologyLinearEquivSingular X n (HQ.linearEquiv X n v))
    (n : ℕ) (v : HQ X n) :
    singularToFieldCohomology ℚ X n (cupComparison X n v) = r • HQ.linearEquiv X n v := by
  rw [hcmp, map_rat_smul, singularToFieldCohomology_rationalCohomologyLinearEquivSingular]

/-- The de Rham image of the complex comparison of `complexSingularClass` is `q • bettiDeRhamHQ`,
for any `q` normalizing the rational comparison in that degree. -/
theorem fieldToDeRham_singularToFieldCohomology_complexSingularClass (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (n : ℕ) (q : ℚ)
    (h6 : ∀ v : HQ X n,
      singularToFieldCohomology ℚ X n (cupComparison X n v) = q • HQ.linearEquiv X n v)
    (ω : ℂ ⊗[ℚ] HQ X n) :
    fieldToDeRhamCohomology ℂ X n (singularToFieldCohomology ℂ X n (complexSingularClass X n ω)) =
      (q : ℂ) • bettiDeRhamHQ X n ω := by
  induction ω using TensorProduct.inductionOn with
  | tmul a v =>
    change fieldToDeRhamCohomology ℂ X n (singularToFieldCohomology ℂ X n
      (cohomologyBaseChange (TopCat.of (ComplexPoint X)) n (a ⊗ₜ cupComparison X n v))) = _
    rw [bettiDeRhamHQ_tmul,
      fieldToDeRham_singularToFieldCohomology_cohomologyBaseChange_tmul X n q h6 a v]
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]

theorem spec_bettiDeRhamHQ_cupC_eq_smul_deRham_cupLeft_aux (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ (k : ℕ) (h : 1 + (k : ℤ) = ((1 + k : ℕ) : ℤ)) (x : ℂ ⊗[ℚ] HQ X 1)
      (a : AlgebraicTopology.Simplicial.Cocycle ℂ
        (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1),
      Singular.cohomologyClass _ 1 a = complexSingularClass X 1 x →
      ∀ y : ℂ ⊗[ℚ] HQ X k,
        bettiDeRhamHQ X (1 + k) ((cupProductOf X).cupC rfl x y) =
          c • fieldToDeRhamCohomology ℂ X (1 + k) (sheafHypercohomologyFieldEquiv ℂ X (1 + k)
            (cupLeftHypercohomology X a h
              (singularToSheafHypercohomology X ℂ k (complexSingularClass X k y)))) := by
  obtain ⟨r, hr, hcmp⟩ := exists_cupComparison_eq_smul X
  have hr' : (r : ℂ) ≠ 0 := Rat.cast_ne_zero.mpr hr
  refine ⟨(r : ℂ)⁻¹, inv_ne_zero hr', fun k h x a ha y ↦ ?_⟩
  rw [spec_cupLeftHypercohomology_transport_complex_aux X x a ha k h y]
  change _ = _ • fieldToDeRhamCohomology ℂ X (1 + k) (singularToFieldCohomology ℂ X (1 + k) _)
  rw [fieldToDeRham_singularToFieldCohomology_complexSingularClass X (1 + k) r
    (singularToFieldCohomology_cupComparison_of_smul X r hcmp (1 + k)), smul_smul,
    inv_mul_cancel₀ hr', one_smul]

theorem spec_bettiDeRhamHQ_cupC_eq_inv_smul_deRham_cupLeft_aux (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (k : ℕ) (q : ℚ)
    (hq : ∀ v : HQ X (1 + k),
      singularToFieldCohomology ℚ X (1 + k) (cupComparison X (1 + k) v) =
        q • HQ.linearEquiv X (1 + k) v)
    (h : 1 + (k : ℤ) = ((1 + k : ℕ) : ℤ)) (x : ℂ ⊗[ℚ] HQ X 1)
    (a : AlgebraicTopology.Simplicial.Cocycle ℂ (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1)
    (ha : Singular.cohomologyClass _ 1 a = complexSingularClass X 1 x) (y : ℂ ⊗[ℚ] HQ X k) :
    bettiDeRhamHQ X (1 + k) ((cupProductOf X).cupC rfl x y) =
      (q : ℂ)⁻¹ • fieldToDeRhamCohomology ℂ X (1 + k) (sheafHypercohomologyFieldEquiv ℂ X (1 + k)
        (cupLeftHypercohomology X a h
          (singularToSheafHypercohomology X ℂ k (complexSingularClass X k y)))) := by
  obtain ⟨r, hr, hcmp⟩ := exists_cupComparison_eq_smul X
  rw [spec_cupLeftHypercohomology_transport_complex_aux X x a ha k h y]
  change _ = _ • fieldToDeRhamCohomology ℂ X (1 + k) (singularToFieldCohomology ℂ X (1 + k) _)
  rw [fieldToDeRham_singularToFieldCohomology_complexSingularClass X (1 + k) q hq, smul_smul]
  by_cases hq0 : (q : ℂ) = 0
  · have hrq := (fieldToDeRham_singularToFieldCohomology_complexSingularClass X (1 + k) r
      (singularToFieldCohomology_cupComparison_of_smul X r hcmp (1 + k))
      ((cupProductOf X).cupC rfl x y)).symm.trans
      (fieldToDeRham_singularToFieldCohomology_complexSingularClass X (1 + k) q hq _)
    rw [hq0, zero_smul, smul_eq_zero] at hrq
    rw [hq0, inv_zero, zero_mul, zero_smul,
      hrq.resolve_left (Rat.cast_ne_zero.mpr hr)]
  · rw [inv_mul_cancel₀ hq0, one_smul]

theorem spec_bettiDeRhamHQ_cupC_eq_zero_iff_cupLeft_aux (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (k : ℕ)
    (h : 1 + (k : ℤ) = ((1 + k : ℕ) : ℤ)) (x : ℂ ⊗[ℚ] HQ X 1)
    (a : AlgebraicTopology.Simplicial.Cocycle ℂ (TopCat.toSSet.obj (TopCat.of (ComplexPoint X))) 1)
    (ha : Singular.cohomologyClass _ 1 a = complexSingularClass X 1 x) (y : ℂ ⊗[ℚ] HQ X k) :
    bettiDeRhamHQ X (1 + k) ((cupProductOf X).cupC rfl x y) = 0 ↔
      cupLeftHypercohomology X a h
        (singularToSheafHypercohomology X ℂ k (complexSingularClass X k y)) = 0 := by
  obtain ⟨c, hc, hβ⟩ := spec_bettiDeRhamHQ_cupC_eq_smul_deRham_cupLeft_aux X
  rw [hβ k h x a ha y, smul_eq_zero, or_iff_right hc]
  constructor
  · intro h0
    apply (sheafHypercohomologyFieldEquiv ℂ X (1 + k)).injective
    apply (spec_fieldToDeRhamCohomology_complex_bijective_aux X (1 + k)).injective
    rw [h0, map_zero, map_zero]
  · intro h0
    rw [h0, map_zero, map_zero]

end HodgeLean.Adapters
