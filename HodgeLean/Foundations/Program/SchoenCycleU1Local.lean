import HodgeLean.Foundations.Program.SchoenCycleStep1

/-! # Affine invariant charts for the retained symmetric quotient -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The ring of permutation-invariant regular functions on an inverse-image chart.
Source: Mumford--Fogarty--Kirwan, Geometric Invariant Theory, third edition, I.1. -/
def s2e_u1_invariantChartRing (Z B : Over (Spec ↧ℂ)) (N : ℕ)
    (γ : g3_power Z N ⟶ B) (hγ : ∀ σ, s2_permute Z N σ ≫ γ = γ)
    (U : B.left.Opens) : Subring Γ((g3_power Z N).left, γ.left ⁻¹ᵁ U) where
  carrier := {b | ∀ σ, ((s2_permute Z N σ).left.appLE _ _
    (s2e_step1_action_preimage _ _ γ _ (hγ σ) U)).hom b = b}
  zero_mem' := fun σ => map_zero _
  one_mem' := fun σ => map_one _
  add_mem' := by
    intro a b ha hb σ
    rw [map_add, ha σ, hb σ]
  mul_mem' := by
    intro a b ha hb σ
    rw [map_mul, ha σ, hb σ]
  neg_mem' := by
    intro a ha σ
    rw [map_neg, ha σ]

/-- Every affine target chart is the spectrum of the actual invariant ring.
No distinctness restriction is imposed on the points of a divisor.
Source: Mumford--Fogarty--Kirwan, Geometric Invariant Theory, third edition, I.1,
finite-group affine quotients. -/
theorem s2e_u1_retained_quotient_invariant_chart
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [IsProjective Z.hom] [IsIntegral B.left] [Smooth B.hom]
    (N : ℕ) (γ : g3_power Z N ⟶ B) [IsFinite γ.left]
    (hsurj : Function.Surjective (Point.map γ))
    (hγ : ∀ σ, s2_permute Z N σ ≫ γ = γ)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z N ⟶ T),
      (∀ σ, s2_permute Z N σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v)
    (U : B.left.Opens) (hU : IsAffineOpen U) :
    ∃ e : Γ(B.left, U) ≃+* s2e_u1_invariantChartRing Z B N γ hγ U,
      (∀ c, (e c).val = (γ.left.app U).hom c) ∧
      Nonempty (U.toScheme ≅ Spec (.of (s2e_u1_invariantChartRing Z B N γ hγ U))) := by
  letI : Surjective γ.left :=
    s2e_step1_surjective_of_complexPoint_surjective _ B γ hsurj
  let f : Γ(B.left, U) →+* s2e_u1_invariantChartRing Z B N γ hγ U :=
    (γ.left.app U).hom.codRestrict _ (by
      intro c σ
      have he := Scheme.Hom.appLE_comp_appLE (s2_permute Z N σ).left γ.left
        U (γ.left ⁻¹ᵁ U) (γ.left ⁻¹ᵁ U) le_rfl
        (s2e_step1_action_preimage _ _ γ _ (hγ σ) U)
      have heγ : (s2_permute Z N σ).left ≫ γ.left = γ.left :=
        congrArg Over.Hom.left (hγ σ)
      simpa only [heγ, Scheme.Hom.app_eq_appLE, CommRingCat.comp_apply] using congrArg
        (fun t => (t : Γ(B.left, U) ⟶ Γ((g3_power Z N).left, γ.left ⁻¹ᵁ U)).hom c) he)
  have hf : Function.Bijective f := by
    constructor
    · intro c d h
      have hc := s2e_step1_invariant_affine_descent (g3_power Z N) B
        (Equiv.Perm (Fin N)) (s2_permute Z N) (s2e_step1_permute_one Z N)
        (s2e_step1_permute_mul Z N) γ hγ hquot U hU (f c).val (f c).property
      exact (hc.unique rfl (congrArg Subtype.val h).symm)
    · intro b
      obtain ⟨c, hc, _⟩ := s2e_step1_invariant_affine_descent (g3_power Z N) B
        (Equiv.Perm (Fin N)) (s2_permute Z N) (s2e_step1_permute_one Z N)
        (s2e_step1_permute_mul Z N) γ hγ hquot U hU b.val b.property
      exact ⟨c, Subtype.ext hc⟩
  let e := RingEquiv.ofBijective f hf
  refine ⟨e, (fun _ => rfl), ⟨hU.isoSpec ≪≫ ?_⟩⟩
  exact Scheme.Spec.mapIso e.toCommRingCatIso.symm.op

end HodgeLean.Foundations.Program
