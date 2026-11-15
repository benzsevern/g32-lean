import HodgeLean.Foundations.Program.SchoenCycleStep1Descent

/-! # Invariant affine sections of finite categorical quotients -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- The morphisms of a group action are isomorphisms. -/
theorem s2e_step1_action_isIso (X : Over (Spec ↧ℂ))
    (G : Type) [Group G] (a : G → (X ⟶ X))
    (ha1 : a 1 = 𝟙 X) (hamul : ∀ u v, a (u * v) = a v ≫ a u) :
    ∀ u, IsIso (a u) := by
  intro u
  let e : X ≅ X :=
    ⟨a u, a u⁻¹, by rw [← hamul, inv_mul_cancel, ha1],
      by rw [← hamul, mul_inv_cancel, ha1]⟩
  exact e.isIso_hom

/-- Invariant sections descend uniquely along a finite categorical quotient by isomorphisms. -/
theorem s2e_step1_invariant_sections
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left]
    (I : Type) (a : I → (X ⟶ X)) [∀ i, IsIso (a i)]
    (q : X ⟶ Y) [IsFinite q.left] [Surjective q.left]
    (hinv : ∀ i, a i ≫ q = q)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : X ⟶ T),
      (∀ i, a i ≫ v = v) → ∃! w : Y ⟶ T, q ≫ w = v)
    (U : Y.left.Opens) (hU : IsAffineOpen U)
    (b : Γ(X.left, q.left ⁻¹ᵁ U))
    (hb : ∀ i, ((a i).left.appLE (q.left ⁻¹ᵁ U) (q.left ⁻¹ᵁ U)
      (by change q.left ⁻¹ᵁ U ≤ ((a i).left ≫ q.left) ⁻¹ᵁ U
          have hi : (a i).left ≫ q.left = q.left := congrArg Over.Hom.left (hinv i)
          rw [hi])).hom b = b) :
    ∃! c : Γ(Y.left, U), (q.left.app U).hom c = b := by
  classical
  haveI := IsSchemeTheoreticallyDominant.of_isDominant q.left
  suffices ∃ c : Γ(Y.left, U), (q.left.app U).hom c = b by
    obtain ⟨c, hc⟩ := this
    exact ⟨c, hc, fun d hd => q.left.app_injective U (hd.trans hc.symm)⟩
  cases isEmpty_or_nonempty (q.left ⁻¹ᵁ U) with
  | inl he =>
    have hUbot : U = ⊥ := by
      apply le_antisymm _ bot_le
      intro y hy
      obtain ⟨x, hxy⟩ := q.left.surjective y
      exact (he.false ⟨x, by change q.left x ∈ U; simpa [hxy] using hy⟩).elim
    subst U
    haveI : Subsingleton Γ(X.left, q.left ⁻¹ᵁ ⊥) := by
      change Subsingleton Γ(X.left, ⊥)
      infer_instance
    exact ⟨0, Subsingleton.elim _ _⟩
  | inr hn =>
    letI := hn
    let K := s2e_step1_fixedField X.left I (fun i => (a i).left)
    have hbK : X.left.germToFunctionField (q.left ⁻¹ᵁ U) b ∈ K := by
      rw [s2e_step1_mem_fixedField]
      intro i
      have hUV : q.left ⁻¹ᵁ U ≤ (a i).left ⁻¹ᵁ (q.left ⁻¹ᵁ U) := by
        change q.left ⁻¹ᵁ U ≤ ((a i).left ≫ q.left) ⁻¹ᵁ U
        have hi : (a i).left ≫ q.left = q.left := congrArg Over.Hom.left (hinv i)
        rw [hi]
      have he := congrArg (fun t : Γ(X.left, q.left ⁻¹ᵁ U) ⟶ X.left.functionField => t.hom b)
        (s2e_step1_fieldPullback_germ X.left (a i).left _ _ hUV)
      exact he.trans (congrArg (X.left.germToFunctionField (q.left ⁻¹ᵁ U)) (hb i))
    obtain ⟨η, hηaff, hη, hp⟩ :=
      s2e_step1_fixedField_normalization X Y I a q hinv hquot U hU
    letI := hηaff
    letI := hp
    exact s2e_step1_descend_of_mem_subfield X Y q K η hη U hU b hbK

end HodgeLean.Foundations.Program
