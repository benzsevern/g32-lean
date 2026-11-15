import HodgeLean.Foundations.Program.SchoenTowerL1aRetainedOrderedParameters

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The actual permutation action and invariant sections restrict to every retained
 affine quotient open.
Source: Schoen (1988), Lemma 2.2, printed p. 13. -/
theorem s2v_i2a_ordered_invariant_chart
    (Z B : Over (Spec ↧ℂ))
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (h : ℕ) (γ : g3_power Z (h + 1) ⟶ B) [IsFinite γ.left]
    (hγinv : ∀ τ, s2_permute Z (h + 1) τ ≫ γ = γ)
    (hγ : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Z (h + 1) ⟶ T),
      (∀ τ, s2_permute Z (h + 1) τ ≫ f = f) → ∃! u : B ⟶ T, γ ≫ u = f)
    (O : B.left.affineOpens) :
    let U := ComplexPoint.openScheme B O.1
    let V := ComplexPoint.openScheme (g3_power Z (h + 1)) (γ.left ⁻¹ᵁ O.1)
    ∃ (q : V ⟶ U) (ρ : Equiv.Perm (Fin (h + 1)) → (V ⟶ V)),
      IsFinite q.left ∧
      ComplexPoint.openInclusion _ (γ.left ⁻¹ᵁ O.1) ≫ γ =
        q ≫ ComplexPoint.openInclusion B O.1 ∧
      (∀ τ, ρ τ ≫ ComplexPoint.openInclusion _ (γ.left ⁻¹ᵁ O.1) =
        ComplexPoint.openInclusion _ (γ.left ⁻¹ᵁ O.1) ≫ s2_permute Z (h + 1) τ) ∧
      (∀ τ, ρ τ ≫ q = q) ∧ Function.Injective q.left.appTop.hom ∧
      (∀ s : Γ(V.left, ⊤), s ∈ Set.range q.left.appTop.hom ↔
        ∀ τ, (ρ τ).left.appTop.hom s = s) := by
  let X := g3_power Z (h + 1)
  let V₀ := γ.left ⁻¹ᵁ O.1
  let U := ComplexPoint.openScheme B O.1
  let V := ComplexPoint.openScheme X V₀
  let u : U ⟶ B := ComplexPoint.openInclusion B O.1
  let v : V ⟶ X := ComplexPoint.openInclusion X V₀
  let q : V ⟶ U := Over.homMk (γ.left ∣_ O.1) (by
    change (γ.left ∣_ O.1) ≫ (O.1.ι ≫ B.hom) = V₀.ι ≫ X.hom
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, Over.w γ])
  have hsquare : v ≫ γ = q ≫ u := by
    apply Over.OverMorphism.ext
    exact (morphismRestrict_ι γ.left O.1).symm
  have hpre (τ : Equiv.Perm (Fin (h + 1))) :
      V₀ ≤ (s2_permute Z (h + 1) τ).left ⁻¹ᵁ V₀ := by
    change γ.left ⁻¹ᵁ O.1 ≤ (s2_permute Z (h + 1) τ).left ⁻¹ᵁ (γ.left ⁻¹ᵁ O.1)
    rw [← Scheme.Hom.comp_preimage]
    rw [show (s2_permute Z (h + 1) τ).left ≫ γ.left = γ.left from
      congrArg (fun f : X ⟶ B => f.left) (hγinv τ)]
  let r (τ : Equiv.Perm (Fin (h + 1))) :=
    (s2_permute Z (h + 1) τ).left.resLE V₀ V₀ (hpre τ)
  have hr (τ : Equiv.Perm (Fin (h + 1))) :
      r τ ≫ V₀.ι = V₀.ι ≫ (s2_permute Z (h + 1) τ).left :=
    Scheme.Hom.resLE_comp_ι _ _
  let ρ (τ : Equiv.Perm (Fin (h + 1))) : V ⟶ V := Over.homMk (r τ) (by
    change r τ ≫ (V₀.ι ≫ X.hom) = V₀.ι ≫ X.hom
    rw [← Category.assoc, hr, Category.assoc, Over.w])
  have hρv (τ : Equiv.Perm (Fin (h + 1))) :
      ρ τ ≫ v = v ≫ s2_permute Z (h + 1) τ := by
    apply Over.OverMorphism.ext
    exact hr τ
  have hρq (τ : Equiv.Perm (Fin (h + 1))) : ρ τ ≫ q = q := by
    apply Over.OverMorphism.ext
    apply (cancel_mono O.1.ι).mp
    change (r τ ≫ (γ.left ∣_ O.1)) ≫ O.1.ι = (γ.left ∣_ O.1) ≫ O.1.ι
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hr, Category.assoc]
    rw [show (s2_permute Z (h + 1) τ).left ≫ γ.left = γ.left from
      congrArg (fun f : X ⟶ B => f.left) (hγinv τ)]
  obtain ⟨hinj, himage⟩ := s2v_l1a_retained_affine_invariants Z B h γ hγinv hγ O
  have Hinv := s2v_l1a_restricted_lift_invariant_image γ.left
    (fun τ => (s2_permute Z (h + 1) τ).left)
    (fun τ => congrArg (fun f : X ⟶ B => f.left) (hγinv τ)) O.1 hinj himage r hr
  exact ⟨q, ρ, inferInstanceAs (IsFinite (γ.left ∣_ O.1)), hsquare,
    hρv, hρq, Hinv.1, Hinv.2⟩

end HodgeLean.Foundations.Program
