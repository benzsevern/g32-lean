import HodgeLean.Foundations.Program.SchoenTowerI2aActualBranchParameters

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
open scoped BigOperators
namespace HodgeLean.Foundations.Program
attribute [local instance] overSpecAlgebra

/-- Every specified branch product descends through the actual quotient and
generates the contraction of its actual shifted coordinate equation.
Source: Schoen (1988), Lemma 2.2, printed p. 13. -/
theorem s2v_i2a_actual_branch_product_sections
    (U V Z : Over (Spec ↧ℂ))
    (h : ℕ) (v : V ⟶ g3_power Z (h + 1)) [Mono v] (q : V ⟶ U)
    (ρ : Equiv.Perm (Fin (h + 1)) → (V ⟶ V))
    (hρv : ∀ τ, ρ τ ≫ v = v ≫ s2_permute Z (h + 1) τ)
    (z : Fin (h + 1) → Γ(V.left, ⊤))
    (hcov : ∀ τ i, (ρ τ).left.appTop.hom (z i) = z (τ⁻¹ i))
    (hqinj : Function.Injective q.left.appTop.hom)
    (hqimage : ∀ s : Γ(V.left, ⊤), s ∈ Set.range q.left.appTop.hom ↔
      ∀ τ, (ρ τ).left.appTop.hom s = s)
    (hzEt : (MvPolynomial.aeval (R := ℂ) z).toRingHom.Etale)
    {T : Type*} (b : T → ℂ) :
    ∃ f : T → Γ(U.left, ⊤),
      (∀ t, q.left.appTop.hom (f t) = ∏ i, (algebraMap ℂ Γ(V.left, ⊤) (b t) - z i)) ∧
      (∀ t, (Ideal.span {z 0 - algebraMap ℂ Γ(V.left, ⊤) (b t)}).comap
        q.left.appTop.hom = Ideal.span {f t}) := by
  let act := s2v_l1a_liftedAction (s2_symmetricPowerAction Z (h + 1)) v ρ hρv
  let act' := ((Over.forget (Spec ↧ℂ)).mapAut V).comp act
  letI := s2_schemeSectionAction V.left (Equiv.Perm (Fin (h + 1))) act'
  letI := s2t_overSectionAction_smulCommClass V (Equiv.Perm (Fin (h + 1))) act
  have hz (g : Equiv.Perm (Fin (h + 1))) (i : Fin (h + 1)) : g • z i = z (g i) := by
    change (ρ g⁻¹).left.appTop.hom (z i) = z (g i)
    simpa only [inv_inv] using hcov g⁻¹ i
  have himage (s : Γ(V.left, ⊤)) : s ∈ Set.range q.left.appTop.hom ↔
      ∀ g : Equiv.Perm (Fin (h + 1)), g • s = s := by
    constructor
    · intro hs g
      exact (hqimage s).mp hs g⁻¹
    · intro hs
      apply (hqimage s).mpr
      intro g
      have H := hs g⁻¹
      change (ρ ((g⁻¹)⁻¹)).left.appTop.hom s = s at H
      simpa only [inv_inv] using H
  have hex (t : T) : ∃ f : Γ(U.left, ⊤),
      q.left.appTop.hom f = ∏ i, (algebraMap ℂ Γ(V.left, ⊤) (b t) - z i) := by
    apply (himage _).mpr
    intro g
    have hs : g • algebraMap ℂ Γ(V.left, ⊤) (b t) =
        algebraMap ℂ Γ(V.left, ⊤) (b t) :=
      (MulSemiringAction.toAlgHom ℂ Γ(V.left, ⊤) g).commutes (b t)
    simp only [Finset.smul_prod', smul_sub, hs, hz]
    exact Equiv.prod_comp g (fun i => algebraMap ℂ Γ(V.left, ⊤) (b t) - z i)
  choose f hf using hex
  refine ⟨f, hf, ?_⟩
  intro t
  exact s2v_i2a_branch_product_ideal_contraction (h + 1) z hz hzEt
    q.left.appTop.hom hqinj himage (b t) (f t) (hf t) 0

/-- The actual branch ideal has the specified equation on a retained affine
quotient chart whenever its actual coordinate contraction has that equation.
Source: Schoen (1988), Lemma 2.2; Hartshorne, Algebraic Geometry, II.5. -/
theorem s2v_i2a_actual_branch_ideal_from_contraction
    (Z B : Over (Spec ↧ℂ)) [IsSeparated Z.hom] (h : ℕ)
    (γ : g3_power Z (h + 1) ⟶ B) [IsFinite γ.left] (O : B.left.affineOpens)
    (q : ComplexPoint.openScheme (g3_power Z (h + 1)) (γ.left ⁻¹ᵁ O.1) ⟶
      ComplexPoint.openScheme B O.1)
    (hq : ComplexPoint.openInclusion _ (γ.left ⁻¹ᵁ O.1) ≫ γ =
      q ≫ ComplexPoint.openInclusion B O.1)
    (b : ComplexPoint Z) (z : Γ((γ.left ⁻¹ᵁ O.1).toScheme, ⊤))
    (f : Γ(O.1.toScheme, ⊤))
    (hcoord : (b.left.ker.comap ((γ.left ⁻¹ᵁ O.1).ι ≫ (g3_proj Z (h + 1) 0).left)).ideal
      ⟨⊤, @isAffineOpen_top _ (O.2.preimage γ.left)⟩ = Ideal.span {z})
    (hcontract : (Ideal.span {z}).comap q.left.appTop.hom = Ideal.span {f}) :
    ((s2c_branchIdeal Z B h γ b).comap O.1.ι).ideal
      ⟨⊤, @isAffineOpen_top _ O.2⟩ = Ideal.span {f} := by
  have hqleft : q.left = γ.left ∣_ O.1 := by
    apply (cancel_mono O.1.ι).mp
    have H := congrArg (fun f => f.left) hq
    change (γ.left ⁻¹ᵁ O.1).ι ≫ γ.left = q.left ≫ O.1.ι at H
    exact H.symm.trans (morphismRestrict_ι γ.left O.1).symm
  have H := s2v_l1a_branchIdeal_affine_contraction Z B h γ b O
  dsimp only at H
  rw [← Scheme.IdealSheafData.comap_comp, hcoord, ← hqleft] at H
  exact H.trans hcontract

end HodgeLean.Foundations.Program
