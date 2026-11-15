import HodgeLean.Foundations.Program.SchoenTowerI2aBranchIdealParameters
import HodgeLean.Foundations.Program.SchoenTowerI2aOrderedCoefficientEtale

/-! # Simultaneous branch products on the actual ordered quotient chart
HC no distance; AV milestone no distance.
-/
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

/-- Present branch values give simultaneous etale coordinates on the actual
quotient, retaining their product equations and principal contraction ideals.
Source: Schoen (1988), Lemma 2.2, printed p. 13. -/
theorem s2v_i2a_actual_present_branch_parameters
    (U V Z : Over (Spec ↧ℂ)) [IsAffine V.left]
    (h : ℕ) (v : V ⟶ g3_power Z (h + 1)) [Mono v] (q : V ⟶ U)
    (ρ : Equiv.Perm (Fin (h + 1)) → (V ⟶ V))
    (hρv : ∀ τ, ρ τ ≫ v = v ≫ s2_permute Z (h + 1) τ)
    (z : Fin (h + 1) → Γ(V.left, ⊤))
    (hcov : ∀ τ i, (ρ τ).left.appTop.hom (z i) = z (τ⁻¹ i))
    (hqinj : Function.Injective q.left.appTop.hom)
    (hqimage : ∀ s : Γ(V.left, ⊤), s ∈ Set.range q.left.appTop.hom ↔
      ∀ τ, (ρ τ).left.appTop.hom s = s)
    (c : MvPolynomial (Fin (h + 1)) ℂ →ₐ[ℂ] Γ(U.left, ⊤))
    (hcEt : c.toRingHom.Etale)
    (hc : ∀ j, q.left.appTop.hom (c (MvPolynomial.X j)) = MvPolynomial.aeval (R := ℂ) z
      (MvPolynomial.esymm (Fin (h + 1)) ℂ (j.val + 1)))
    (hzEt : (MvPolynomial.aeval (R := ℂ) z).toRingHom.Etale)
    (p : ComplexPoint V) {J : Type} [Finite J] (b : J → ℂ)
    (hb : Function.Injective b) (hpresent : ∀ j, ∃ i, Point.evaluate ⊤ (z i) p = b j) :
    ∃ (κ : J ↪ Fin (h + 1))
      (cBranch : MvPolynomial (Fin (h + 1)) ℂ →ₐ[ℂ] Γ(U.left, ⊤)),
      cBranch.toRingHom.Etale ∧
      (∀ j, Point.evaluate ⊤ (z (κ j)) p = b j) ∧
      (∀ j, q.left.appTop.hom (cBranch (MvPolynomial.X (κ j))) =
        ∏ i, (algebraMap ℂ Γ(V.left, ⊤) (b j) - z i)) ∧
      (∀ j, (Ideal.span {z 0 - algebraMap ℂ Γ(V.left, ⊤) (b j)}).comap
        q.left.appTop.hom = Ideal.span {cBranch (MvPolynomial.X (κ j))}) ∧
      (∀ j, Point.evaluate ⊤ (cBranch (MvPolynomial.X (κ j))) (Point.map q p) = 0) := by
  let act := s2v_l1a_liftedAction (s2_symmetricPowerAction Z (h + 1)) v ρ hρv
  let act' := ((Over.forget (Spec ↧ℂ)).mapAut V).comp act
  letI := s2_schemeSectionAction V.left (Equiv.Perm (Fin (h + 1))) act'
  letI := s2t_overSectionAction_smulCommClass V (Equiv.Perm (Fin (h + 1))) act
  let φ := s2t_affinePointAlgHom V p
  letI : Nontrivial Γ(V.left, ⊤) := φ.toRingHom.domain_nontrivial
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
  obtain ⟨κ, hκ⟩ := s2v_i2a_present_branch_slots (h + 1)
    (fun i => Point.evaluate ⊤ (z i) p) b hb hpresent
  obtain ⟨cBranch, hEt, hprod⟩ := s2v_i2a_etale_symmetric_branch_products ℂ
    Γ(V.left, ⊤) Γ(U.left, ⊤) (h + 1) c hcEt (s2t_overSectionsAlgHom q) z hc κ b hb
  refine ⟨κ, cBranch, hEt, hκ, hprod, ?_, ?_⟩
  · intro j
    exact s2v_i2a_branch_product_ideal_contraction (h + 1) z hz hzEt
      q.left.appTop.hom hqinj himage (b j) (cBranch (MvPolynomial.X (κ j))) (hprod j) 0
  · intro j
    rw [← s2t_affinePointAlgHom_apply, s2v_l1a_affine_point_evaluation_map]
    change φ ((s2t_overSectionsAlgHom q) (cBranch (MvPolynomial.X (κ j)))) = 0
    rw [hprod, map_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ (κ j))
    rw [map_sub, φ.commutes]
    have H : φ (z (κ j)) = b j := by
      rw [s2t_affinePointAlgHom_apply]
      exact hκ j
    rw [H]
    simp

end HodgeLean.Foundations.Program
