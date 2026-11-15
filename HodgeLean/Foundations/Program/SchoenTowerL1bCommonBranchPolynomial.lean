import HodgeLean.Foundations.Program.SchoenTowerL1bCommonInvariantChart
import HodgeLean.Foundations.Program.SchoenTowerL1bBranchPolynomial
import HodgeLean.Foundations.Program.SchoenTowerL1aParameterMorphism

/-! # Polynomial equations for both actual branch ideals on one retained chart

Both ideal equations descend through the same actual quotient section map.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local instance] overSpecAlgebra

/-- Both retained insertion ideals have equations obtained from one descended polynomial. -/
theorem s2v_l1b_common_two_branch_polynomial
    (Z B : Over (Spec ↧ℂ))
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (hdim : TopologicalSpace.dim Z.left = 1) (h : ℕ)
    (γ : g3_power Z (h + 1) ⟶ B) [IsFinite γ.left]
    (hγinv : ∀ τ, s2_permute Z (h + 1) τ ≫ γ = γ)
    (hγ : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Z (h + 1) ⟶ T),
      (∀ τ, s2_permute Z (h + 1) τ ≫ f = f) → ∃! u : B ⟶ T, γ ≫ u = f)
    (b : Fin 2 → ComplexPoint Z) (hb : b 0 ≠ b 1)
    (x : ComplexPoint (g3_power Z (h + 1))) :
    ∃ O : B.left.affineOpens, x.underlying ∈ γ.left ⁻¹ᵁ O.1 ∧
      let U := ComplexPoint.openScheme B O.1
      let V := ComplexPoint.openScheme (g3_power Z (h + 1)) (γ.left ⁻¹ᵁ O.1)
      ∃ (P : Polynomial Γ(U.left, ⊤)) (a : Fin 2 → ℂ)
        (z : Fin (h + 1) → Γ(V.left, ⊤)),
        a 0 ≠ a 1 ∧
        P.map (γ.left ∣_ O.1).appTop.hom = ∏ i, (Polynomial.C (z i) - Polynomial.X) ∧
        ∀ k, ((s2c_branchIdeal Z B h γ (b k)).comap O.1.ι).ideal
          ⟨⊤, @isAffineOpen_top _ O.2⟩ =
          Ideal.span {P.eval (algebraMap ℂ Γ(U.left, ⊤) (a k))} := by
  obtain ⟨O, hx, z, c, hc, hEt, ρ, hρv, hqinj, hqimage, hcov, hbranch, _⟩ :=
    s2v_l1b_common_two_branch_invariant_chart Z B hdim h γ hγinv hγ b hb x
  let U := ComplexPoint.openScheme B O.1
  let V := ComplexPoint.openScheme (g3_power Z (h + 1)) (γ.left ⁻¹ᵁ O.1)
  letI : IsAffine U.left := O.2
  letI : IsAffine V.left := O.2.preimage γ.left
  let v : V ⟶ g3_power Z (h + 1) :=
    ComplexPoint.openInclusion (g3_power Z (h + 1)) (γ.left ⁻¹ᵁ O.1)
  letI : IsOpenImmersion v.left := inferInstanceAs (IsOpenImmersion (γ.left ⁻¹ᵁ O.1).ι)
  letI : Mono v := Over.mono_of_mono_left v
  let q : V ⟶ U := Over.homMk (γ.left ∣_ O.1) (by
    change (γ.left ∣_ O.1) ≫ (O.1.ι ≫ B.hom) = (γ.left ⁻¹ᵁ O.1).ι ≫ (g3_power Z (h + 1)).hom
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, Over.w γ])
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
      exact ((hqimage s).mp hs) g⁻¹
    · intro hs
      apply (hqimage s).mpr
      intro g
      have H := hs g⁻¹
      change (ρ ((g⁻¹)⁻¹)).left.appTop.hom s = s at H
      simpa only [inv_inv] using H
  have hEtC : (MvPolynomial.aeval (R := ℂ) z).toRingHom.Etale := by
    rw [s2v_l1a_structure_section_coefficients] at hEt
    exact (s2v_l1a_etale_eval_change_coefficients_iff _ _ _).mp hEt
  obtain ⟨P, hP, hPI⟩ := s2v_l1b_branch_polynomial_contractions (h + 1) z hz hEtC
    (s2t_overSectionsAlgHom q) hqinj himage
  let e := (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv
  refine ⟨O, hx, P, (fun k => e (c k)), z, ?_, hP, ?_⟩
  · exact fun H => hc (e.injective H)
  · intro k
    rw [hbranch]
    have H := hPI (e (c k)) 0
    have hcoeff : V.hom.appTop.hom (c k) = algebraMap ℂ Γ(V.left, ⊤) (e (c k)) := by
      rw [s2v_l1a_structure_section_coefficients]
      rfl
    rw [hcoeff]
    exact H

end HodgeLean.Foundations.Program
