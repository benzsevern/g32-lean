import HodgeLean.Foundations.Program.SchoenTowerL1bFiniteInvariantChart
import HodgeLean.Foundations.Program.SchoenTowerL1bBranchPolynomial
import HodgeLean.Foundations.Program.SchoenTowerL1aParameterMorphism
import HodgeLean.Foundations.Program.SchoenTowerL1aCoefficientHelpers
import HodgeLean.Foundations.Program.SchoenTowerL1aSymmetricCoefficientNeighborhood
import HodgeLean.Foundations.Program.SchoenTowerL1aTuplePointStabilizers
import HodgeLean.Foundations.Program.SchoenTowerL1aPointAction

/-! # Polynomial equations for finitely many actual branch ideals on one retained chart

All ideal equations descend through the same actual quotient section map.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
open scoped Pointwise
namespace HodgeLean.Foundations.Program
attribute [local instance] overSpecAlgebra

/-- One retained chart has every specified branch equation and a principal etale neighborhood of its symmetric coefficients. -/
theorem s2v_l1b_common_finite_branch_etale_coefficients
    (Z B : Over (Spec ↧ℂ))
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (hdim : TopologicalSpace.dim Z.left = 1) (h : ℕ)
    (γ : g3_power Z (h + 1) ⟶ B) [IsFinite γ.left]
    (hγinv : ∀ τ, s2_permute Z (h + 1) τ ≫ γ = γ)
    (hγ : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Z (h + 1) ⟶ T),
      (∀ τ, s2_permute Z (h + 1) τ ≫ f = f) → ∃! u : B ⟶ T, γ ≫ u = f)
    (m : ℕ) (b : Fin m → ComplexPoint Z) (hb : Function.Injective b)
    (x : ComplexPoint (g3_power Z (h + 1))) :
    ∃ O : B.left.affineOpens, x.underlying ∈ γ.left ⁻¹ᵁ O.1 ∧
      let U := ComplexPoint.openScheme B O.1
      let V := ComplexPoint.openScheme (g3_power Z (h + 1)) (γ.left ⁻¹ᵁ O.1)
      ∃ (P : Polynomial Γ(U.left, ⊤)) (a : Fin m → ℂ)
        (z : Fin (h + 1) → Γ(V.left, ⊤)),
        Function.Injective a ∧
        P.map (γ.left ∣_ O.1).appTop.hom = ∏ i, (Polynomial.C (z i) - Polynomial.X) ∧
        (∀ k, ((s2c_branchIdeal Z B h γ (b k)).comap O.1.ι).ideal
          ⟨⊤, @isAffineOpen_top _ O.2⟩ =
          Ideal.span {P.eval (algebraMap ℂ Γ(U.left, ⊤) (a k))}) ∧
        ∀ hx : x.underlying ∈ γ.left ⁻¹ᵁ O.1,
        ∃ (c : Fin (h + 1) → Γ(U.left, ⊤)) (d : Γ(U.left, ⊤)),
          (∀ j, (γ.left ∣_ O.1).appTop.hom (c j) = MvPolynomial.aeval (R := ℂ) z
            (MvPolynomial.esymm (Fin (h + 1)) ℂ (j.val + 1))) ∧
          Point.evaluate ⊤ ((γ.left ∣_ O.1).appTop.hom d)
            (ComplexPoint.asOpenPoint (g3_power Z (h + 1)) (γ.left ⁻¹ᵁ O.1) x hx) ≠ 0 ∧
          ((algebraMap Γ(U.left, ⊤) (Localization.Away d)).comp
            (MvPolynomial.aeval (R := ℂ) c).toRingHom).Etale := by
  obtain ⟨O, hx, z, c, hc, hEt, ρ, hρv, hqinj, hqimage, hcov, hbranch, hsep⟩ :=
    s2v_l1b_common_finite_branch_invariant_chart Z B hdim h γ hγinv hγ m b hb x
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
  refine ⟨O, hx, P, (fun k => e (c k)), z, ?_, hP, ?_, ?_⟩
  · intro i j H
    exact hc (e.injective H)
  · intro k
    rw [hbranch]
    have H := hPI (e (c k)) 0
    have hcoeff : V.hom.appTop.hom (c k) = algebraMap ℂ Γ(V.left, ⊤) (e (c k)) := by
      rw [s2v_l1a_structure_section_coefficients]
      rfl
    rw [hcoeff]
    exact H

  · intro hx'
    let pt := ComplexPoint.asOpenPoint (g3_power Z (h + 1)) (γ.left ⁻¹ᵁ O.1) x hx'
    have hp : Point.map v pt = x := by
      apply Over.OverMorphism.ext
      exact ComplexPoint.liftToOpen_fac (g3_power Z (h + 1)) (γ.left ⁻¹ᵁ O.1) x hx'
    letI : LocallyOfFiniteType V.hom := by
      rw [← Over.w v]
      infer_instance
    letI : Algebra.FiniteType ℂ Γ(V.left, ⊤) := s2t_globalSections_finiteType V
    have hR (g : Equiv.Perm (Fin (h + 1))) :
        (MulSemiringAction.toRingHom (Equiv.Perm (Fin (h + 1))) Γ(V.left, ⊤) g).comp
          (algebraMap ℂ Γ(V.left, ⊤)) = algebraMap ℂ Γ(V.left, ⊤) := by
      ext t
      exact (MulSemiringAction.toAlgHom ℂ Γ(V.left, ⊤) g).commutes t
    obtain ⟨cv, hcv, _⟩ := s2v_l1a_symmetric_coefficient_descent
      (algebraMap ℂ Γ(V.left, ⊤)) q.left.appTop.hom hqinj h z
      (MulSemiringAction.toRingHom (Equiv.Perm (Fin (h + 1))) Γ(V.left, ⊤)) hR hz himage
    let φ := s2t_affinePointAlgHom V pt
    have hsep' : ∀ i j, Point.map (v ≫ g3_proj Z (h + 1) i) pt ≠
        Point.map (v ≫ g3_proj Z (h + 1) j) pt →
        Point.evaluate ⊤ (z i) pt ≠ Point.evaluate ⊤ (z j) pt := by
      intro i j hij
      apply hsep hx' i j
      change pt ≫ (v ≫ g3_proj Z (h + 1) i) ≠ pt ≫ (v ≫ g3_proj Z (h + 1) j) at hij
      rw [← Category.assoc, ← Category.assoc, show pt ≫ v = x from hp] at hij
      exact hij
    have hreflect (g : Equiv.Perm (Fin (h + 1)))
        (H : ∀ i, φ (z (g⁻¹ i)) = φ (z i)) :
        φ.comp (MulSemiringAction.toAlgHom ℂ Γ(V.left, ⊤) g⁻¹) = φ := by
      have hval (i : Fin (h + 1)) : Point.evaluate ⊤ (z (g⁻¹ i)) pt =
          Point.evaluate ⊤ (z i) pt := by
        rw [← s2t_affinePointAlgHom_apply, ← s2t_affinePointAlgHom_apply]
        exact H i
      have hpfix := s2v_l1a_tuple_point_stabilizer V Z (h + 1) v ρ hρv pt z hsep' g hval
      have hk : g • RingHom.ker φ.toRingHom = RingHom.ker φ.toRingHom :=
        (s2v_l1a_affine_point_kernel_stabilizer V (Equiv.Perm (Fin (h + 1))) act pt g).mpr hpfix
      exact (s2v_l1a_rational_kernel_stabilizer φ g).mp hk
    obtain ⟨d, hd, hSym⟩ := s2v_l1a_symmetric_coefficient_neighborhood (h + 1) z hz hEtC
      (s2t_overSectionsAlgHom q) hqinj himage cv hcv φ hreflect
    refine ⟨cv, d, hcv, ?_, hSym⟩
    rw [← s2t_affinePointAlgHom_apply]
    exact hd

end HodgeLean.Foundations.Program
