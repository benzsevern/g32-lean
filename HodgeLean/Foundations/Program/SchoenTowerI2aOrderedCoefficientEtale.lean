import HodgeLean.Foundations.Program.SchoenTowerL1aPreProofs

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

/-- The actual descended elementary coefficients are etale on a principal
neighborhood retaining the specified separated ordered point.
Source: Schoen (1988), Lemma 2.2, printed p. 13; EGA IV, 17.1.1. -/
theorem s2v_i2a_ordered_coefficient_etale_neighborhood
    (U V Z : Over (Spec ↧ℂ)) [IsAffine V.left] [LocallyOfFiniteType V.hom]
    (h : ℕ) (v : V ⟶ g3_power Z (h + 1)) [Mono v] (q : V ⟶ U)
    (ρ : Equiv.Perm (Fin (h + 1)) → (V ⟶ V))
    (hρv : ∀ τ, ρ τ ≫ v = v ≫ s2_permute Z (h + 1) τ)
    (z : Fin (h + 1) → Γ(V.left, ⊤))
    (hcov : ∀ τ i, (ρ τ).left.appTop.hom (z i) = z (τ⁻¹ i))
    (hqinj : Function.Injective q.left.appTop.hom)
    (hqimage : ∀ s : Γ(V.left, ⊤), s ∈ Set.range q.left.appTop.hom ↔
      ∀ τ, (ρ τ).left.appTop.hom s = s)
    (c : Fin (h + 1) → Γ(U.left, ⊤))
    (hc : ∀ j, q.left.appTop.hom (c j) = MvPolynomial.aeval (R := ℂ) z
      (MvPolynomial.esymm (Fin (h + 1)) ℂ (j.val + 1)))
    (hEtC : (MvPolynomial.aeval (R := ℂ) z).toRingHom.Etale)
    (p : ComplexPoint V)
    (hsep : ∀ i j, Point.map (v ≫ g3_proj Z (h + 1) i) p ≠
      Point.map (v ≫ g3_proj Z (h + 1) j) p →
      Point.evaluate ⊤ (z i) p ≠ Point.evaluate ⊤ (z j) p) :
    ∃ d : Γ(U.left, ⊤), Point.evaluate ⊤ d (Point.map q p) ≠ 0 ∧
      ((algebraMap Γ(U.left, ⊤) (Localization.Away d)).comp
        (MvPolynomial.aeval (R := ℂ) c).toRingHom).Etale := by
  let act := s2v_l1a_liftedAction (s2_symmetricPowerAction Z (h + 1)) v ρ hρv
  let act' := ((Over.forget (Spec ↧ℂ)).mapAut V).comp act
  letI := s2_schemeSectionAction V.left (Equiv.Perm (Fin (h + 1))) act'
  letI := s2t_overSectionAction_smulCommClass V (Equiv.Perm (Fin (h + 1))) act
  letI : Algebra.FiniteType ℂ Γ(V.left, ⊤) := s2t_globalSections_finiteType V
  have hcov' (g : Equiv.Perm (Fin (h + 1))) (i : Fin (h + 1)) : g • z i = z (g i) := by
    have H := hcov g⁻¹ i
    change (ρ g⁻¹).left.appTop.hom (z i) = z (g i)
    simpa only [inv_inv] using H
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
  let φ := s2t_affinePointAlgHom V p
  have hreflect (g : Equiv.Perm (Fin (h + 1)))
      (H : ∀ i, φ (z (g⁻¹ i)) = φ (z i)) :
      φ.comp (MulSemiringAction.toAlgHom ℂ Γ(V.left, ⊤) g⁻¹) = φ := by
    have hval (i : Fin (h + 1)) : Point.evaluate ⊤ (z (g⁻¹ i)) p =
        Point.evaluate ⊤ (z i) p := by
      rw [← s2t_affinePointAlgHom_apply, ← s2t_affinePointAlgHom_apply]
      exact H i
    have hpfix := s2v_l1a_tuple_point_stabilizer V Z (h + 1) v ρ hρv p z hsep g hval
    have hk : g • RingHom.ker φ.toRingHom = RingHom.ker φ.toRingHom :=
      (s2v_l1a_affine_point_kernel_stabilizer V (Equiv.Perm (Fin (h + 1))) act p g).mpr hpfix
    exact (s2v_l1a_rational_kernel_stabilizer φ g).mp hk
  obtain ⟨d, hd, hSym⟩ := s2v_l1a_symmetric_coefficient_neighborhood (h + 1) z hcov' hEtC
    (s2t_overSectionsAlgHom q) hqinj himage c hc φ hreflect
  refine ⟨d, ?_, hSym⟩
  rw [← s2t_affinePointAlgHom_apply, s2v_l1a_affine_point_evaluation_map]
  exact hd

end HodgeLean.Foundations.Program
