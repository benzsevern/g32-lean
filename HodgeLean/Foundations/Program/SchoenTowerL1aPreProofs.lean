import HodgeLean.Foundations.Program.SchoenTowerGeometryDefs
import HodgeLean.Foundations.Program.SchoenTowerL1aRetainedAffine
import HodgeLean.Foundations.Program.SchoenTowerL1aRetainedInvariantCharts
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import HodgeLean.Foundations.Program.SchoenTowerL1aCurveParameter
import HodgeLean.Foundations.Program.SchoenTowerL1aOrderedPointIdeals
import HodgeLean.Foundations.Program.SchoenTowerL1aRetainedOrderedParameters
import HodgeLean.Foundations.Program.SchoenTowerL1aFlatInsertion
import HodgeLean.Foundations.Program.SchoenTowerL1aComplexIdealAssembly
import HodgeLean.Foundations.Program.SchoenTowerL1aParameterMorphism
import HodgeLean.Foundations.Program.SchoenTowerL1aSymmetricCoefficientNeighborhood
import HodgeLean.Foundations.Program.SchoenTowerL1aPrincipalQuotientRestriction
import HodgeLean.Foundations.Program.SchoenTowerL1aLocalizedInvariantImage
import HodgeLean.Foundations.Program.SchoenTowerL1aSectionParameterRestriction
import HodgeLean.Foundations.Program.SchoenTowerL1aTuplePointStabilizers
import HodgeLean.Foundations.Program.SchoenTowerL1aPointAction

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Adapters
open scoped BigOperators Pointwise
attribute [local instance] overSpecAlgebra
namespace HodgeLean.Foundations.Program

/-- Comparison with a specified symmetric categorical quotient, retaining its quotient map.
Source: Mac Lane, Categories for the Working Mathematician, III.1, uniqueness of universal objects; Schoen (1988), §2, printed p. 12. -/
theorem s2v_l1a_pre_quotient_iso_aux
    (Z B₀ : Over (Spec ↧ℂ))
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    [IsIntegral B₀.left] [Smooth B₀.hom] [IsProjective B₀.hom]
    (hdimZ : TopologicalSpace.dim Z.left = 1)
    (h : ℕ) (γ : g3_power Z (h + 1) ⟶ B₀) [IsFinite γ.left]
    (hγsurj : Function.Surjective (Point.map γ))
    (hγinv : ∀ τ, s2_permute Z (h + 1) τ ≫ γ = γ)
    (hγ : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Z (h + 1) ⟶ T),
      (∀ τ, s2_permute Z (h + 1) τ ≫ f = f) →
      ∃! u : B₀ ⟶ T, γ ≫ u = f)
    (Q : Over (Spec ↧ℂ)) (q : g3_power Z (h + 1) ⟶ Q)
    (hqinv : ∀ τ, s2_permute Z (h + 1) τ ≫ q = q)
    (hq : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Z (h + 1) ⟶ T),
      (∀ τ, s2_permute Z (h + 1) τ ≫ f = f) →
      ∃! u : Q ⟶ T, q ≫ u = f) :
    ∃ e : B₀ ≅ Q, γ ≫ e.hom = q ∧ q ≫ e.inv = γ := by
  obtain ⟨f, hf, hfu⟩ := hγ Q q hqinv
  obtain ⟨g, hg, hgu⟩ := hq B₀ γ hγinv
  have hfg : f ≫ g = 𝟙 B₀ := by
    apply (hγ B₀ γ hγinv).unique
    · rw [← Category.assoc, hf, hg]
    · exact Category.comp_id γ
  have hgf : g ≫ f = 𝟙 Q := by
    apply (hq Q q hqinv).unique
    · rw [← Category.assoc, hg, hf]
    · exact Category.comp_id q
  exact ⟨⟨f, g, hfg, hgf⟩, hf, hg⟩

/-- Invariant affine neighborhoods with elementary symmetric parameters, including repeated coordinates.
The last coefficient generates the insertion ideal; ordered parameters generate coordinate point ideals.
Source: Schoen (1988), Lemma 2.2 and its proof, printed p. 13; Hartshorne, Algebraic Geometry, II.6; fundamental theorem of symmetric polynomials. -/
theorem s2v_l1a_pre_invariant_charts_aux
    (Z B₀ : Over (Spec ↧ℂ))
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    [IsIntegral B₀.left] [Smooth B₀.hom] [IsProjective B₀.hom]
    (hdimZ : TopologicalSpace.dim Z.left = 1)
    (h : ℕ) (γ : g3_power Z (h + 1) ⟶ B₀) [IsFinite γ.left]
    (hγsurj : Function.Surjective (Point.map γ))
    (hγinv : ∀ τ, s2_permute Z (h + 1) τ ≫ γ = γ)
    (hγ : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Z (h + 1) ⟶ T),
      (∀ τ, s2_permute Z (h + 1) τ ≫ f = f) →
      ∃! u : B₀ ⟶ T, γ ≫ u = f)
    (b : ComplexPoint Z) (x : ComplexPoint (g3_power Z (h + 1))) :
    ∃ (U V : Over (Spec ↧ℂ)) (hU : IsAffine U.left) (hV : IsAffine V.left)
      (u : U ⟶ B₀) (v : V ⟶ g3_power Z (h + 1)) (q : V ⟶ U),
      IsOpenImmersion u.left ∧ IsOpenImmersion v.left ∧ IsFinite q.left ∧
      v ≫ γ = q ≫ u ∧ x ∈ Set.range (Point.map v) ∧
      ∃ (ρ : Equiv.Perm (Fin (h + 1)) → (V ⟶ V))
        (z : Fin (h + 1) → Γ(V.left, ⊤))
        (c : Fin (h + 1) → Γ(U.left, ⊤)),
        (∀ τ, ρ τ ≫ v = v ≫ s2_permute Z (h + 1) τ) ∧
        (∀ τ, ρ τ ≫ q = q) ∧
        Function.Injective q.left.appTop.hom ∧
        (∀ f : Γ(V.left, ⊤),
          f ∈ Set.range q.left.appTop.hom ↔ ∀ τ, (ρ τ).left.appTop.hom f = f) ∧
        (MvPolynomial.eval₂Hom V.hom.appTop.hom z).Etale ∧
        (MvPolynomial.eval₂Hom U.hom.appTop.hom c).Etale ∧
        (∀ j, q.left.appTop.hom (c j) =
          MvPolynomial.eval₂Hom V.hom.appTop.hom z
            (MvPolynomial.esymm (Fin (h + 1)) Γ(Spec ↧ℂ, ⊤) (j.val + 1))) ∧
        q.left.appTop.hom (c (Fin.last h)) = ∏ j, z j ∧
        ((s2c_branchIdeal Z B₀ h γ b).comap u.left).ideal ⟨⊤, @isAffineOpen_top U.left hU⟩ =
          Ideal.span {c (Fin.last h)} ∧
        (∀ j, ((b.left.ker).comap ((v ≫ g3_proj Z (h + 1) j).left)).ideal
          ⟨⊤, @isAffineOpen_top V.left hV⟩ = Ideal.span {z j}) := by
  classical
  obtain ⟨U, V, hU, hV, u, v, q, p, ρ, z, hu, hv, hq, hsquare, hp,
    hρv, hρq, hqinj, hqimage, hEt, hzi, hcov, hbranch, hsep⟩ :=
    s2v_l1a_retained_separated_ordered_parameters Z B₀ hdimZ h γ hγinv hγ b x
  letI : IsAffine U.left := hU
  letI : IsAffine V.left := hV
  letI : IsOpenImmersion u.left := hu
  letI : IsOpenImmersion v.left := hv
  letI : IsFinite q.left := hq
  letI : Mono v := Over.mono_of_mono_left v
  let act := s2v_l1a_liftedAction (s2_symmetricPowerAction Z (h + 1)) v ρ hρv
  let act' := ((Over.forget (Spec ↧ℂ)).mapAut V).comp act
  letI := s2_schemeSectionAction V.left (Equiv.Perm (Fin (h + 1))) act'
  letI := s2t_overSectionAction_smulCommClass V (Equiv.Perm (Fin (h + 1))) act
  letI : LocallyOfFiniteType V.hom := by
    rw [← Over.w v]
    infer_instance
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
  have hR (g : Equiv.Perm (Fin (h + 1))) :
      (MulSemiringAction.toRingHom (Equiv.Perm (Fin (h + 1))) Γ(V.left, ⊤) g).comp
        (algebraMap ℂ Γ(V.left, ⊤)) = algebraMap ℂ Γ(V.left, ⊤) := by
    ext c
    exact (MulSemiringAction.toAlgHom ℂ Γ(V.left, ⊤) g).commutes c
  obtain ⟨c, hc, _⟩ := s2v_l1a_symmetric_coefficient_descent
    (algebraMap ℂ Γ(V.left, ⊤)) q.left.appTop.hom hqinj h z
    (MulSemiringAction.toRingHom (Equiv.Perm (Fin (h + 1))) Γ(V.left, ⊤))
    hR hcov' himage
  have hcoeff (j : Fin (h + 1)) : q.left.appTop.hom (c j) =
      MvPolynomial.eval₂Hom V.hom.appTop.hom z
        (MvPolynomial.esymm (Fin (h + 1)) Γ(Spec ↧ℂ, ⊤) (j.val + 1)) := by
    rw [hc j]
    simp only [MvPolynomial.esymm, map_sum, map_prod, MvPolynomial.eval₂Hom_X']
  have hlast : q.left.appTop.hom (c (Fin.last h)) = ∏ i, z i := by
    rw [hc]
    exact s2v_l1a_eval_last_esymm (algebraMap ℂ Γ(V.left, ⊤)) h z
  have hEtC : (MvPolynomial.aeval (R := ℂ) z).toRingHom.Etale := by
    rw [s2v_l1a_structure_section_coefficients] at hEt
    exact (s2v_l1a_etale_eval_change_coefficients_iff _ _ _).mp hEt
  have hflat : letI := (MvPolynomial.aeval (R := ℂ) z).toRingHom.toAlgebra
      Module.Flat (MvPolynomial (Fin (h + 1)) ℂ) Γ(V.left, ⊤) := by
    letI : Algebra (MvPolynomial (Fin (h + 1)) ℂ) Γ(V.left, ⊤) :=
      (MvPolynomial.aeval (R := ℂ) z).toRingHom.toAlgebra
    letI : Algebra.Etale (MvPolynomial (Fin (h + 1)) ℂ) Γ(V.left, ⊤) := hEtC
    infer_instance
  have hI : ((s2c_branchIdeal Z B₀ h γ b).comap u.left).ideal
      ⟨⊤, isAffineOpen_top U.left⟩ = Ideal.span {c (Fin.last h)} := by
    rw [hbranch]
    exact s2v_l1a_flat_insertion_contraction (K := ℂ) (h + 1) z hcov' hflat
      q.left.appTop.hom hqinj himage (c (Fin.last h)) hlast 0
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
  have hdpoint : Point.evaluate ⊤ d (Point.map q p) ≠ 0 := by
    rw [← s2t_affinePointAlgHom_apply, s2v_l1a_affine_point_evaluation_map]
    exact hd
  obtain ⟨U', V', hU', hV', rU, rV, q', p', σ, hrU, hrV, hq', hsquare', hp', hσv,
    hσq, hlocU, hlocV⟩ :=
    s2v_l1a_principal_quotient_restriction V U q ρ hρq p d hdpoint
  letI : IsAffine U'.left := hU'
  letI : IsAffine V'.left := hV'
  letI : IsOpenImmersion rU.left := hrU
  letI : IsOpenImmersion rV.left := hrV
  letI : Algebra Γ(U.left, ⊤) Γ(U'.left, ⊤) := rU.left.appTop.hom.toAlgebra
  letI : Algebra Γ(V.left, ⊤) Γ(V'.left, ⊤) := rV.left.appTop.hom.toAlgebra
  letI : IsLocalization.Away d Γ(U'.left, ⊤) := hlocU
  letI : IsLocalization.Away (q.left.appTop.hom d) Γ(V'.left, ⊤) := hlocV
  have hcomm (s : Γ(U.left, ⊤)) : q'.left.appTop.hom (rU.left.appTop.hom s) =
      rV.left.appTop.hom (q.left.appTop.hom s) := by
    have H := congrArg (fun f : V' ⟶ U => f.left.appTop.hom s) hsquare'
    simpa only [Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using H.symm
  have hmap (t : Equiv.Perm (Fin (h + 1))) :
      (σ t).left.appTop.hom.comp rV.left.appTop.hom =
        rV.left.appTop.hom.comp (ρ t).left.appTop.hom := by
    ext s
    change (σ t).left.appTop.hom (rV.left.appTop.hom s) =
      rV.left.appTop.hom ((ρ t).left.appTop.hom s)
    have H := congrArg (fun f : V' ⟶ V => f.left.appTop.hom s) (hσv t)
    simpa only [Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using H
  obtain ⟨hqinj', hqimage'⟩ := s2v_l1a_localized_invariant_image
    q.left.appTop.hom hqinj (fun t => (ρ t).left.appTop.hom) hqimage d
    q'.left.appTop.hom hcomm (fun t => (σ t).left.appTop.hom) hmap
  let z' (i : Fin (h + 1)) := rV.left.appTop.hom (z i)
  let c' (i : Fin (h + 1)) := rU.left.appTop.hom (c i)
  have hEt' : (MvPolynomial.eval₂Hom V'.hom.appTop.hom z').Etale := by
    rw [← s2v_l1a_section_parameter_comp rV z]
    exact s2v_l1a_etale_ringHom_comp _ _ hEt
      (HasRingHomProperty.appTop (P := @Etale) rV.left inferInstance)
  have hSym' : (MvPolynomial.eval₂Hom U'.hom.appTop.hom c').Etale :=
    s2v_l1a_etale_principal_section_parameters rU c d hlocU hSym
  refine ⟨U', V', hU', hV', rU ≫ u, rV ≫ v, q', ?_, ?_, hq', ?_, ?_, σ, z', c',
    ?_, hσq, hqinj', hqimage', hEt', hSym', ?_, ?_, ?_, ?_⟩
  · exact inferInstanceAs (IsOpenImmersion (rU.left ≫ u.left))
  · exact inferInstanceAs (IsOpenImmersion (rV.left ≫ v.left))
  · rw [Category.assoc, hsquare, ← Category.assoc, hsquare', Category.assoc]
  · refine ⟨p', ?_⟩
    change (p' ≫ rV) ≫ v = x
    rw [show p' ≫ rV = p from hp']
    exact hp
  · intro t
    rw [← Category.assoc, hσv, Category.assoc, hρv, ← Category.assoc]
  · intro j
    change q'.left.appTop.hom (rU.left.appTop.hom (c j)) = _
    rw [hcomm, hcoeff j]
    exact DFunLike.congr_fun (s2v_l1a_section_parameter_comp rV z)
      (MvPolynomial.esymm (Fin (h + 1)) Γ(Spec ↧ℂ, ⊤) (j.val + 1))
  · change q'.left.appTop.hom (rU.left.appTop.hom (c (Fin.last h))) = _
    rw [hcomm, hlast, map_prod]
  · change ((s2c_branchIdeal Z B₀ h γ b).comap (rU.left ≫ u.left)).ideal
      ⟨⊤, isAffineOpen_top U'.left⟩ = _
    exact s2v_l1a_curve_point_equation_pullback u.left rU.left
      (s2c_branchIdeal Z B₀ h γ b) (c (Fin.last h)) hI
  · intro i
    change (b.left.ker.comap ((rV ≫ v) ≫ g3_proj Z (h + 1) i).left).ideal
      ⟨⊤, isAffineOpen_top V'.left⟩ = _
    rw [Category.assoc]
    exact s2v_l1a_curve_point_equation_pullback (v ≫ g3_proj Z (h + 1) i).left rV.left
      b.left.ker (z i) (hzi i)

/-- Global comparison for the specified quotient and any complex point of the curve.
Source: Schoen (1988), Lemma 2.2, printed p. 13; Hartshorne, Algebraic Geometry, II.5–6, locality of ideal sheaves. -/
theorem s2v_l1a_pre_local_to_global_aux
    (Z B₀ : Over (Spec ↧ℂ))
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    [IsIntegral B₀.left] [Smooth B₀.hom] [IsProjective B₀.hom]
    (hdimZ : TopologicalSpace.dim Z.left = 1)
    (h : ℕ) (γ : g3_power Z (h + 1) ⟶ B₀) [IsFinite γ.left]
    (hγsurj : Function.Surjective (Point.map γ))
    (hγinv : ∀ τ, s2_permute Z (h + 1) τ ≫ γ = γ)
    (hγ : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Z (h + 1) ⟶ T),
      (∀ τ, s2_permute Z (h + 1) τ ≫ f = f) →
      ∃! u : B₀ ⟶ T, γ ≫ u = f)
    (b : ComplexPoint Z) :
    (s2c_branchIdeal Z B₀ h γ b).comap γ.left =
      ∏ j : Fin (h + 1), (b.left.ker).comap (g3_proj Z (h + 1) j).left := by
  classical
  let X := g3_power Z (h + 1)
  apply s2v_l1a_ideal_comparison_of_complex_principal_charts X B₀ γ
    (s2c_branchIdeal Z B₀ h γ b)
    (fun i : Fin (h + 1) => b.left.ker.comap (g3_proj Z (h + 1) i).left)
  intro x
  obtain ⟨U, V, hU, hV, u, v, q, p, ρ, z, hu, hv, hq, hsquare, hp,
    hρv, hρq, hqinj, hqimage, hEt, hzi, hcov, hbranch⟩ :=
    s2v_l1a_retained_ordered_parameters Z B₀ hdimZ h γ hγinv hγ b x
  letI : IsAffine U.left := hU
  letI : IsAffine V.left := hV
  letI : IsOpenImmersion v.left := hv
  letI : Mono v := Over.mono_of_mono_left v
  let act := s2v_l1a_liftedAction (s2_symmetricPowerAction Z (h + 1)) v ρ hρv
  let act' := ((Over.forget (Spec ↧ℂ)).mapAut V).comp act
  letI := s2_schemeSectionAction V.left (Equiv.Perm (Fin (h + 1))) act'
  have hcov' (g : Equiv.Perm (Fin (h + 1))) (i : Fin (h + 1)) :
      g • z i = z (g i) := by
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
  have hNfix (g : Equiv.Perm (Fin (h + 1))) : g • ∏ i, z i = ∏ i, z i := by
    rw [Finset.smul_prod']
    simp_rw [hcov']
    exact Equiv.prod_comp g z
  obtain ⟨c, hc⟩ := (himage (∏ i, z i)).mpr hNfix
  have hEtC : (MvPolynomial.aeval (R := ℂ) z).toRingHom.Etale := by
    rw [s2v_l1a_structure_section_coefficients] at hEt
    exact (s2v_l1a_etale_eval_change_coefficients_iff _ _ _).mp hEt
  have hflat : letI := (MvPolynomial.aeval (R := ℂ) z).toRingHom.toAlgebra
      Module.Flat (MvPolynomial (Fin (h + 1)) ℂ) Γ(V.left, ⊤) := by
    letI : Algebra (MvPolynomial (Fin (h + 1)) ℂ) Γ(V.left, ⊤) :=
      (MvPolynomial.aeval (R := ℂ) z).toRingHom.toAlgebra
    letI : Algebra.Etale (MvPolynomial (Fin (h + 1)) ℂ) Γ(V.left, ⊤) := hEtC
    infer_instance
  have hI : ((s2c_branchIdeal Z B₀ h γ b).comap u.left).ideal
      ⟨⊤, isAffineOpen_top U.left⟩ = Ideal.span {c} := by
    rw [hbranch]
    exact s2v_l1a_flat_insertion_contraction (K := ℂ) (h + 1) z hcov' hflat
      q.left.appTop.hom hqinj himage c hc 0
  refine ⟨U, V, hU, hV, u, v, q, hv, hsquare, ⟨p, hp⟩, c, z, hI, ?_, hc⟩
  intro i
  rw [← Scheme.IdealSheafData.comap_comp]
  exact hzi i


end HodgeLean.Foundations.Program
