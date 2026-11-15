import HodgeLean.Foundations.Program.SchoenTowerL1bFiniteEtaleCoefficients
import HodgeLean.Foundations.Program.SchoenTowerL1bFiniteDescendedEvaluations
import HodgeLean.Foundations.Program.SchoenTowerL1bFiniteRootEmbedding
import HodgeLean.Foundations.Program.SchoenTowerL1bFinitePrincipalChart
import HodgeLean.Foundations.Program.SchoenTowerL1bSupports
import HodgeLean.Foundations.Program.SchoenTowerL1aInvariantSections

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

/-- Every marked branch through the specified quotient point has its own etale coordinate on one affine neighborhood. -/
theorem s2v_l1b_finite_supported_coordinates
    (Z B : Over (Spec ↧ℂ))
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom] [IsIntegral B.left] [Smooth B.hom]
    (hdim : TopologicalSpace.dim Z.left = 1) (h : ℕ)
    (γ : g3_power Z (h + 1) ⟶ B) [IsFinite γ.left]
    (hγsurj : Function.Surjective (Point.map γ))
    (hγinv : ∀ τ, s2_permute Z (h + 1) τ ≫ γ = γ)
    (hγ : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Z (h + 1) ⟶ T),
      (∀ τ, s2_permute Z (h + 1) τ ≫ f = f) → ∃! u : B ⟶ T, γ ≫ u = f)
    (m : ℕ) (b : Fin m → ComplexPoint Z) (hb : Function.Injective b)
    (x : ComplexPoint (g3_power Z (h + 1))) :
    ∃ (U : Over (Spec ↧ℂ)) (hU : IsAffine U.left) (j : U ⟶ B)
      (p : ComplexPoint U) (w : Fin (h + 1) → Γ(U.left, ⊤))
      (f : {t : Fin m // (Point.map γ x).underlying ∈
        (s2c_branchIdeal Z B h γ (b t)).support} ↪ Fin (h + 1)),
      IsOpenImmersion j.left ∧ Point.map j p = Point.map γ x ∧
      (MvPolynomial.eval₂Hom U.hom.appTop.hom w).Etale ∧
      ∀ t, ((s2c_branchIdeal Z B h γ (b t.val)).comap j.left).ideal
        ⟨⊤, @isAffineOpen_top _ hU⟩ = Ideal.span {w (f t)} := by
  classical
  obtain ⟨O, hx, P, a, z, ha, hP, hI, H⟩ :=
    s2v_l1b_common_finite_branch_etale_coefficients Z B hdim h γ hγinv hγ m b hb x
  obtain ⟨c, d, hc, hd, hEt⟩ := H hx
  let X := ComplexPoint.openScheme B O.1
  let V := ComplexPoint.openScheme (g3_power Z (h + 1)) (γ.left ⁻¹ᵁ O.1)
  letI : IsAffine X.left := O.2
  letI : IsAffine V.left := O.2.preimage γ.left
  let u : X ⟶ B := ComplexPoint.openInclusion B O.1
  let v : V ⟶ g3_power Z (h + 1) :=
    ComplexPoint.openInclusion (g3_power Z (h + 1)) (γ.left ⁻¹ᵁ O.1)
  let q : V ⟶ X := Over.homMk (γ.left ∣_ O.1) (by
    change (γ.left ∣_ O.1) ≫ (O.1.ι ≫ B.hom) =
      (γ.left ⁻¹ᵁ O.1).ι ≫ (g3_power Z (h + 1)).hom
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, Over.w γ])
  let xp := ComplexPoint.asOpenPoint (g3_power Z (h + 1)) (γ.left ⁻¹ᵁ O.1) x hx
  have hsquare : q ≫ u = v ≫ γ := by
    apply Over.OverMorphism.ext
    exact morphismRestrict_ι γ.left O.1
  have hv : xp ≫ v = x := by
    apply Over.OverMorphism.ext
    exact ComplexPoint.liftToOpen_fac (g3_power Z (h + 1)) (γ.left ⁻¹ᵁ O.1) x hx
  have hp : Point.map u (Point.map q xp) = Point.map γ x := by
    change (xp ≫ q) ≫ u = x ≫ γ
    rw [Category.assoc, hsquare, ← Category.assoc, hv]
  let κ := {t : Fin m // (Point.map γ x).underlying ∈
    (s2c_branchIdeal Z B h γ (b t)).support}
  let φ := s2t_affinePointAlgHom V xp
  have hzero (t : κ) :
      φ ((s2t_overSectionsAlgHom q) (P.eval (algebraMap ℂ Γ(X.left, ⊤) (a t.val)))) = 0 := by
    have heval : Point.evaluate ⊤ (P.eval (algebraMap ℂ Γ(X.left, ⊤) (a t.val)))
        (Point.map q xp) = 0 := by
      apply (s2v_l1b_evaluate_zero_iff_support X
        ((s2c_branchIdeal Z B h γ (b t.val)).comap O.1.ι)
        ⟨⊤, @isAffineOpen_top _ O.2⟩ _ (hI t.val) (Point.map q xp) (by trivial)).mpr
      rw [Scheme.IdealSheafData.support_comap]
      change (Point.map u (Point.map q xp)).underlying ∈
        (s2c_branchIdeal Z B h γ (b t.val)).support
      rw [hp]
      exact t.property
    rw [s2t_affinePointAlgHom_apply]
    exact (Point.evaluate_map q ⊤ _ xp).symm.trans heval
  have hprod (t : κ) : (∏ i, (φ (z i) - a t.val)) = 0 := by
    have H := hzero t
    change φ ((s2t_overSectionsAlgHom q).toRingHom
      (P.eval (algebraMap ℂ Γ(X.left, ⊤) (a t.val)))) = 0 at H
    rw [s2v_l1b_branch_polynomial_eval (h + 1) z
      (s2t_overSectionsAlgHom q).toRingHom P hP] at H
    have hscalar : φ ((s2t_overSectionsAlgHom q).toRingHom
        (algebraMap ℂ Γ(X.left, ⊤) (a t.val))) = a t.val :=
      (φ.comp (s2t_overSectionsAlgHom q)).commutes (a t.val)
    rw [map_prod] at H
    simp_rw [map_sub] at H
    rw [hscalar] at H
    exact H
  obtain ⟨f, hf⟩ := s2v_l1b_finite_root_embedding (h + 1) (fun i => φ (z i))
    (fun t : κ => a t.val) (ha.comp Subtype.val_injective) hprod
  obtain ⟨af, haf, hafix⟩ := s2v_l1b_extend_finite_values f
    (fun t : κ => a t.val) (ha.comp Subtype.val_injective)
  let l : Γ(X.left, ⊤) →ₐ[ℂ] Localization.Away d :=
    IsScalarTower.toAlgHom ℂ Γ(X.left, ⊤) (Localization.Away d)
  have hmap : ((algebraMap Γ(X.left, ⊤) (Localization.Away d)).comp
      (MvPolynomial.aeval (R := ℂ) c).toRingHom) =
      MvPolynomial.eval₂Hom (algebraMap ℂ (Localization.Away d)) (fun j => l (c j)) := by
    apply MvPolynomial.ringHom_ext
    · intro t
      change algebraMap Γ(X.left, ⊤) (Localization.Away d)
        ((MvPolynomial.aeval (R := ℂ) c) (MvPolynomial.C t)) = _
      rw [MvPolynomial.aeval_C, MvPolynomial.eval₂Hom_C]
      exact (IsScalarTower.algebraMap_apply ℂ Γ(X.left, ⊤) (Localization.Away d) t).symm
    · intro i
      change algebraMap Γ(X.left, ⊤) (Localization.Away d)
        ((MvPolynomial.aeval (R := ℂ) c) (MvPolynomial.X i)) = _
      rw [MvPolynomial.aeval_X, MvPolynomial.eval₂Hom_X']
      rfl
  rw [hmap] at hEt
  have hqinj : Function.Injective (s2t_overSectionsAlgHom q) :=
    s2v_l1a_restricted_sections_injective _ _ γ hγsurj O.1
  have hEt' := s2v_l1b_finite_descended_evaluations_etale (h + 1) z
    (s2t_overSectionsAlgHom q) hqinj P hP c hc l af haf hEt
  let w₀ (i : Fin (h + 1)) := P.eval (algebraMap ℂ Γ(X.left, ⊤) (af i))
  let I (t : κ) := (s2c_branchIdeal Z B h γ (b t.val)).comap u.left
  have hI' (t : κ) : (I t).ideal ⟨⊤, isAffineOpen_top X.left⟩ =
      Ideal.span {w₀ (f t)} := by
    change _ = Ideal.span {P.eval (algebraMap ℂ Γ(X.left, ⊤) (af (f t)))}
    rw [hafix]
    exact hI t.val
  have hd' : Point.evaluate ⊤ d (Point.map q xp) ≠ 0 := by
    rw [Point.evaluate_map q ⊤ d xp]
    exact hd
  obtain ⟨U, hU, j, p, hj, hpj, hw, hJ⟩ :=
    s2v_l1b_finite_principal_evaluation_chart X w₀ f I hI' (Point.map q xp) d hd' hEt'
  letI : IsOpenImmersion j.left := hj
  letI : IsOpenImmersion u.left := inferInstanceAs (IsOpenImmersion O.1.ι)
  refine ⟨U, hU, j ≫ u, p, (fun i => j.left.appTop.hom (w₀ i)), f,
    inferInstanceAs (IsOpenImmersion (j.left ≫ u.left)), ?_, hw, ?_⟩
  · change (p ≫ j) ≫ u = x ≫ γ
    rw [show p ≫ j = xp ≫ q from hpj, Category.assoc, hsquare, ← Category.assoc, hv]
  · intro t
    rw [Over.comp_left, Scheme.IdealSheafData.comap_comp]
    exact hJ t

end HodgeLean.Foundations.Program
