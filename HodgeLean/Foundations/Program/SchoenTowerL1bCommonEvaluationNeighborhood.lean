import HodgeLean.Foundations.Program.SchoenTowerL1bCommonEtaleCoefficients
import HodgeLean.Foundations.Program.SchoenTowerL1bDescendedEvaluationEtale
import HodgeLean.Foundations.Program.SchoenTowerL1aInvariantSections
import HodgeLean.Foundations.Program.SchoenTowerL1bPrincipalEvaluationChart

/-! Actual simultaneous branch evaluations on a principal coefficient neighborhood.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local instance] overSpecAlgebra

/-- Both actual branch polynomial evaluations are etale coordinates on the same localized retained chart. -/
theorem s2v_l1b_common_two_branch_evaluation_neighborhood
    (Z B : Over (Spec ↧ℂ))
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (hdim : TopologicalSpace.dim Z.left = 1) (n : ℕ)
    (γ : g3_power Z (n + 2) ⟶ B) [IsFinite γ.left]
    (hγsurj : Function.Surjective (Point.map γ))
    (hγinv : ∀ τ, s2_permute Z (n + 2) τ ≫ γ = γ)
    (hγ : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Z (n + 2) ⟶ T),
      (∀ τ, s2_permute Z (n + 2) τ ≫ f = f) → ∃! u : B ⟶ T, γ ≫ u = f)
    (b : Fin 2 → ComplexPoint Z) (hb : b 0 ≠ b 1)
    (x : ComplexPoint (g3_power Z (n + 2))) :
    ∃ (O : B.left.affineOpens) (hx : x.underlying ∈ γ.left ⁻¹ᵁ O.1),
      let U := ComplexPoint.openScheme B O.1
      ∃ (P : Polynomial Γ(U.left, ⊤)) (a : Fin 2 → ℂ)
        (c : Fin (n + 2) → Γ(U.left, ⊤)) (d : Γ(U.left, ⊤)),
        a 0 ≠ a 1 ∧
        (∀ k, ((s2c_branchIdeal Z B (n + 1) γ (b k)).comap O.1.ι).ideal
          ⟨⊤, @isAffineOpen_top _ O.2⟩ =
          Ideal.span {P.eval (algebraMap ℂ Γ(U.left, ⊤) (a k))}) ∧
        Point.evaluate ⊤ ((γ.left ∣_ O.1).appTop.hom d)
          (ComplexPoint.asOpenPoint (g3_power Z (n + 2)) (γ.left ⁻¹ᵁ O.1) x hx) ≠ 0 ∧
        (MvPolynomial.eval₂Hom (algebraMap ℂ (Localization.Away d))
          (Sum.elim
            ![algebraMap Γ(U.left, ⊤) (Localization.Away d)
                (P.eval (algebraMap ℂ Γ(U.left, ⊤) (a 0))),
              algebraMap Γ(U.left, ⊤) (Localization.Away d)
                (P.eval (algebraMap ℂ Γ(U.left, ⊤) (a 1)))]
            (fun k : Fin n => algebraMap Γ(U.left, ⊤) (Localization.Away d)
              (c (Fin.rev ⟨k.val + 2, by omega⟩))))).Etale := by
  obtain ⟨O, hx, P, a, z, ha, hP, hI, H⟩ :=
    s2v_l1b_common_two_branch_etale_coefficients Z B hdim (n + 1) γ hγinv hγ b hb x
  obtain ⟨c, d, hc, hd, hEt⟩ := H hx
  let U := ComplexPoint.openScheme B O.1
  let V := ComplexPoint.openScheme (g3_power Z (n + 2)) (γ.left ⁻¹ᵁ O.1)
  let q : V ⟶ U := Over.homMk (γ.left ∣_ O.1) (by
    change (γ.left ∣_ O.1) ≫ (O.1.ι ≫ B.hom) =
      (γ.left ⁻¹ᵁ O.1).ι ≫ (g3_power Z (n + 2)).hom
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, Over.w γ])
  have hqinj : Function.Injective (s2t_overSectionsAlgHom q) :=
    s2v_l1a_restricted_sections_injective _ _ γ hγsurj O.1
  let l : Γ(U.left, ⊤) →ₐ[ℂ] Localization.Away d :=
    IsScalarTower.toAlgHom ℂ Γ(U.left, ⊤) (Localization.Away d)
  have hmap : ((algebraMap Γ(U.left, ⊤) (Localization.Away d)).comp
      (MvPolynomial.aeval (R := ℂ) c).toRingHom) =
      MvPolynomial.eval₂Hom (algebraMap ℂ (Localization.Away d)) (fun j => l (c j)) := by
    apply MvPolynomial.ringHom_ext
    · intro t
      change algebraMap Γ(U.left, ⊤) (Localization.Away d)
        ((MvPolynomial.aeval (R := ℂ) c) (MvPolynomial.C t)) = _
      rw [MvPolynomial.aeval_C, MvPolynomial.eval₂Hom_C]
      exact (IsScalarTower.algebraMap_apply ℂ Γ(U.left, ⊤) (Localization.Away d) t).symm
    · intro j
      change algebraMap Γ(U.left, ⊤) (Localization.Away d)
        ((MvPolynomial.aeval (R := ℂ) c) (MvPolynomial.X j)) = _
      rw [MvPolynomial.aeval_X, MvPolynomial.eval₂Hom_X']
      rfl
  refine ⟨O, hx, P, a, c, d, ha, hI, hd, ?_⟩
  rw [hmap] at hEt
  exact s2v_l1b_descended_evaluations_etale n z (s2t_overSectionsAlgHom q) hqinj
    P hP c hc l (a 0) (a 1) ha hEt

/-- The actual retained base has one affine etale chart with the two branch ideals as its specified first coordinates. -/
theorem s2v_l1b_common_two_branch_affine_evaluations
    (Z B : Over (Spec ↧ℂ))
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (hdim : TopologicalSpace.dim Z.left = 1) (n : ℕ)
    (γ : g3_power Z (n + 2) ⟶ B) [IsFinite γ.left]
    (hγsurj : Function.Surjective (Point.map γ))
    (hγinv : ∀ τ, s2_permute Z (n + 2) τ ≫ γ = γ)
    (hγ : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Z (n + 2) ⟶ T),
      (∀ τ, s2_permute Z (n + 2) τ ≫ f = f) → ∃! u : B ⟶ T, γ ≫ u = f)
    (b : Fin 2 → ComplexPoint Z) (hb : b 0 ≠ b 1)
    (x : ComplexPoint (g3_power Z (n + 2))) :
    ∃ (U : Over (Spec ↧ℂ)) (hU : IsAffine U.left) (j : U ⟶ B)
      (p : ComplexPoint U) (w : Fin 2 ⊕ Fin n → Γ(U.left, ⊤)),
      IsOpenImmersion j.left ∧ Point.map j p = Point.map γ x ∧
      (MvPolynomial.eval₂Hom U.hom.appTop.hom w).Etale ∧
      ∀ k, ((s2c_branchIdeal Z B (n + 1) γ (b k)).comap j.left).ideal
        ⟨⊤, @isAffineOpen_top _ hU⟩ = Ideal.span {w (Sum.inl k)} := by
  obtain ⟨O, hx, P, a, c, d, ha, hI, hd, hEt⟩ :=
    s2v_l1b_common_two_branch_evaluation_neighborhood Z B hdim n γ hγsurj hγinv hγ b hb x
  let V := ComplexPoint.openScheme (g3_power Z (n + 2)) (γ.left ⁻¹ᵁ O.1)
  let X := ComplexPoint.openScheme B O.1
  let u : X ⟶ B := ComplexPoint.openInclusion B O.1
  let v : V ⟶ g3_power Z (n + 2) :=
    ComplexPoint.openInclusion (g3_power Z (n + 2)) (γ.left ⁻¹ᵁ O.1)
  let q : V ⟶ X := Over.homMk (γ.left ∣_ O.1) (by
    change (γ.left ∣_ O.1) ≫ (O.1.ι ≫ B.hom) =
      (γ.left ⁻¹ᵁ O.1).ι ≫ (g3_power Z (n + 2)).hom
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, Over.w γ])
  let xp := ComplexPoint.asOpenPoint (g3_power Z (n + 2)) (γ.left ⁻¹ᵁ O.1) x hx
  let w₀ : Fin 2 ⊕ Fin n → Γ(X.left, ⊤) := Sum.elim
    ![P.eval (algebraMap ℂ Γ(X.left, ⊤) (a 0)),
      P.eval (algebraMap ℂ Γ(X.left, ⊤) (a 1))]
    (fun k => c (Fin.rev ⟨k.val + 2, by omega⟩))
  let I (k : Fin 2) := (s2c_branchIdeal Z B (n + 1) γ (b k)).comap u.left
  letI : IsAffine X.left := O.2
  have hI' (k : Fin 2) : (I k).ideal ⟨⊤, isAffineOpen_top X.left⟩ =
      Ideal.span {w₀ (Sum.inl k)} := by
    fin_cases k <;> exact hI _
  have hd' : Point.evaluate ⊤ d (Point.map q xp) ≠ 0 := by
    rw [Point.evaluate_map q ⊤ d xp]
    exact hd
  have hEt' : (MvPolynomial.eval₂Hom (algebraMap ℂ (Localization.Away d))
      (fun i => algebraMap Γ(X.left, ⊤) (Localization.Away d) (w₀ i))).Etale := by
    convert hEt using 1
    apply congrArg
    funext i
    rcases i with k | k
    · fin_cases k <;> rfl
    · rfl
  obtain ⟨U, hU, j, p, hj, hp, hw, hJ⟩ :=
    s2v_l1b_principal_evaluation_chart X w₀ Sum.inl I hI' (Point.map q xp) d hd' hEt'
  letI : IsOpenImmersion j.left := hj
  letI : IsOpenImmersion u.left := inferInstanceAs (IsOpenImmersion O.1.ι)
  refine ⟨U, hU, j ≫ u, p, (fun i => j.left.appTop.hom (w₀ i)),
    inferInstanceAs (IsOpenImmersion (j.left ≫ u.left)), ?_, hw, ?_⟩
  · change (p ≫ j) ≫ u = x ≫ γ
    rw [show p ≫ j = xp ≫ q from hp, Category.assoc]
    have hsquare : q ≫ u = v ≫ γ := by
      apply Over.OverMorphism.ext
      exact morphismRestrict_ι γ.left O.1
    rw [hsquare, ← Category.assoc]
    have hv : xp ≫ v = x := by
      apply Over.OverMorphism.ext
      exact ComplexPoint.liftToOpen_fac (g3_power Z (n + 2)) (γ.left ⁻¹ᵁ O.1) x hx
    rw [hv]
  · intro k
    rw [Over.comp_left, Scheme.IdealSheafData.comap_comp]
    exact hJ k

end HodgeLean.Foundations.Program
