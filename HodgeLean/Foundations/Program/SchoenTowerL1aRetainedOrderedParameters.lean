import HodgeLean.Foundations.Program.SchoenTowerL1aCompatibleCurveChart
import HodgeLean.Foundations.Program.SchoenTowerL1aCurveParameter
import HodgeLean.Foundations.Program.SchoenTowerL1aOrderedPointIdeals
import HodgeLean.Foundations.Program.SchoenTowerL1aEtaleCoefficients
import HodgeLean.Foundations.Program.SchoenTowerL1aChartParameterAction
import HodgeLean.Foundations.Program.SchoenTowerL1aBranchIdealContraction

/-! # Actual ordered parameters on compatible retained affine charts

Implication from the retained quotient and the constructed curve parameter to
compatible affine charts with ordered etale parameters and actual point ideals.
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

/-- Compatible affine restrictions of the retained quotient have actual ordered
etale parameters generating the actual coordinate point ideals.
Source: Schoen (1988), Lemma 2.2, printed p. 13; Hartshorne, Algebraic Geometry, II.5–6. -/
theorem s2v_l1a_retained_separated_ordered_parameters
    (Z B : Over (Spec ↧ℂ))
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (hdim : TopologicalSpace.dim Z.left = 1) (h : ℕ)
    (γ : g3_power Z (h + 1) ⟶ B) [IsFinite γ.left]
    (hγinv : ∀ τ, s2_permute Z (h + 1) τ ≫ γ = γ)
    (hγ : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Z (h + 1) ⟶ T),
      (∀ τ, s2_permute Z (h + 1) τ ≫ f = f) → ∃! u : B ⟶ T, γ ≫ u = f)
    (b : ComplexPoint Z) (x : ComplexPoint (g3_power Z (h + 1))) :
    ∃ (U V : Over (Spec ↧ℂ)) (hU : IsAffine U.left) (hV : IsAffine V.left)
      (u : U ⟶ B) (v : V ⟶ g3_power Z (h + 1)) (q : V ⟶ U)
      (p : ComplexPoint V) (ρ : Equiv.Perm (Fin (h + 1)) → (V ⟶ V))
      (z : Fin (h + 1) → Γ(V.left, ⊤)),
      IsOpenImmersion u.left ∧ IsOpenImmersion v.left ∧ IsFinite q.left ∧
      v ≫ γ = q ≫ u ∧ Point.map v p = x ∧
      (∀ τ, ρ τ ≫ v = v ≫ s2_permute Z (h + 1) τ) ∧
      (∀ τ, ρ τ ≫ q = q) ∧ Function.Injective q.left.appTop.hom ∧
      (∀ s : Γ(V.left, ⊤), s ∈ Set.range q.left.appTop.hom ↔
        ∀ τ, (ρ τ).left.appTop.hom s = s) ∧
      (MvPolynomial.eval₂Hom V.hom.appTop.hom z).Etale ∧
      (∀ i, (b.left.ker.comap ((v ≫ g3_proj Z (h + 1) i).left)).ideal
        ⟨⊤, @isAffineOpen_top V.left hV⟩ = Ideal.span {z i}) ∧
      (∀ τ i, (ρ τ).left.appTop.hom (z i) = z (τ⁻¹ i)) ∧
      ((s2c_branchIdeal Z B h γ b).comap u.left).ideal ⟨⊤, @isAffineOpen_top U.left hU⟩ =
        (Ideal.span {z 0}).comap q.left.appTop.hom ∧
      (∀ i j, Point.map (v ≫ g3_proj Z (h + 1) i) p ≠
        Point.map (v ≫ g3_proj Z (h + 1) j) p →
        Point.evaluate ⊤ (z i) p ≠ Point.evaluate ⊤ (z j) p) := by
  let X := g3_power Z (h + 1)
  obtain ⟨A, hA, a, y, zA, ha, hy, hzEt, hzI, hzsep⟩ :=
    s2v_l1a_separating_curve_parameter_aux Z hdim (h + 1)
      (Fin.cases b (fun i => Point.map (g3_proj Z (h + 1) i) x))
  letI : IsAffine A.left := hA
  letI : IsOpenImmersion a.left := ha
  let yp : ComplexPoint (g3_power A (h + 1)) := s2_lift (h + 1) (fun i => y i.succ)
  have hyp : Point.map (s2_powerMap a (h + 1)) yp = x :=
    s2v_l1a_ordered_point_lift a (h + 1) x (fun i => y i.succ) (fun i => hy i.succ)
  obtain ⟨O, hx, j, hj, hjfac⟩ :=
    s2v_l1a_compatible_curve_chart A Z B h a γ hγinv hγ x yp hyp
  let V₀ := γ.left ⁻¹ᵁ O.1
  let U := ComplexPoint.openScheme B O.1
  let V := ComplexPoint.openScheme X V₀
  let u : U ⟶ B := ComplexPoint.openInclusion B O.1
  let v : V ⟶ X := ComplexPoint.openInclusion X V₀
  letI : IsAffine U.left := O.2
  letI : IsAffine V.left := O.2.preimage γ.left
  letI : IsOpenImmersion j.left := hj
  letI : IsAffine (g3_power A (h + 1)).left := s2v_l1a_ordered_power_affine A (h + 1)
  let q : V ⟶ U := Over.homMk (γ.left ∣_ O.1) (by
    change (γ.left ∣_ O.1) ≫ (O.1.ι ≫ B.hom) = V₀.ι ≫ X.hom
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, Over.w γ])
  have hsquare : v ≫ γ = q ≫ u := by
    apply Over.OverMorphism.ext
    exact (morphismRestrict_ι γ.left O.1).symm
  let p := ComplexPoint.asOpenPoint X V₀ x hx
  have hp : Point.map v p = x := by
    apply Over.OverMorphism.ext
    exact ComplexPoint.liftToOpen_fac X V₀ x hx
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
  let ac (i : Fin (h + 1)) := j ≫ g3_proj A (h + 1) i
  let z (i : Fin (h + 1)) := (ac i).left.appTop.hom zA
  have hac (i : Fin (h + 1)) : ac i ≫ a = v ≫ g3_proj Z (h + 1) i := by
    have H : s2_powerMap a (h + 1) ≫ g3_proj Z (h + 1) i =
        g3_proj A (h + 1) i ≫ a := s2_check_lift_proj (h + 1) _ i
    change (j ≫ g3_proj A (h + 1) i) ≫ a = _
    rw [Category.assoc, ← H, ← Category.assoc, hjfac]
  have hjEt : j.left.appTop.hom.Etale :=
    HasRingHomProperty.appTop (P := @Etale) j.left inferInstance
  have heval : MvPolynomial.eval₂Hom V.hom.appTop.hom z =
      j.left.appTop.hom.comp
        (MvPolynomial.eval₂Hom (g3_power A (h + 1)).hom.appTop.hom
          (fun i => (g3_proj A (h + 1) i).left.appTop.hom zA)) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      change (MvPolynomial.eval₂Hom V.hom.appTop.hom z) (MvPolynomial.C c) = j.left.appTop.hom
        ((MvPolynomial.eval₂Hom (g3_power A (h + 1)).hom.appTop.hom
          (fun i => (g3_proj A (h + 1) i).left.appTop.hom zA)) (MvPolynomial.C c))
      rw [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C]
      have H := congrArg (fun f : V.left ⟶ Spec ↧ℂ => f.appTop.hom c) (Over.w j)
      simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using H.symm
    · intro i
      change (MvPolynomial.eval₂Hom V.hom.appTop.hom z) (MvPolynomial.X i) = j.left.appTop.hom
        ((MvPolynomial.eval₂Hom (g3_power A (h + 1)).hom.appTop.hom
          (fun i => (g3_proj A (h + 1) i).left.appTop.hom zA)) (MvPolynomial.X i))
      rw [MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']
      change (j ≫ g3_proj A (h + 1) i).left.appTop zA = _
      rw [Over.comp_left, Scheme.Hom.comp_appTop]
      rfl
  have hEt : (MvPolynomial.eval₂Hom V.hom.appTop.hom z).Etale := by
    rw [heval]
    exact s2v_l1a_etale_ringHom_comp _ _
      (s2v_l1a_ordered_parameter_etale A zA hzEt (h + 1)) hjEt
  have hzi (i : Fin (h + 1)) :
      (b.left.ker.comap ((v ≫ g3_proj Z (h + 1) i).left)).ideal
        ⟨⊤, isAffineOpen_top V.left⟩ = Ideal.span {z i} := by
    rw [← hac i]
    exact s2v_l1a_curve_point_equation_pullback a.left (ac i).left b.left.ker zA hzI
  letI : IsOpenImmersion v.left := inferInstanceAs (IsOpenImmersion V₀.ι)
  letI : Mono v := Over.mono_of_mono_left v
  letI : Mono a := Over.mono_of_mono_left a
  have hcov (τ : Equiv.Perm (Fin (h + 1))) (i : Fin (h + 1)) :
      (ρ τ).left.appTop.hom (z i) = z (τ⁻¹ i) := by
    have H := s2v_l1a_chart_parameter_action V A Z (h + 1) a v ρ hρv ac hac zA τ⁻¹ i
    change (ρ ((τ⁻¹)⁻¹)).left.appTop.hom (z i) = z (τ⁻¹ i) at H
    simpa only [inv_inv] using H
  have hbranch : ((s2c_branchIdeal Z B h γ b).comap u.left).ideal
      ⟨⊤, isAffineOpen_top U.left⟩ = (Ideal.span {z 0}).comap q.left.appTop.hom := by
    have H := s2v_l1a_branchIdeal_affine_contraction Z B h γ b O
    dsimp only at H
    change ((s2c_branchIdeal Z B h γ b).comap u.left).ideal
      ⟨⊤, isAffineOpen_top U.left⟩ =
        (((b.left.ker.comap (g3_proj Z (h + 1) 0).left).comap v.left).ideal
          ⟨⊤, isAffineOpen_top V.left⟩).comap q.left.appTop.hom at H
    rw [← Scheme.IdealSheafData.comap_comp] at H
    have hz0 := hzi 0
    rw [Over.comp_left] at hz0
    rw [hz0] at H
    exact H
  have hsep : ∀ i j, Point.map (v ≫ g3_proj Z (h + 1) i) p ≠
      Point.map (v ≫ g3_proj Z (h + 1) j) p →
      Point.evaluate ⊤ (z i) p ≠ Point.evaluate ⊤ (z j) p := by
    have hay (i : Fin (h + 1)) : Point.map (ac i) p = y i.succ := by
      apply (cancel_mono a).mp
      change (p ≫ ac i) ≫ a = y i.succ ≫ a
      rw [Category.assoc, hac, ← Category.assoc]
      change Point.map (g3_proj Z (h + 1) i) (Point.map v p) = Point.map a (y i.succ)
      rw [hp, hy]
      rfl
    have heval (i : Fin (h + 1)) : Point.evaluate ⊤ (z i) p =
        Point.evaluate ⊤ zA (y i.succ) := by
      change Point.evaluate ⊤ ((ac i).left.appTop zA) p = _
      have H := Point.evaluate_map (ac i) ⊤ zA p
      rw [hay] at H
      simpa only [TopologicalSpace.Opens.map_top, Scheme.Hom.appTop] using H.symm
    intro i k hik
    rw [heval, heval]
    apply hzsep i.succ k.succ
    intro H
    apply hik
    change Point.map (g3_proj Z (h + 1) i) x = Point.map (g3_proj Z (h + 1) k) x at H
    change (p ≫ v) ≫ g3_proj Z (h + 1) i = (p ≫ v) ≫ g3_proj Z (h + 1) k
    rw [show p ≫ v = x from hp]
    exact H
  exact ⟨U, V, inferInstance, inferInstance, u, v, q, p, ρ, z,
    inferInstanceAs (IsOpenImmersion O.1.ι), inferInstanceAs (IsOpenImmersion V₀.ι),
    inferInstanceAs (IsFinite (γ.left ∣_ O.1)), hsquare, hp, hρv, hρq,
    Hinv.1, Hinv.2, hEt, hzi, hcov, hbranch, hsep⟩

/-- Actual ordered chart parameters and retained branch contraction follow
from the separated-support chart construction.
Source: Schoen (1988), Lemma 2.2, printed p. 13. -/
theorem s2v_l1a_retained_ordered_parameters
    (Z B : Over (Spec ↧ℂ))
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (hdim : TopologicalSpace.dim Z.left = 1) (h : ℕ)
    (γ : g3_power Z (h + 1) ⟶ B) [IsFinite γ.left]
    (hγinv : ∀ τ, s2_permute Z (h + 1) τ ≫ γ = γ)
    (hγ : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Z (h + 1) ⟶ T),
      (∀ τ, s2_permute Z (h + 1) τ ≫ f = f) → ∃! u : B ⟶ T, γ ≫ u = f)
    (b : ComplexPoint Z) (x : ComplexPoint (g3_power Z (h + 1))) :
    ∃ (U V : Over (Spec ↧ℂ)) (hU : IsAffine U.left) (hV : IsAffine V.left)
      (u : U ⟶ B) (v : V ⟶ g3_power Z (h + 1)) (q : V ⟶ U)
      (p : ComplexPoint V) (ρ : Equiv.Perm (Fin (h + 1)) → (V ⟶ V))
      (z : Fin (h + 1) → Γ(V.left, ⊤)),
      IsOpenImmersion u.left ∧ IsOpenImmersion v.left ∧ IsFinite q.left ∧
      v ≫ γ = q ≫ u ∧ Point.map v p = x ∧
      (∀ τ, ρ τ ≫ v = v ≫ s2_permute Z (h + 1) τ) ∧
      (∀ τ, ρ τ ≫ q = q) ∧ Function.Injective q.left.appTop.hom ∧
      (∀ s : Γ(V.left, ⊤), s ∈ Set.range q.left.appTop.hom ↔
        ∀ τ, (ρ τ).left.appTop.hom s = s) ∧
      (MvPolynomial.eval₂Hom V.hom.appTop.hom z).Etale ∧
      (∀ i, (b.left.ker.comap ((v ≫ g3_proj Z (h + 1) i).left)).ideal
        ⟨⊤, @isAffineOpen_top V.left hV⟩ = Ideal.span {z i}) ∧
      (∀ τ i, (ρ τ).left.appTop.hom (z i) = z (τ⁻¹ i)) ∧
      ((s2c_branchIdeal Z B h γ b).comap u.left).ideal ⟨⊤, @isAffineOpen_top U.left hU⟩ =
        (Ideal.span {z 0}).comap q.left.appTop.hom := by
  obtain ⟨U, V, hU, hV, u, v, q, p, ρ, z, hu, hv, hq, hsquare, hp,
    hρv, hρq, hqinj, hqimage, hEt, hzi, hcov, hbranch, _⟩ :=
    s2v_l1a_retained_separated_ordered_parameters Z B hdim h γ hγinv hγ b x
  exact ⟨U, V, hU, hV, u, v, q, p, ρ, z, hu, hv, hq, hsquare, hp,
    hρv, hρq, hqinj, hqimage, hEt, hzi, hcov, hbranch⟩

end HodgeLean.Foundations.Program
