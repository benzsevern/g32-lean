import HodgeLean.Foundations.Curves.SymmetricCharts.StageTwo.CoefficientHelpers
import HodgeLean.Foundations.Program.SchoenTowerI2aInitialBranchChart

/-! # Retained quotient coefficient neighborhoods

HC no distance; AV milestone no distance.
-/
noncomputable section
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Curves.SymmetricCharts.StageTwo
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
attribute [local instance] overSpecAlgebra

/-- A common curve parameter gives actual descended coefficient sections etale near the retained tuple image.
Source: Milne, Jacobian Varieties, §3; SGA 1, Exposé V, §1.
HC no distance; AV milestone no distance.
-/
theorem curve_coefficient_neighborhood
    (C B A : Over (Spec ↧ℂ)) [IsIntegral C.left] [Smooth C.hom] [IsProjective C.hom]
    [IsAffine A.left] (h : ℕ) (a : A ⟶ C) [IsOpenImmersion a.left]
    (γ : g3_power C (h+1) ⟶ B) [IsFinite γ.left]
    (hinv : ∀ σ, s2_permute C (h+1) σ ≫ γ = γ)
    (huniv : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power C (h+1) ⟶ T),
      (∀ σ, s2_permute C (h+1) σ ≫ f = f) → ∃! d : B ⟶ T, γ ≫ d = f)
    (x : ComplexPoint (g3_power C (h+1))) (y : Fin (h+1) → ComplexPoint A)
    (hy : ∀ i, Point.map a (y i) = Point.map (g3_proj C (h+1) i) x)
    (s : Γ(A.left, ⊤))
    (hs : (MvPolynomial.eval₂Hom A.hom.appTop.hom (fun _ : Fin 1 => s)).Etale)
    (hsep : ∀ i j, Point.evaluate ⊤ s (y i) = Point.evaluate ⊤ s (y j) →
      Point.map (g3_proj C (h+1) i) x = Point.map (g3_proj C (h+1) j) x) :
    ∃ O : B.left.affineOpens,
      let V := ComplexPoint.openScheme (g3_power C (h+1)) (γ.left ⁻¹ᵁ O.1)
      let U := ComplexPoint.openScheme B O.1
      ∃ (j : V ⟶ g3_power A (h+1)) (q : V ⟶ U) (p : ComplexPoint V)
        (c : Fin (h+1) → Γ(U.left, ⊤)) (d : Γ(U.left, ⊤)),
        IsOpenImmersion j.left ∧
        j ≫ s2_powerMap a (h+1) = ComplexPoint.openInclusion _ (γ.left ⁻¹ᵁ O.1) ∧
        Point.map (ComplexPoint.openInclusion _ (γ.left ⁻¹ᵁ O.1)) p = x ∧
        ComplexPoint.openInclusion _ (γ.left ⁻¹ᵁ O.1) ≫ γ =
          q ≫ ComplexPoint.openInclusion B O.1 ∧
        Point.evaluate ⊤ d (Point.map q p) ≠ 0 ∧
        ((algebraMap Γ(U.left, ⊤) (Localization.Away d)).comp
          (MvPolynomial.aeval (R := ℂ) c).toRingHom).Etale ∧
        ∀ l, q.left.appTop.hom (c l) = MvPolynomial.aeval (R := ℂ)
          (fun i => (j ≫ g3_proj A (h+1) i).left.appTop.hom s)
          (MvPolynomial.esymm (Fin (h+1)) ℂ (l.val+1)) := by
  letI : Mono a := Over.mono_of_mono_left a
  let yOrdered := s2_lift (h+1) y
  have hyOrdered : Point.map (s2_powerMap a (h+1)) yOrdered = x :=
    s2v_l1a_ordered_point_lift a (h+1) x y hy
  obtain ⟨O, hxO, j, hj, hjSquare⟩ :=
    s2v_l1a_compatible_curve_chart A C B h a γ hinv huniv x yOrdered hyOrdered
  let V := ComplexPoint.openScheme (g3_power C (h+1)) (γ.left ⁻¹ᵁ O.1)
  let U := ComplexPoint.openScheme B O.1
  let v : V ⟶ g3_power C (h+1) := ComplexPoint.openInclusion _ (γ.left ⁻¹ᵁ O.1)
  letI : IsAffine V.left := O.2.preimage γ.left
  letI : IsAffine U.left := O.2
  letI : IsOpenImmersion j.left := hj
  letI : IsOpenImmersion v.left := inferInstanceAs (IsOpenImmersion (γ.left ⁻¹ᵁ O.1).ι)
  letI : Mono v := Over.mono_of_mono_left v
  have hRootEt := s2v_i2a_ordered_curve_chart_parameters_etale A V (h+1) j s hs
  obtain ⟨q, ρ, hqFinite, hqSquare, hρ, hρq, hqInj, hqImage⟩ :=
    s2v_i2a_ordered_invariant_chart C B h γ hinv huniv O
  let r (i : Fin (h+1)) := (j ≫ g3_proj A (h+1) i).left.appTop.hom s
  have hcoord (i : Fin (h+1)) : (j ≫ g3_proj A (h+1) i) ≫ a = v ≫ g3_proj C (h+1) i := by
    have H : s2_powerMap a (h+1) ≫ g3_proj C (h+1) i = g3_proj A (h+1) i ≫ a :=
      s2_check_lift_proj (h+1) _ i
    rw [Category.assoc, ← H, ← Category.assoc, hjSquare]
  have hcov (σ : Equiv.Perm (Fin (h+1))) (i : Fin (h+1)) :
      (ρ σ).left.appTop.hom (r i) = r (σ⁻¹ i) := by
    have H := s2v_l1a_chart_parameter_action V A C (h+1) a v ρ hρ
      (fun i => j ≫ g3_proj A (h+1) i) hcoord s σ⁻¹ i
    change (ρ ((σ⁻¹)⁻¹)).left.appTop.hom (r i) = r (σ⁻¹ i) at H
    simpa only [inv_inv] using H
  obtain ⟨c, hc, _⟩ := s2v_i2a_ordered_coefficient_descent U V h q ρ r hqInj hqImage hcov
  let p := ComplexPoint.asOpenPoint (g3_power C (h+1)) (γ.left ⁻¹ᵁ O.1) x hxO
  have hp : Point.map v p = x := by
    apply Over.OverMorphism.ext
    exact ComplexPoint.liftToOpen_fac (g3_power C (h+1)) (γ.left ⁻¹ᵁ O.1) x hxO
  have hev := s2v_i2a_curve_coordinate_evaluations A V C (h+1) a v
    (fun i => j ≫ g3_proj A (h+1) i) hcoord p x hp y hy s
  have hseparation (i l : Fin (h+1))
      (hil : Point.map (v ≫ g3_proj C (h+1) i) p ≠ Point.map (v ≫ g3_proj C (h+1) l) p) :
      Point.evaluate ⊤ (r i) p ≠ Point.evaluate ⊤ (r l) p := by
    rw [hev i, hev l]
    intro H
    apply hil
    change (p ≫ v) ≫ g3_proj C (h+1) i = (p ≫ v) ≫ g3_proj C (h+1) l
    rw [show p ≫ v = x from hp]
    exact hsep i l H
  letI : Algebra ℂ Γ(V.left, ⊤) := overSpecAlgebra V ⊤
  letI : Algebra ℂ Γ(U.left, ⊤) := overSpecAlgebra U ⊤
  have hRootEtC : (MvPolynomial.aeval (R := ℂ) r).toRingHom.Etale := by
    rw [s2v_l1a_structure_section_coefficients] at hRootEt
    exact (s2v_l1a_etale_eval_change_coefficients_iff _ _ _).mp hRootEt
  letI : LocallyOfFiniteType V.hom := by
    rw [← Over.w v]
    infer_instance
  obtain ⟨d, hd, hEt⟩ := s2v_i2a_ordered_coefficient_etale_neighborhood U V C h v q ρ hρ
    r hcov hqInj hqImage c hc hRootEtC p hseparation
  exact ⟨O, j, q, p, c, d, hj, hjSquare, hp, hqSquare, hd, hEt, hc⟩

end HodgeLean.Foundations.Curves.SymmetricCharts.StageTwo
