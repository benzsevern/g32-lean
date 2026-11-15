import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorSplit

/-! Original-base branch equations for the common signed character.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters
open scoped BigOperators Manifold ContDiff OnePoint
namespace HodgeLean.Foundations.Program

/-- The signed original-field eigenvector has a rational weighted branch equation at every original-base complex point. -/
theorem s2v_i2a_signed_original_branch_equation
    (S : g32p_Supplier) (Y Z W₀ B₀ : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    [IsIntegral W₀.left] [IsProjective W₀.hom]
    [IsIntegral B₀.left] [Smooth B₀.hom] [IsProjective B₀.hom]
    (hdimY : TopologicalSpace.dim Y.left = 1)
    (hdimZ : TopologicalSpace.dim Z.left = 1)
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (hinj : Function.Injective a)
    (p₀ : Y ⟶ Z) [IsFinite p₀.left]
    (hp₀ : ∀ u, a u ≫ p₀ = p₀)
    (hpsurj : Function.Surjective (Point.map p₀))
    (hporbit : ∀ x y : ComplexPoint Y, Point.map p₀ x = Point.map p₀ y ↔
      ∃ u, Point.map (a u) x = y)
    (C : Type) [TopologicalSpace C] [MulAction g32p_G C]
    [ChartedSpace ℂ (rsq_Quot S.χ.ker C)]
    [IsManifold 𝓘(ℂ, ℂ) ω (rsq_Quot S.χ.ker C)]
    (eY : rsq_Quot S.χ.ker C ≃ₜ ComplexPoint Y)
    (hpointAction : ∀ u y, Point.map (a u) (eY y) = eY (u • y))
    (r : ℕ) (σ : Fin (2 * r) ≃ Fin (g32p_exponents S).length)
    (y : Fin (g32p_exponents S).length → rsq_Quot S.χ.ker C)
    (rot : Fin (g32p_exponents S).length → S.H ⧸ S.χ.ker)
    (hrot : ∀ t, b4_IsRotGen ℂ (y t) (rot t) ∧
      e (rot t) = Multiplicative.ofAdd ((g32p_exponents S).get (t) : ZMod S.m))
    (hy : Function.Injective (fun t => Point.map p₀ (eY (y t))))
    (hbranch : ∀ z : rsq_Quot S.χ.ker C,
      MulAction.stabilizer (S.H ⧸ S.χ.ker) z ≠ ⊥ ↔
        ∃ t, Point.map p₀ (eY z) = Point.map p₀ (eY (y t)))
    (hexp : ∀ t : Fin (g32p_exponents S).length, 0 < (g32p_exponents S).get (t) ∧ (g32p_exponents S).get (t) < S.m)
    (hpair : ∀ i : Fin r,
      (g32p_exponents S).get (σ ⟨2 * i.val, by omega⟩) +
      (g32p_exponents S).get (σ ⟨2 * i.val + 1, by omega⟩) = S.m)
    (h : ℕ) (hh : 0 < h + 1)
    (q₀ : g3_power Y (h + 1) ⟶ W₀) [IsFinite q₀.left]
    (hqsurj : Function.Surjective (Point.map q₀))
    (hqinv : ∀ (v : Fin (h + 1) → ZMod S.m) (τ : Equiv.Perm (Fin (h + 1))),
      ∑ t, v t = 0 → s2_action S Y a e (h + 1) v τ ≫ q₀ = q₀)
    (hq : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Y (h + 1) ⟶ T),
      (∀ (v : Fin (h + 1) → ZMod S.m) (τ : Equiv.Perm (Fin (h + 1))),
        ∑ t, v t = 0 → s2_action S Y a e (h + 1) v τ ≫ f = f) →
      ∃! u : W₀ ⟶ T, q₀ ≫ u = f)
    (γ : g3_power Z (h + 1) ⟶ B₀) [IsFinite γ.left]
    (hγsurj : Function.Surjective (Point.map γ))
    (hγinv : ∀ τ, s2_permute Z (h + 1) τ ≫ γ = γ)
    (hγ : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Z (h + 1) ⟶ T),
      (∀ τ, s2_permute Z (h + 1) τ ≫ f = f) →
      ∃! u : B₀ ⟶ T, γ ≫ u = f)
    (β₀ : W₀ ⟶ B₀) [IsFinite β₀.left]
    (hβ₀ : q₀ ≫ β₀ = s2_powerMap p₀ (h + 1) ≫ γ)
    (d₀ : W₀ ⟶ W₀) (hd₀ : d₀ ≫ β₀ = β₀)
    (hgenerator : q₀ ≫ d₀ =
      s2_action S Y a e (h + 1) (s2_delta S (h + 1) hh 1) 1 ≫ q₀)
    (s : ℤ) (hs : s = 1 ∨ s = -1)
    (hcomparison :
    ∀ j : Fin (g32p_exponents S).length,
      let p := (eY (y j)).left (IsLocalRing.closedPoint ℂ)
      ∃ (hp : (a (rot j)).left p = p)
        (ι : Y.left.presheaf.stalk p →+* PowerSeries ℂ),
        Function.Injective ι ∧
        (∃ u : Y.left.presheaf.stalk p, ι u = PowerSeries.X) ∧
        (∀ c : ℂ, ι (HodgeLean.Foundations.Curves.stalkC p c) = PowerSeries.C c) ∧
        ∀ v : Y.left.presheaf.stalk p,
          ι (s2e_fixed_point_stalkPullback Y.left (a (rot j)).left p hp v) =
            PowerSeries.rescale
              (Complex.exp ((s : ℂ) * (2 * Real.pi * Complex.I) /
                (orderOf (rot j) : ℂ))) (ι v))
    (t : W₀.left.functionField) (τ : W₀.left.functionField ≃+* W₀.left.functionField)
    (ht : t ≠ 0)
    (hτ : Spec.map (CommRingCat.ofHom τ.toRingHom) ≫
      W₀.left.fromSpecStalk (genericPoint W₀.left) =
      W₀.left.fromSpecStalk (genericPoint W₀.left) ≫ d₀.left)
    (hcharacter : τ t = ((Scheme.ΓSpecIso ↧ℂ).inv ≫ W₀.hom.appTop ≫
      W₀.left.germToFunctionField ⊤).hom
      (Complex.exp ((s : ℂ) * (2 * Real.pi * Complex.I) / (S.m : ℂ))) * t)
 :
    ∃ κ₀ : B₀.left.functionField ⟶ W₀.left.functionField,
      (Spec.map κ₀ ≫ B₀.left.fromSpecStalk (genericPoint B₀.left) =
        W₀.left.fromSpecStalk (genericPoint W₀.left) ≫ β₀.left) ∧
      ∀ x₀ : ComplexPoint B₀,
      ∃ (V₀ : B₀.left.affineOpens) (hx₀ : x₀.underlying ∈ V₀.1)
        (g₀ : Fin (2 * r) → Γ(B₀.left, V₀))
        (ε₀ : (B₀.left.presheaf.stalk x₀.underlying)ˣ)
        (A₀ B₁ : B₀.left.presheaf.stalk x₀.underlying),
        A₀ ≠ 0 ∧ B₁ ≠ 0 ∧
        (∀ j, (s2c_branchIdeal Z B₀ h γ (Point.map p₀ (eY (y (σ j))))).ideal V₀ =
          Ideal.span {g₀ j}) ∧
        let ρ₀ := s2v_l1b_kval_stalkMap B₀.left x₀.underlying κ₀
        t ^ S.m * (ρ₀ B₁) ^ S.m =
          ρ₀ (ε₀ : B₀.left.presheaf.stalk x₀.underlying) *
          (∏ j, ρ₀ ((B₀.left.presheaf.germ V₀.1 x₀.underlying hx₀).hom (g₀ j)) ^
            (g32p_exponents S).get (σ j)) * (ρ₀ A₀) ^ S.m := by
  have hcurve := s2v_l1b_divisor_original_curve S Y Z hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction y rot hrot hy hbranch hexp s hs hcomparison
  exact s2v_l1b_divisor_symmetric_quotient S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator s hs hcomparison t τ ht hτ hcharacter hcurve

end HodgeLean.Foundations.Program
