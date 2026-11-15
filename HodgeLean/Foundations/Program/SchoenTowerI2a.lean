import HodgeLean.Foundations.Program.SchoenTowerI2aProofs

/-! # I2a local equations and normalized monomial inertia
Implication from the retained tower inputs to original-field local charts,
and from explicit monomial chart data to pointwise inertia.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Adapters
open scoped BigOperators Manifold ContDiff OnePoint
namespace HodgeLean.Foundations.Program

/-- All present retained branch divisors have simultaneous etale parameters and a normalization chart in the original field.
Source: Schoen (1988), Lemma 2.2, printed p. 13, and Lemma 2.5, printed p. 15. -/
theorem s2v_i2a_original_field_chart
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
      e (rot t) = Multiplicative.ofAdd ((g32p_exponents S)[t] : ZMod S.m))
    (hy : Function.Injective (fun t => Point.map p₀ (eY (y t))))
    (hbranch : ∀ z : rsq_Quot S.χ.ker C,
      MulAction.stabilizer (S.H ⧸ S.χ.ker) z ≠ ⊥ ↔
        ∃ t, Point.map p₀ (eY z) = Point.map p₀ (eY (y t)))
    (hexp : ∀ t : Fin (g32p_exponents S).length, 0 < (g32p_exponents S)[t] ∧ (g32p_exponents S)[t] < S.m)
    (hpair : ∀ i : Fin r,
      (g32p_exponents S)[σ ⟨2 * i.val, by omega⟩] +
      (g32p_exponents S)[σ ⟨2 * i.val + 1, by omega⟩] = S.m)
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
    (B : Fin (r + 1) → Over (Spec ↧ℂ))
    [∀ i, IsIntegral (B i).left] [∀ i, Smooth (B i).hom]
    [∀ i, IsProjective (B i).hom]
    (e₀ : B 0 ≅ B₀) (b : ∀ i : Fin r, B i.succ ⟶ B i.castSucc)
    (D : ∀ i, Fin (2 * r) → (B i).left.IdealSheafData)
    (hD₀ : ∀ t, D 0 t =
      (s2c_branchIdeal Z B₀ h γ (Point.map p₀ (eY (y (σ t))))).comap e₀.hom.left)
    (htransform : ∀ (i : Fin r) t, D i.succ t = s2c_strictTransform (b i).left
      (D i.castSucc t) (D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
        D i.castSucc ⟨2 * i.val + 1, by omega⟩))
    (hcartier : ∀ (i : Fin r) (x : (B i.succ).left),
      let I := D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
        D i.castSucc ⟨2 * i.val + 1, by omega⟩
      ∃ U : (B i.succ).left.affineOpens, x ∈ U.1 ∧
        Nonempty (((I.comap (b i).left).ideal U) ≃ₗ[Γ((B i.succ).left, U)]
          Γ((B i.succ).left, U)))
    (hblowup : ∀ (i : Fin r) (T : Over (Spec ↧ℂ)) (f : T ⟶ B i.castSucc),
      let I := D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
        D i.castSucc ⟨2 * i.val + 1, by omega⟩
      (∀ x : T.left, ∃ U : T.left.affineOpens, x ∈ U.1 ∧
        Nonempty (((I.comap f.left).ideal U) ≃ₗ[Γ(T.left, U)] Γ(T.left, U))) →
      ∃! u : T ⟶ B i.succ, u ≫ b i = f)
    (η : ∀ i, Spec W₀.left.functionField ⟶ (B i).left)
    [∀ i, QuasiCompact (η i)] [∀ i, QuasiSeparated (η i)]
    (hη₀ : η 0 ≫ e₀.hom.left = W₀.left.fromSpecStalk (genericPoint W₀.left) ≫ β₀.left)
    (hη : ∀ i : Fin r, η i.succ ≫ (b i).left = η i.castSucc)
    (eW : s2b_normalizationOver (B 0) (η 0) ≅ W₀)
    (heW : eW.hom ≫ β₀ = s2b_normalizationMap (B 0) (η 0) ≫ e₀.hom)
    (hgeneric : (η 0).toNormalization ≫ eW.hom.left =
      W₀.left.fromSpecStalk (genericPoint W₀.left))
    (w : ∀ i : Fin r, s2b_normalizationOver (B i.succ) (η i.succ) ⟶
      s2b_normalizationOver (B i.castSucc) (η i.castSucc))
    (hw : ∀ i : Fin r, (η i.succ).toNormalization ≫ (w i).left =
      (η i.castSucc).toNormalization)
    (d : ∀ i, s2b_normalizationOver (B i) (η i) ⟶ s2b_normalizationOver (B i) (η i))
    (hd : ∀ i, d i ≫ s2b_normalizationMap (B i) (η i) = s2b_normalizationMap (B i) (η i))
    (hdinit : d 0 ≫ eW.hom = eW.hom ≫ d₀)
    (hdw : ∀ i : Fin r, d i.succ ≫ w i = w i ≫ d i.castSucc)
    (horder : ∀ i, (End.of (d i)) ^ S.m = 1)
    (i : Fin r)
    (s : Fin (r + 1)) (x : ComplexPoint (B s)) :
    ∃ (U : Over (Spec ↧ℂ)) (hU : IsAffine U.left) (u : U ⟶ B s)
      (ηU : Spec W₀.left.functionField ⟶ U.left),
      IsOpenImmersion u.left ∧ x ∈ Set.range (Point.map u) ∧
      ηU ≫ u.left = η s ∧
      ∃ (c : MvPolynomial (Fin (h + 1)) ℂ →+* Γ(U.left, ⊤))
        (J : Finset (Fin (2 * r))) (κ : J ↪ Fin (h + 1))
        (z : Fin (2 * r) → Γ(U.left, ⊤)) (ε : Γ(U.left, ⊤))
        (v : W₀.left.functionField),
        c.Etale ∧
        c.comp MvPolynomial.C =
          ((Scheme.ΓSpecIso ↧ℂ).inv ≫ U.hom.appTop).hom ∧
        (∀ t, t ∈ J ↔ x.left (IsLocalRing.closedPoint ℂ) ∈ (D s t).support) ∧
        (∀ t : J, z t = c (MvPolynomial.X (κ t))) ∧
        (∀ t, t ∉ J → z t = 1) ∧
        (∀ t, ((D s t).comap u.left).ideal ⟨⊤, @isAffineOpen_top U.left hU⟩ = Ideal.span {z t}) ∧
        IsUnit ε ∧
        let φ : Γ(U.left, ⊤) →+* W₀.left.functionField :=
          (ηU.appTop ≫ (Scheme.ΓSpecIso ↧W₀.left.functionField).hom).hom
        letI := φ.toAlgebra
        v ^ S.m = φ ε * ∏ t, (φ (z t)) ^ (g32p_exponents S)[σ t] ∧
        Subfield.closure (Set.range φ ∪ {v}) = ⊤ ∧
        ∃ eN : pullback (s2b_normalizationMap (B s) (η s)).left u.left ≅
            Spec ↧(integralClosure Γ(U.left, ⊤) W₀.left.functionField),
          pullback.snd (s2b_normalizationMap (B s) (η s)).left u.left ≫
              U.left.toSpecΓ =
            eN.hom ≫ Spec.map (CommRingCat.ofHom
              (algebraMap Γ(U.left, ⊤)
                (integralClosure Γ(U.left, ⊤) W₀.left.functionField))) :=
  s2v_i2a_original_field_chart_aux S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder i s x

example := @s2v_i2a_original_field_chart

/-- Dividing the generic generator by the exceptional coordinate retains every unpaired exponent on both charts.
Source: Schoen (1988), Lemmas 2.4–2.5, printed pp. 14–15, exceptional multiplicity m. -/
theorem s2v_i2a_blowup_exponents
    (K : Type*) [Field K] (n m a b : ℕ) (hm : 0 < m)
    (hab : a + b = m) (α : Fin n → ℕ)
    (ε t x y : K) (z : Fin n → K) (hx : x ≠ 0) (hy : y ≠ 0)
    (ht : t ^ m = ε * x ^ a * y ^ b * ∏ j, z j ^ α j) :
    (t / x) ^ m = ε * (y / x) ^ b * ∏ j, z j ^ α j ∧
    (t / y) ^ m = ε * (x / y) ^ a * ∏ j, z j ^ α j :=
  s2v_i2a_blowup_exponents_aux K n m a b hm hab α ε t x y z hx hy ht

example := @s2v_i2a_blowup_exponents

/-- Each vanishing coordinate contributes its exponent subgroup to pointwise inertia in the integral closure.
Source: Schoen (1988), Lemma 2.5, printed p. 15, and Sublemma 2.9, printed p. 19; G32 v0.16, Lemma 4.3, prime-free monomial inertia. -/
theorem s2v_i2a_normalized_monomial_inertia
    (n m : ℕ) (hm : 0 < m)
    (R K : Type*) [CommRing R] [IsDomain R] [Field K]
    [Algebra ℂ R] [Algebra R K] [Algebra ℂ K] [IsScalarTower ℂ R K]
    (c : MvPolynomial (Fin n) ℂ →ₐ[ℂ] R) (hc : c.toRingHom.Etale)
    (hinj : Function.Injective (algebraMap R K))
    (α : Fin n → ℕ) (ε : R) (hε : IsUnit ε) (v : K)
    (hv : v ^ m = algebraMap R K ε *
      ∏ j, (algebraMap R K (c (MvPolynomial.X j))) ^ α j)
    (hgen : Subfield.closure (Set.range (algebraMap R K) ∪ {v}) = ⊤)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ m)
    (d : K ≃ₐ[R] K) (hd : d v = algebraMap ℂ K ζ * v)
    (p : integralClosure R K →ₐ[ℂ] ℂ) (j : Fin n)
    (hp : p (algebraMap R (integralClosure R K) (c (MvPolynomial.X j))) = 0) :
    Subgroup.zpowers (d.mapIntegralClosure ^ α j) ≤
      { carrier := {g : integralClosure R K ≃ₐ[R] integralClosure R K |
            ∀ b, p (g b) = p b}
        one_mem' := fun _ => rfl
        mul_mem' := fun hg hk b => (hg _).trans (hk b)
        inv_mem' := fun {g} hg b => by
          have H := hg (g⁻¹ b)
          simpa only [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply] using H.symm } :=
  s2v_i2a_normalized_monomial_inertia_aux n m hm R K c hc hinj α ε hε v hv hgen ζ hζ d hd p j hp

example := @s2v_i2a_normalized_monomial_inertia

end HodgeLean.Foundations.Program
