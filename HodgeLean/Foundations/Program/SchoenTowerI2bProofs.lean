import HodgeLean.Foundations.Program.SchoenTowerI2bRetainedChartInertia
import HodgeLean.Foundations.Program.SchoenTowerI2bRetainedBranchSupport
import HodgeLean.Foundations.Program.SchoenTowerI2a
import HodgeLean.Foundations.Program.SchoenTowerI2bChartAction
import HodgeLean.Foundations.Program.SchoenTowerI2bGenericAction
import HodgeLean.Foundations.Program.SchoenTowerI2bTowerGeneric
import HodgeLean.Foundations.Program.SchoenTowerI2bChartScalars
import HodgeLean.Foundations.Program.SchoenTowerI2bMonomialNonzero
import HodgeLean.Foundations.Program.SchoenTowerI2bFieldEigen
import HodgeLean.Foundations.Program.SchoenTowerI2bResidualOrder
import HodgeLean.Foundations.Program.SchoenTowerI2bPeriodDetection
import Mathlib.RingTheory.RootsOfUnity.Complex
import HodgeLean.Foundations.Program.SchoenTowerI2bNormalizationAction
import HodgeLean.Foundations.Program.SchoenTowerI2bIntegralChartAction

/-! # I2b retained normalized inertia
Implication from the retained tower inputs to chart action compatibility and
pointwise inertia on exceptional preimages. HC no distance; AV milestone no distance.
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
/-- The original-field chart action intertwines the retained stage generator.
Source: Schoen (1988), Lemma 2.5, printed p. 15. -/
theorem s2v_i2b_retained_chart_action_aux
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
    (x : ComplexPoint (B i.succ)) :
    ∃ (U : Over (Spec ↧ℂ)) (hU : IsAffine U.left) (u : U ⟶ B i.succ)
      (ηU : Spec W₀.left.functionField ⟶ U.left),
      IsOpenImmersion u.left ∧ x ∈ Set.range (Point.map u) ∧
      ηU ≫ u.left = η i.succ ∧
      ∃ (c : MvPolynomial (Fin (h + 1)) ℂ →+* Γ(U.left, ⊤))
        (J : Finset (Fin (2 * r))) (κ : J ↪ Fin (h + 1))
        (z : Fin (2 * r) → Γ(U.left, ⊤)) (ε : Γ(U.left, ⊤))
        (v : W₀.left.functionField),
        c.Etale ∧
        c.comp MvPolynomial.C =
          ((Scheme.ΓSpecIso ↧ℂ).inv ≫ U.hom.appTop).hom ∧
        (∀ t, t ∈ J ↔ x.left (IsLocalRing.closedPoint ℂ) ∈ (D i.succ t).support) ∧
        (∀ t : J, z t = c (MvPolynomial.X (κ t))) ∧
        (∀ t, t ∉ J → z t = 1) ∧
        (∀ t, ((D i.succ t).comap u.left).ideal ⟨⊤, @isAffineOpen_top U.left hU⟩ = Ideal.span {z t}) ∧
        IsUnit ε ∧
        let φ : Γ(U.left, ⊤) →+* W₀.left.functionField :=
          (ηU.appTop ≫ (Scheme.ΓSpecIso ↧W₀.left.functionField).hom).hom
        letI := φ.toAlgebra
        v ^ S.m = φ ε * ∏ t, (φ (z t)) ^ (g32p_exponents S)[σ t] ∧
        Subfield.closure (Set.range φ ∪ {v}) = ⊤ ∧
        ∃ eN : pullback (s2b_normalizationMap (B i.succ) (η i.succ)).left u.left ≅
            Spec ↧(integralClosure Γ(U.left, ⊤) W₀.left.functionField),
          pullback.snd (s2b_normalizationMap (B i.succ) (η i.succ)).left u.left ≫
              U.left.toSpecΓ =
            eN.hom ≫ Spec.map (CommRingCat.ofHom
              (algebraMap Γ(U.left, ⊤)
                (integralClosure Γ(U.left, ⊤) W₀.left.functionField))) ∧
          ∃ (ζ : ℂ) (δ : W₀.left.functionField ≃ₐ[Γ(U.left, ⊤)] W₀.left.functionField)
            (dn : pullback (s2b_normalizationMap (B i.succ) (η i.succ)).left u.left ⟶
              pullback (s2b_normalizationMap (B i.succ) (η i.succ)).left u.left),
            IsPrimitiveRoot ζ S.m ∧
            δ v = φ (((Scheme.ΓSpecIso ↧ℂ).inv ≫ U.hom.appTop).hom ζ) * v ∧
            dn ≫ pullback.fst (s2b_normalizationMap (B i.succ) (η i.succ)).left u.left =
              pullback.fst (s2b_normalizationMap (B i.succ) (η i.succ)).left u.left ≫ (d i.succ).left ∧
            dn ≫ pullback.snd (s2b_normalizationMap (B i.succ) (η i.succ)).left u.left =
              pullback.snd (s2b_normalizationMap (B i.succ) (η i.succ)).left u.left ∧
            dn ≫ eN.hom = eN.hom ≫ Spec.map
              (CommRingCat.ofHom δ.mapIntegralClosure.toRingEquiv.toRingHom) := by
  have hchart := s2v_i2a_original_field_chart S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder i i.succ x
  obtain ⟨U, hU, u, ηU, hu, hx, hηU, c, J, κ, z, ε, v,
    hc, hbase, hJ, hz, habsent, hideal, hunit, hmono, hgen, eN, hN⟩ := hchart
  refine ⟨U, hU, u, ηU, hu, hx, hηU, c, J, κ, z, ε, v,
    hc, hbase, hJ, hz, habsent, hideal, hunit, hmono, hgen, eN, hN, ?_⟩
  have hdbase : (d i.succ).left ≫
      (s2b_normalizationMap (B i.succ) (η i.succ)).left =
      (s2b_normalizationMap (B i.succ) (η i.succ)).left :=
    congrArg Over.Hom.left (hd i.succ)
  obtain ⟨dn, hdn, hdn_unique⟩ := s2v_i2b_chart_action_exists_unique
    (s2b_normalizationMap (B i.succ) (η i.succ)).left u.left
    (d i.succ).left hdbase
  have horiginal := s2v_towerToOriginal_deck
    (fun j => s2b_normalizationOver (B j) (η j)) w d hdw W₀ eW d₀ hdinit i.succ
  haveI : IsIso (d 0) := s2v_i2b_isIso_of_order (d 0) S.m
    (by have := S.three_le; omega) (horder 0)
  haveI : IsIso d₀ := s2v_i2b_isIso_of_conjugacy eW (d 0) d₀ hdinit
  haveI : IsIso d₀.left := inferInstance
  obtain ⟨δring, hδring⟩ := s2v_i2b_functionField_action W₀.left d₀.left
  have hdom0 : IsDominant (η 0) := s2v_initial_genericSource_dominant
    p₀ hpsurj (h + 1) q₀ γ hγsurj β₀ hβ₀ e₀ (η 0) hη₀
  let I : ∀ j : Fin r, (B j.castSucc).left.IdealSheafData := fun j =>
    D j.castSucc ⟨2 * j.val, by omega⟩ ⊔ D j.castSucc ⟨2 * j.val + 1, by omega⟩
  have hδinitial : Spec.map (CommRingCat.ofHom δring.toRingHom) ≫ η 0 = η 0 := by
    apply (cancel_mono e₀.hom.left).mp
    calc
      (Spec.map (CommRingCat.ofHom δring.toRingHom) ≫ η 0) ≫ e₀.hom.left =
          Spec.map (CommRingCat.ofHom δring.toRingHom) ≫
            (W₀.left.fromSpecStalk (genericPoint W₀.left) ≫ β₀.left) := by
        rw [Category.assoc, hη₀]
      _ = (W₀.left.fromSpecStalk (genericPoint W₀.left) ≫ d₀.left) ≫ β₀.left := by
        rw [← Category.assoc, hδring]
      _ = W₀.left.fromSpecStalk (genericPoint W₀.left) ≫ β₀.left := by
        have hd₀left : d₀.left ≫ β₀.left = β₀.left := congrArg Over.Hom.left hd₀
        rw [Category.assoc, hd₀left]
      _ = η 0 ≫ e₀.hom.left := hη₀.symm
  have hηfixed := s2v_i2b_tower_genericSource_invariant B b I hcartier hblowup
    η hη hdom0 (Spec.map (CommRingCat.ofHom δring.toRingHom)) hδinitial i.succ
  have hηUfixed : Spec.map (CommRingCat.ofHom δring.toRingHom) ≫ ηU = ηU := by
    apply (cancel_mono u.left).mp
    rw [Category.assoc, hηU, hηfixed]
  let φ : Γ(U.left, ⊤) →+* W₀.left.functionField :=
    (ηU.appTop ≫ (Scheme.ΓSpecIso ↧W₀.left.functionField).hom).hom
  letI := φ.toAlgebra
  let δlinear : W₀.left.functionField ≃ₐ[Γ(U.left, ⊤)] W₀.left.functionField :=
    { δring with commutes' := s2v_i2b_chart_coefficient_fixed ηU δring hηUfixed }
  haveI : IsAffine U.left := hU
  haveI : Nonempty U.left := ⟨ηU (IsLocalRing.closedPoint W₀.left.functionField)⟩
  haveI : IsIntegral U.left := isIntegral_of_isOpenImmersion u.left
  haveI : IsDominant (η i.succ) := s2v_i2b_tower_genericSource_dominant B b I
    hcartier hblowup η hη hdom0 i.succ
  haveI : IsDominant (ηU ≫ u.left) := by rw [hηU]; infer_instance
  haveI : IsDominant ηU := IsDominant.of_comp_of_isOpenImmersion ηU u.left
  have hφ : Function.Injective φ := s2v_i2b_chart_coefficient_injective ηU
  have hc_inj := s2v_i2b_etale_injective_of_domain c hc
  have hv_nonzero := s2v_i2b_monomial_generator_ne_zero (h + 1) S.m
    (by have := S.three_le; omega) c hc_inj φ hφ J (fun t => κ t) z hz habsent
    (fun t => (g32p_exponents S)[σ t]) ε hunit v hmono
  let ψ : ℂ →+* Γ(U.left, ⊤) :=
    ((Scheme.ΓSpecIso ↧ℂ).inv ≫ U.hom.appTop).hom
  letI : Algebra ℂ Γ(U.left, ⊤) := ψ.toAlgebra
  letI : Algebra ℂ W₀.left.functionField := (φ.comp ψ).toAlgebra
  haveI : IsScalarTower ℂ Γ(U.left, ⊤) W₀.left.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  let δC : W₀.left.functionField ≃ₐ[ℂ] W₀.left.functionField := δlinear.restrictScalars ℂ
  have hv_fixed : δC (v ^ S.m) = v ^ S.m := by
    let bmon : Γ(U.left, ⊤) := ε * ∏ t, (z t) ^ (g32p_exponents S)[σ t]
    have hvbase : v ^ S.m = φ bmon := by
      simpa only [bmon, map_mul, map_prod, map_pow] using hmono
    rw [hvbase]
    exact δlinear.commutes bmon
  let ζ₀ : ℂ := Complex.exp (2 * Real.pi * Complex.I / S.m)
  have hζ₀ : IsPrimitiveRoot ζ₀ S.m := Complex.isPrimitiveRoot_exp S.m (NeZero.ne _)
  obtain ⟨k, hk, hvk⟩ := s2v_i2b_binomial_generator_eigenvalue S.m
    (by have := S.three_le; omega) ζ₀ hζ₀ δC v hv_nonzero hv_fixed
  let ζ : ℂ := ζ₀ ^ k
  have hζpow : ζ ^ S.m = 1 := by
    dsimp only [ζ]
    rw [pow_right_comm, hζ₀.pow_eq_one, one_pow]
  have hveigen : δlinear v = φ (ψ ζ) * v := hvk
  have hscalarpow : (ψ ζ) ^ S.m = 1 := by rw [← map_pow, hζpow, map_one]
  have hfieldpow : δlinear ^ S.m = 1 := s2v_i2b_field_action_pow_eq_one
    v hgen δlinear (ψ ζ) hveigen S.m hscalarpow
  haveI : Finite (S.H ⧸ S.χ.ker) := Finite.of_injective e e.injective
  obtain ⟨yfree, hyfree⟩ := s2v_i2b_free_curve_point Y Z a p₀ hporbit eY
    hpointAction y hbranch
  have hqorbits := s2v_i1a_original_quotient_orbits S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder i
  haveI : IsDominant (W₀.left.fromSpecStalk (genericPoint W₀.left)) :=
    s2v_fromSpecFunctionField_dominant W₀.left
  have hperiod : ∀ n : ℕ, δlinear ^ n = 1 → S.m ∣ n := by
    intro n hn
    apply s2v_i2b_residual_period_dvd S Y W₀ a e ha1 hamul (h + 1) hh q₀ d₀
      hgenerator hqorbits yfree hyfree n
    exact s2v_i2b_field_period_on_cover W₀
      (W₀.left.fromSpecStalk (genericPoint W₀.left)) d₀ δlinear hδring n hn
  have hfieldorder : orderOf δlinear = S.m := Nat.dvd_antisymm
    (orderOf_dvd_of_pow_eq_one hfieldpow) (hperiod _ (pow_orderOf_eq_one δlinear))
  have hprimitiveR : IsPrimitiveRoot (ψ ζ) S.m :=
    s2v_i2b_eigenvalue_primitive_of_order v hgen δlinear (ψ ζ) hveigen S.m
      hscalarpow hfieldorder
  have hprimitive : IsPrimitiveRoot ζ S.m :=
    hprimitiveR.of_map_of_injective ψ.injective
  haveI : ∀ j, IsIntegral (s2b_normalizationOver (B j) (η j)).left :=
    fun j => inferInstanceAs (IsIntegral (η j).normalization)
  haveI : IsIso (Scheme.stalkClosedPointTo
      (W₀.left.fromSpecStalk (genericPoint W₀.left))) := by
    rw [Scheme.stalkClosedPointTo_fromSpecStalk]
    infer_instance
  haveI : IsIso (Scheme.stalkClosedPointTo ((η 0).toNormalization ≫ eW.hom.left)) := by
    rw [hgeneric]
    infer_instance
  have hstalk0 : IsIso (Scheme.stalkClosedPointTo (η 0).toNormalization) :=
    s2v_i2b_genericSource_stalk_iso_of_comp
      (s2b_normalizationOver (B 0) (η 0)).left W₀.left (η 0).toNormalization eW.hom.left
  haveI : ∀ j, IsIso (d j) := fun j => s2v_i2b_isIso_of_order (d j) S.m
    (by have := S.three_le; omega) (horder j)
  haveI : ∀ j, IsIso (d j).left := fun j => inferInstance
  haveI : IsIso (CommRingCat.ofHom δring.toRingHom) :=
    inferInstanceAs (IsIso δring.toCommRingCatIso.hom)
  have hδnorm0 : Spec.map (CommRingCat.ofHom δring.toRingHom) ≫ (η 0).toNormalization =
      (η 0).toNormalization ≫ (d 0).left := by
    apply (cancel_mono eW.hom.left).mp
    calc
      (Spec.map (CommRingCat.ofHom δring.toRingHom) ≫ (η 0).toNormalization) ≫ eW.hom.left =
          Spec.map (CommRingCat.ofHom δring.toRingHom) ≫
            W₀.left.fromSpecStalk (genericPoint W₀.left) := by rw [Category.assoc, hgeneric]
      _ = W₀.left.fromSpecStalk (genericPoint W₀.left) ≫ d₀.left := hδring
      _ = ((η 0).toNormalization ≫ (d 0).left) ≫ eW.hom.left := by
        have hinit : (d 0).left ≫ eW.hom.left = eW.hom.left ≫ d₀.left :=
          congrArg Over.Hom.left hdinit
        rw [Category.assoc, hinit, ← Category.assoc, hgeneric]
  have hδnorm := s2v_i2b_tower_source_action
    (fun j => (s2b_normalizationOver (B j) (η j)).left) (fun j => (η j).toNormalization)
    (fun j => (w j).left) hw hstalk0 (Spec.map (CommRingCat.ofHom δring.toRingHom))
    (fun j => (d j).left)
    (fun j => (show (d j.succ).left ≫ (w j).left = (w j).left ≫ (d j.castSucc).left from
      congrArg Over.Hom.left (hdw j))) hδnorm0 i.succ
  let qN : Spec W₀.left.functionField ⟶
      pullback (s2b_normalizationMap (B i.succ) (η i.succ)).left u.left :=
    pullback.lift (η i.succ).toNormalization ηU (by
      change (η i.succ).toNormalization ≫ (η i.succ).fromNormalization = ηU ≫ u.left
      rw [Scheme.Hom.toNormalization_fromNormalization, hηU])
  have hqNfirst : qN ≫ pullback.fst
      (s2b_normalizationMap (B i.succ) (η i.succ)).left u.left = (η i.succ).toNormalization :=
    pullback.lift_fst _ _ _
  have hqNsecond : qN ≫ pullback.snd
      (s2b_normalizationMap (B i.succ) (η i.succ)).left u.left = ηU := pullback.lift_snd _ _ _
  have hqNaction : Spec.map (CommRingCat.ofHom δring.toRingHom) ≫ qN = qN ≫ dn := by
    apply pullback.hom_ext
    · rw [Category.assoc, hqNfirst, Category.assoc, hdn.1, ← Category.assoc, hqNfirst]
      exact hδnorm
    · rw [Category.assoc, hqNsecond, Category.assoc, hdn.2, hqNsecond]
      exact hηUfixed
  haveI : IsDominant (qN ≫ pullback.fst
      (s2b_normalizationMap (B i.succ) (η i.succ)).left u.left) := by
    rw [hqNfirst]
    infer_instance
  haveI : IsDominant qN := IsDominant.of_comp_of_isOpenImmersion qN
    (pullback.fst (s2b_normalizationMap (B i.succ) (η i.succ)).left u.left)
  refine ⟨ζ, δlinear, dn, hprimitive, hveigen, hdn.1, hdn.2, ?_⟩
  haveI : Nonempty ↥(pullback (s2b_normalizationMap (B i.succ) (η i.succ)).left u.left : Scheme) :=
    ⟨qN (IsLocalRing.closedPoint W₀.left.functionField)⟩
  haveI : IsIntegral (pullback (s2b_normalizationMap (B i.succ) (η i.succ)).left u.left) :=
    isIntegral_of_isOpenImmersion
      (pullback.fst (s2b_normalizationMap (B i.succ) (η i.succ)).left u.left)
  let bmon : Γ(U.left, ⊤) := ε * ∏ t, (z t) ^ (g32p_exponents S)[σ t]
  have hvbase : v ^ S.m = φ bmon := by
    simpa only [bmon, map_mul, map_prod, map_pow] using hmono
  have hvint : IsIntegral Γ(U.left, ⊤) v := by
    apply IsIntegral.of_pow (n := S.m) (by have := S.three_le; omega)
    rw [hvbase]
    exact isIntegral_algebraMap
  apply s2v_i2b_integral_chart_action S.m (by have := S.three_le; omega) ζ₀ hζ₀
    v hv_nonzero hvint bmon hvbase hgen δlinear (ψ ζ) hveigen eN dn qN hqNaction
  have hbaseSpec : (qN ≫ eN.hom) ≫ Spec.map (CommRingCat.ofHom
      (algebraMap Γ(U.left, ⊤) (integralClosure Γ(U.left, ⊤) W₀.left.functionField))) =
      Spec.map (CommRingCat.ofHom φ) := by
    calc
      (qN ≫ eN.hom) ≫ Spec.map (CommRingCat.ofHom
          (algebraMap Γ(U.left, ⊤) (integralClosure Γ(U.left, ⊤) W₀.left.functionField))) =
          qN ≫ (pullback.snd (s2b_normalizationMap (B i.succ) (η i.succ)).left u.left ≫
            U.left.toSpecΓ) := by rw [Category.assoc, ← hN]
      _ = ηU ≫ U.left.toSpecΓ := by rw [← Category.assoc, hqNsecond]
      _ = Spec.map (CommRingCat.ofHom φ) := s2v_i2b_field_chart_toSpecΓ ηU
  have hbaseRing := congrArg Spec.preimage hbaseSpec
  simp only [Spec.preimage_comp, Spec.preimage_map] at hbaseRing
  intro a
  exact congrArg (fun f : Γ(U.left, ⊤) ⟶ CommRingCat.of W₀.left.functionField => f.hom a) hbaseRing

/-- Every point of the exceptional preimage above an unpaired support has the retained exponent inertia.
Source: G32 v0.16, Lemma 4.3, deeper-stratum inertia. -/
theorem s2v_i2b_unpaired_preimage_inertia_aux
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
    (t : Fin (2 * r)) (ht₀ : t ≠ ⟨2 * i.val, by omega⟩)
    (ht₁ : t ≠ ⟨2 * i.val + 1, by omega⟩) :
    let I := D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
      D i.castSucc ⟨2 * i.val + 1, by omega⟩
    let K := s2c_subscheme (B i.castSucc) I
    let kι := s2c_subschemeι (B i.castSucc) I
    let E := s2c_exceptional (b i) I
    let j : E ⟶ B i.succ := pullback.fst (b i) kι
    let p : E ⟶ K := pullback.snd (b i) kι
    let β := s2b_normalizationMap (B i.succ) (η i.succ)
    ∀ (k : ComplexPoint K),
      (Point.map kι k).left (IsLocalRing.closedPoint ℂ) ∈ (D i.castSucc t).support →
      ∀ x : ComplexPoint (s2b_preimage β j),
        Point.map (s2b_toExceptional β j ≫ p) x = k →
        (Point.map (s2b_preimageDeck β j (d i.succ) (hd i.succ)))^[
          (g32p_exponents S)[σ t]] x = x := by
  classical
  dsimp only
  intro k hk x hx
  let aidx : Fin (2 * r) := ⟨2 * i.val, by omega⟩
  let bidx : Fin (2 * r) := ⟨2 * i.val + 1, by omega⟩
  let I := D i.castSucc aidx ⊔ D i.castSucc bidx
  let kι := s2c_subschemeι (B i.castSucc) I
  let β := s2b_normalizationMap (B i.succ) (η i.succ)
  let j := pullback.fst (b i) kι
  let xW := Point.map (s2b_toCover β j) x
  let xB := Point.map β xW
  let xK := Point.map kι k
  have hwbase := s2v_normalization_transition_base (b i) (η i.succ) (η i.castSucc)
    (hη i) (w i) (hw i)
  have hxbase := s2v_exceptionalPreimage_point_base β
    (s2b_normalizationMap (B i.castSucc) (η i.castSucc)) (b i) kι (w i) hwbase k x hx
  change x ≫ (s2b_toCover β j ≫ w i ≫
    s2b_normalizationMap (B i.castSucc) (η i.castSucc)) = k ≫ kι at hxbase
  rw [hwbase] at hxbase
  have hXB : Point.map (b i) xB = xK := by
    change ((x ≫ s2b_toCover β j) ≫ β) ≫ b i = k ≫ kι
    simpa only [Category.assoc] using hxbase
  have hXBpt : (b i).left (xB.left (IsLocalRing.closedPoint ℂ)) =
      xK.left (IsLocalRing.closedPoint ℂ) := by
    change (b i).left xB.underlying = xK.underlying
    exact (Point.underlying_map (b i) xB).symm.trans (congrArg Point.underlying hXB)
  have hkcentre : xK.left (IsLocalRing.closedPoint ℂ) ∈ I.support := by
    change (k.left ≫ I.subschemeι) (IsLocalRing.closedPoint ℂ) ∈ I.support
    rw [Scheme.Hom.comp_apply]
    exact (Scheme.IdealSheafData.range_subschemeι I).le ⟨_, rfl⟩
  have hprechart := s2v_i2a_original_field_chart S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder i i.castSucc xK
  obtain ⟨U₀, hU₀, u₀, ηU₀, hu₀, hx₀, hηU₀, c₀, J₀, κ₀, z₀, ε₀, v₀,
    hc₀, hbase₀, hJ₀, hz₀, habsent₀, hideal₀, hunit₀, hmono₀, hgen₀, eN₀, hN₀⟩ := hprechart
  haveI : IsAffine U₀.left := hU₀
  haveI : IsOpenImmersion u₀.left := hu₀
  have hidx : aidx ≠ bidx := by
    intro he
    have hv := congrArg Fin.val he
    dsimp only [aidx, bidx] at hv
    omega
  have hupperSupport : xB.left (IsLocalRing.closedPoint ℂ) ∈ (D i.succ t).support := by
    rw [htransform i t]
    exact s2v_i2b_retained_chart_unpaired_support (h + 1) (B i.castSucc) (B i.succ) U₀
      u₀ (b i) (D i.castSucc) aidx bidx t hidx ht₀ ht₁ I rfl
      (hcartier i) (hblowup i) xK hx₀ hkcentre hk c₀ hc₀ J₀ κ₀ z₀ hJ₀ hz₀ hideal₀
      (xB.left (IsLocalRing.closedPoint ℂ)) hXBpt
  have hupperchart := s2v_i2b_retained_chart_action_aux S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder i xB
  obtain ⟨U, hU, u, ηU, hu, hxU, hηU, c, J, κ, z, ε, v,
    hc, hbase, hJ, hz, habsent, hideal, hunit, hmono, hgen, eN, hN,
    ζ, δ, dn, hζ, hδ, hdnfst, hdnsnd, hact⟩ := hupperchart
  haveI : IsAffine U.left := hU
  haveI : IsOpenImmersion u.left := hu
  let φ : Γ(U.left, ⊤) →+* W₀.left.functionField :=
    (ηU.appTop ≫ (Scheme.ΓSpecIso ↧W₀.left.functionField).hom).hom
  letI := φ.toAlgebra
  let ψ : ℂ →+* Γ(U.left, ⊤) :=
    ((Scheme.ΓSpecIso ↧ℂ).inv ≫ U.hom.appTop).hom
  letI : Algebra ℂ Γ(U.left, ⊤) := ψ.toAlgebra
  letI : Algebra ℂ W₀.left.functionField := (φ.comp ψ).toAlgebra
  haveI : IsScalarTower ℂ Γ(U.left, ⊤) W₀.left.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  haveI : Nonempty U.left := ⟨ηU (IsLocalRing.closedPoint W₀.left.functionField)⟩
  haveI : IsIntegral U.left := isIntegral_of_isOpenImmersion u.left
  have hdom0 := s2v_initial_genericSource_dominant p₀ hpsurj (h + 1) q₀ γ hγsurj β₀ hβ₀
    e₀ (η 0) hη₀
  let centres : ∀ j : Fin r, (B j.castSucc).left.IdealSheafData := fun j =>
    D j.castSucc ⟨2 * j.val, by omega⟩ ⊔ D j.castSucc ⟨2 * j.val + 1, by omega⟩
  haveI : IsDominant (η i.succ) := s2v_i2b_tower_genericSource_dominant B b centres
    hcartier hblowup η hη hdom0 i.succ
  haveI : IsDominant (ηU ≫ u.left) := by rw [hηU]; infer_instance
  haveI : IsDominant ηU := IsDominant.of_comp_of_isOpenImmersion ηU u.left
  have hφ : Function.Injective (algebraMap Γ(U.left, ⊤) W₀.left.functionField) :=
    s2v_i2b_chart_coefficient_injective ηU
  let cA : MvPolynomial (Fin (h + 1)) ℂ →ₐ[ℂ] Γ(U.left, ⊤) :=
    { toRingHom := c
      commutes' := by
        intro a
        change c (MvPolynomial.C a) = ψ a
        exact congrArg (fun f : ℂ →+* Γ(U.left, ⊤) => f a) hbase }
  obtain ⟨pU, hpU⟩ := hxU
  have hcond : xW.left ≫ β.left = pU.left ≫ u.left := by
    have he := congrArg (fun q : ComplexPoint (B i.succ) => q.left) hpU
    change pU.left ≫ u.left = xW.left ≫ β.left at he
    exact he.symm
  let qchart : Spec ↧ℂ ⟶ pullback β.left u.left := pullback.lift xW.left pU.left hcond
  have hqU : qchart ≫ pullback.snd β.left u.left = pU.left := pullback.lift_snd _ _ _
  have hqW : qchart ≫ pullback.fst β.left u.left = xW.left := pullback.lift_fst _ _ _
  have hpSupport : pU.left (IsLocalRing.closedPoint ℂ) ∈
      ((D i.succ t).comap u.left).support := by
    rw [Scheme.IdealSheafData.support_comap]
    change u.left (pU.left (IsLocalRing.closedPoint ℂ)) ∈ (D i.succ t).support
    have hp : u.left pU.underlying = xB.underlying :=
      (Point.underlying_map u pU).symm.trans (congrArg Point.underlying hpU)
    exact (congrArg (fun y : (B i.succ).left => y ∈ (D i.succ t).support) hp).mpr hupperSupport
  have hzero := s2v_i2b_principal_support_evaluation U.left ((D i.succ t).comap u.left)
    (z t) (hideal t) pU.left hpSupport
  have htJ : t ∈ J := (hJ t).mpr hupperSupport
  have hfixW := s2v_i2b_retained_chart_cover_point_inertia (h + 1) S.m
    (by have := S.three_le; omega) U rfl W₀.left.functionField cA hc hφ J κ z
    (fun s => (g32p_exponents S)[σ s]) hz habsent ε hunit v hmono hgen ζ hζ δ hδ
    (s2b_normalizationOver (B i.succ) (η i.succ)) (pullback β.left u.left)
    (pullback.snd β.left u.left) (pullback.fst β.left u.left) eN hN
    (d i.succ) dn hdnfst hact qchart pU xW hqU hqW ⟨t, htJ⟩ hzero
  exact (s2v_preimageDeck_iterate_fixed_iff β j (d i.succ) (hd i.succ)
    (g32p_exponents S)[σ t] x).mpr hfixW

end HodgeLean.Foundations.Program
