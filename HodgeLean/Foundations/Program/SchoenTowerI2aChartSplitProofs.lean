import HodgeLean.Foundations.Program.SchoenTowerI2aWeightedPullbackChartAssembly
import HodgeLean.Foundations.Program.SchoenTowerI2aCartierProductGerm
import HodgeLean.Foundations.Program.SchoenTowerL1bKvalSpread
import HodgeLean.Foundations.Program.SchoenTowerI2aAllStageWeightedTransform
import HodgeLean.Foundations.Program.SchoenTowerI2aSignedKummerGenerator
import HodgeLean.Foundations.Program.SchoenTowerI2aSignedOriginalBranchEquation
import HodgeLean.Foundations.Program.SchoenTowerI2aGenericConstants
import HodgeLean.Foundations.Program.SchoenTowerI2aCompatibleFieldNeighborhood
import HodgeLean.Foundations.Program.SchoenTowerI2aInitialTowerChart
import HodgeLean.Foundations.Program.SchoenTowerI2aOrderedCoefficientEtale
import HodgeLean.Foundations.Program.SchoenTowerI2aOrderedEvaluations
import HodgeLean.Foundations.Program.SchoenTowerI2aOrderedCoefficientDescent
import HodgeLean.Foundations.Program.SchoenTowerI2aOrderedInvariantChart
import HodgeLean.Foundations.Program.SchoenTowerI2aFiniteCurveSupport
import HodgeLean.Foundations.Program.SchoenTowerI2aTowerBaseMaps
import HodgeLean.Foundations.Program.SchoenTowerI2aOrderedCurveChart
import HodgeLean.Foundations.Program.SchoenTowerI2aGenericFieldFactor
import HodgeLean.Foundations.Program.SchoenTowerN2a
import HodgeLean.Foundations.Program.SchoenTowerI2aFixedFieldGalois
import HodgeLean.Foundations.Program.SchoenTowerI2aFixedCoefficients
import HodgeLean.Foundations.Program.SchoenTowerI2aFixedNormalization
import HodgeLean.Foundations.Program.SchoenTowerI2aResidualCategorical
import HodgeLean.Foundations.Program.SchoenTowerI2aAffineKummerGenerator
import HodgeLean.Foundations.Program.SchoenTowerI2aResidualOrder
import HodgeLean.Foundations.Program.SchoenTowerI2aKummerGenerator
import HodgeLean.Foundations.Program.SchoenTowerI2aFiniteFieldPoints
import HodgeLean.Foundations.Program.SchoenTowerI2aDeckFaithfulness
import HodgeLean.Foundations.Program.SchoenTowerI2aFractionDeck
import HodgeLean.Foundations.Program.SchoenTowerI2aCoefficientEmbedding
import HodgeLean.Foundations.Program.SchoenTowerI2aFieldDeckPowers
import HodgeLean.Foundations.Program.SchoenTowerI2aFieldLiftUniqueness
import HodgeLean.Foundations.Program.SchoenTowerI2aDeckCoefficients
import HodgeLean.Foundations.Program.SchoenTowerI2aRetainedDeck
import HodgeLean.Foundations.Program.SchoenTowerFoundC2
import HodgeLean.Foundations.Program.SchoenTowerI2aRootChoices
import HodgeLean.Foundations.Program.SchoenTowerI2aPointedRootCover
import HodgeLean.Foundations.Program.SchoenTowerI2aNormalGeneratorInertia
import HodgeLean.Foundations.Program.SchoenTowerI2aMonomialRotation
import HodgeLean.Foundations.Program.SchoenTowerI2aMonomialParameters
import HodgeLean.Foundations.Program.SchoenTowerI2aGenericCharts
import HodgeLean.Foundations.Program.SchoenTowerI2aFieldHelpers
import HodgeLean.Foundations.Program.SchoenTowerI1a
import HodgeLean.Foundations.Program.SchoenTowerI1b
import HodgeLean.Foundations.Program.SchoenTowerL1a
import HodgeLean.Foundations.Program.SchoenTowerL1b
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import HodgeLean.Foundations.Program.SchoenTowerI2aOpenNormalizationSquare
import HodgeLean.Foundations.Program.SchoenTowerI2aRetainedStepPointSupport

/-! # I2.1 strict branch parameters and Kummer coefficients
Implication from the retained tower inputs to simultaneous strict branch
parameters and a compatible original-field Kummer equation after shrinking.
The two geometric construction bodies remain open.
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

/-- Reduced strict branch equations in an etale chart, with the original-field normalization square on every affine refinement.
Source: Schoen (1988), Lemmas 2.2–2.5, printed pp. 13–15; Mathlib, Scheme.Hom.normalizationObjIso. -/
theorem s2v_i2a_strict_transform_parameters_aux
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
        (z : Fin (2 * r) → Γ(U.left, ⊤)),
        c.Etale ∧
        c.comp MvPolynomial.C =
          ((Scheme.ΓSpecIso ↧ℂ).inv ≫ U.hom.appTop).hom ∧
        (∀ t, t ∈ J ↔ x.left (IsLocalRing.closedPoint ℂ) ∈ (D s t).support) ∧
        (∀ t : J, z t = c (MvPolynomial.X (κ t))) ∧
        (∀ t, t ∉ J → z t = 1) ∧
        (∀ t, ((D s t).comap u.left).ideal ⟨⊤, @isAffineOpen_top U.left hU⟩ = Ideal.span {z t}) ∧
        ∀ (V : Over (Spec ↧ℂ)) (hV : IsAffine V.left) (k : V ⟶ U)
          (ηV : Spec W₀.left.functionField ⟶ V.left),
          IsOpenImmersion k.left → ηV ≫ k.left = ηU →
          let φ : Γ(V.left, ⊤) →+* W₀.left.functionField :=
            (ηV.appTop ≫ (Scheme.ΓSpecIso ↧W₀.left.functionField).hom).hom
          letI := φ.toAlgebra
          ∃ eN : pullback (s2b_normalizationMap (B s) (η s)).left (k ≫ u).left ≅
              Spec ↧(integralClosure Γ(V.left, ⊤) W₀.left.functionField),
            pullback.snd (s2b_normalizationMap (B s) (η s)).left (k ≫ u).left ≫
                V.left.toSpecΓ =
              eN.hom ≫ Spec.map (CommRingCat.ofHom
                (algebraMap Γ(V.left, ⊤)
                  (integralClosure Γ(V.left, ⊤) W₀.left.functionField))) := by
  classical
  have hL1bCharts := s2v_l1b_blowup_charts S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder i
  have hcenters (j : Fin r) :
      (D j.castSucc ⟨2 * j.val, by omega⟩ ⊔
        D j.castSucc ⟨2 * j.val + 1, by omega⟩).support ≠ ⊤ :=
    s2v_i2a_center_support_ne_top (b j).left _ (hcartier j)
  haveI : IsDominant β₀.left := n1bc_dominant_of_points_surjective β₀
    (n1bc_originalCover_points_surjective p₀ hpsurj (h + 1) q₀ γ hγsurj β₀ hβ₀)
  haveI : IsDominant (W₀.left.fromSpecStalk (genericPoint W₀.left)) :=
    s2_genericPointMorphism_dominant W₀.left
  haveI : IsDominant (η 0 ≫ e₀.hom.left) := by
    rw [hη₀]
    infer_instance
  have hdom : ∀ t, IsDominant (η t) := by
    intro t
    induction t using Fin.induction with
    | zero => exact IsDominant.of_comp_of_isOpenImmersion (η 0) e₀.hom.left
    | succ j ih =>
      letI := ih
      exact s2v_i2a_retained_field_lift_dominant (B j.succ) (B j.castSucc)
        (b j) _ (hcenters j) (hblowup j) (η j.castSucc) (η j.succ) (hη j)
  have charts : ∀ (t : Fin (r + 1)) (x : ComplexPoint (B t)),
      ∃ (U : Over (Spec ↧ℂ)) (hU : IsAffine U.left) (u : U ⟶ B t)
        (p : ComplexPoint U), IsOpenImmersion u.left ∧ Point.map u p = x ∧
      ∃ (c : MvPolynomial (Fin (h + 1)) ℂ →+* Γ(U.left, ⊤))
        (J : Finset (Fin (2 * r))) (κ : J ↪ Fin (h + 1))
        (z : Fin (2 * r) → Γ(U.left, ⊤)),
        c.Etale ∧
        c.comp MvPolynomial.C = ((Scheme.ΓSpecIso ↧ℂ).inv ≫ U.hom.appTop).hom ∧
        (∀ l, l ∈ J ↔ x.underlying ∈ (D t l).support) ∧
        (∀ l : J, z l = c (MvPolynomial.X (κ l))) ∧
        (∀ l, l ∉ J → z l = 1) ∧
        (∀ l, ((D t l).comap u.left).ideal ⟨⊤, @isAffineOpen_top U.left hU⟩ =
          Ideal.span {z l}) := by
    intro t
    induction t using Fin.induction with
    | zero =>
      intro x
      obtain ⟨xOrdered, hxOrdered⟩ := hγsurj (Point.map e₀.hom x)
      obtain ⟨U, hU, u, p, c, J, κ, z, hu, hp, hc, hJ, hz, hab, hid⟩ :=
        s2v_i2a_simultaneous_initial_tower_chart Z B₀ (B 0) hdimZ h γ hγinv hγ
          (fun t => Point.map p₀ (eY (y (σ t)))) (hy.comp σ.injective)
          e₀ (D 0) hD₀ x xOrdered hxOrdered
      letI : Algebra ℂ Γ(U.left, ⊤) := overSpecAlgebra U ⊤
      refine ⟨U, hU, u, p, hu, hp, c.toRingHom, J, κ, z, hc, ?_, hJ, hz, hab, hid⟩
      ext a
      simpa only [overSpecAlgebra, RingHom.algebraMap_toAlgebra, RingHom.comp_apply,
        Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, TopologicalSpace.Opens.map_top,
        CommRingCat.hom_comp, RingHom.comp_apply, MvPolynomial.algebraMap_eq,
        AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using c.commutes a
    | succ j ih =>
      intro x
      obtain ⟨U, hU, u, p, hu, hp, c, J, κ, z, hc, hcC, hJ, hz, hab, hid⟩ :=
        ih (Point.map (b j) x)
      letI : IsAffine U.left := hU
      letI : IsOpenImmersion u.left := hu
      letI : Nonempty U.left := ⟨p.underlying⟩
      letI : IsIntegral U.left := isIntegral_of_isOpenImmersion u.left
      letI := hdom j.succ
      have hx : (b j).left x.underlying ∈ Set.range u.left :=
        ⟨p.underlying, congrArg Point.underlying hp⟩
      have hD (l : J) : ((D j.castSucc l).comap u.left).ideal
          ⟨⊤, isAffineOpen_top _⟩ = Ideal.span {c (MvPolynomial.X (κ l))} := by
        rw [hid, hz]
      have hnone (l) (hl : l ∉ J) : ((D j.castSucc l).comap u.left).ideal
          ⟨⊤, isAffineOpen_top _⟩ = ⊤ := by rw [hid, hab l hl, Ideal.span_singleton_one]
      obtain ⟨V, hV, v, q, hv, hq, ηV, hηV, hηdom, a, J', κ', z', _, ha, haC,
          hsupp, hcoord, hunit, hideals⟩ :=
        s2v_i2a_retained_step_point_exact_support (h + 1) (B j.castSucc) (B j.succ)
          U (b j) _ u c hc hcC (hblowup j) (hcartier j) (D j.castSucc) J κ
          ⟨2 * j.val, by omega⟩ ⟨2 * j.val + 1, by omega⟩
          (by intro H; have Hval := congrArg Fin.val H; dsimp only at Hval; omega) rfl hD hnone x hx (η j.succ)
      refine ⟨V, hV, v, q, hv, hq, a, J', κ', z', ha, haC, ?_, hcoord, hunit, ?_⟩
      · simpa only [← htransform] using hsupp
      · simpa only [← htransform] using hideals
  obtain ⟨U, hU, u, p, hu, hp, c, J, κ, z, hc, hcC, hJ, hz, hab, hid⟩ := charts s x
  letI : IsAffine U.left := hU
  letI : IsOpenImmersion u.left := hu
  letI : Nonempty U.left := ⟨p.underlying⟩
  letI := hdom s
  obtain ⟨ηU, hηU, _⟩ := s2v_i2a_dominant_field_point_open_factor u.left (η s)
  refine ⟨U, hU, u, ηU, hu, ⟨p, hp⟩, hηU.1, c, J, κ, z, hc, hcC, hJ, hz, hab, hid, ?_⟩
  intro V hV k ηV hk hηV
  letI : IsAffine V.left := hV
  letI : IsOpenImmersion k.left := hk
  haveI : IsOpenImmersion (k ≫ u).left :=
    inferInstanceAs (IsOpenImmersion (k.left ≫ u.left))
  apply s2v_i2a_open_field_normalization_square (η s) (k ≫ u).left ηV
  change ηV ≫ (k.left ≫ u.left) = η s
  rw [← Category.assoc, hηV, hηU.1]

/-- After shrinking a supplied strict branch chart at its specified point, its pulled-back parameters give the prescribed original-field Kummer coefficient.
Source: Schoen (1988), Lemmas 2.3–2.5, printed pp. 14–15. -/
theorem s2v_i2a_branch_monomial_coefficient_aux
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
    (s : Fin (r + 1)) (x : ComplexPoint (B s))
    (U : Over (Spec ↧ℂ)) (hU : IsAffine U.left) (u : U ⟶ B s)
    (ηU : Spec W₀.left.functionField ⟶ U.left)
    (hu : IsOpenImmersion u.left) (hxU : x ∈ Set.range (Point.map u))
    (hηU : ηU ≫ u.left = η s)
    (c : MvPolynomial (Fin (h + 1)) ℂ →+* Γ(U.left, ⊤))
    (J : Finset (Fin (2 * r))) (κ : J ↪ Fin (h + 1))
    (z : Fin (2 * r) → Γ(U.left, ⊤))
    (hc : c.Etale)
    (hscalar : c.comp MvPolynomial.C =
      ((Scheme.ΓSpecIso ↧ℂ).inv ≫ U.hom.appTop).hom)
    (hJ : ∀ t, t ∈ J ↔ x.left (IsLocalRing.closedPoint ℂ) ∈ (D s t).support)
    (hz : ∀ t : J, z t = c (MvPolynomial.X (κ t)))
    (habsent : ∀ t, t ∉ J → z t = 1)
    (hideal : ∀ t, ((D s t).comap u.left).ideal
      ⟨⊤, @isAffineOpen_top U.left hU⟩ = Ideal.span {z t}) :
    ∃ (V : Over (Spec ↧ℂ)) (hV : IsAffine V.left) (k : V ⟶ U)
      (ηV : Spec W₀.left.functionField ⟶ V.left)
      (cV : MvPolynomial (Fin (h + 1)) ℂ →+* Γ(V.left, ⊤))
      (zV : Fin (2 * r) → Γ(V.left, ⊤)) (ε : Γ(V.left, ⊤))
      (v : W₀.left.functionField),
      IsOpenImmersion k.left ∧ x ∈ Set.range (Point.map (k ≫ u)) ∧
      ηV ≫ k.left = ηU ∧
      cV = k.left.appTop.hom.comp c ∧
      (∀ t, zV t = k.left.appTop.hom (z t)) ∧
      cV.Etale ∧
      cV.comp MvPolynomial.C =
        ((Scheme.ΓSpecIso ↧ℂ).inv ≫ V.hom.appTop).hom ∧
      (∀ t : J, zV t = cV (MvPolynomial.X (κ t))) ∧
      (∀ t, t ∉ J → zV t = 1) ∧
      (∀ t, ((D s t).comap (k ≫ u).left).ideal
        ⟨⊤, @isAffineOpen_top V.left hV⟩ = Ideal.span {zV t}) ∧
      IsUnit ε ∧
      let φ : Γ(V.left, ⊤) →+* W₀.left.functionField :=
        (ηV.appTop ≫ (Scheme.ΓSpecIso ↧W₀.left.functionField).hom).hom
      v ^ S.m = φ ε * ∏ t, (φ (zV t)) ^ (g32p_exponents S)[σ t] ∧
      Subfield.closure (Set.range φ ∪ {v}) = ⊤ := by
  haveI : IsIso d₀ := s2v_i2a_periodic_retained_deck_isIso eW (d 0) d₀ hdinit S.m
    (by have := S.three_le; omega) (horder 0)
  haveI : IsIso d₀.left := inferInstanceAs (IsIso ((Over.forget (Spec ↧ℂ)).map d₀))
  obtain ⟨δ, hδ, hδunique⟩ := s2t_functionField_deck W₀.left (asIso d₀.left)
  haveI : IsDominant (W₀.left.fromSpecStalk (genericPoint W₀.left)) :=
    s2_genericPointMorphism_dominant W₀.left
  have hδorder : orderOf δ.commRingCatIsoToRingEquiv = orderOf (End.of d₀) :=
    s2v_i2a_field_deck_order_eq W₀ (W₀.left.fromSpecStalk (genericPoint W₀.left))
      d₀ δ.commRingCatIsoToRingEquiv hδ
  have hd₀period : (End.of d₀.left) ^ S.m = 1 := by
    have H := s2v_i2a_retained_deck_period eW (d 0) d₀ hdinit S.m (horder 0)
    have Hleft := congrArg ((Over.forget (Spec ↧ℂ)).mapEnd W₀ : End W₀ → End W₀.left) H
    rw [map_pow, map_one] at Hleft
    change (End.of d₀.left) ^ S.m = 1 at Hleft
    exact Hleft
  have hδperiod : δ.commRingCatIsoToRingEquiv ^ S.m = 1 :=
    s2v_i2a_field_deck_period (W₀.left.fromSpecStalk (genericPoint W₀.left))
      d₀.left δ.commRingCatIsoToRingEquiv hδ S.m hd₀period
  haveI : LocallyQuasiFinite
      (W₀.left.fromSpecStalk (genericPoint W₀.left) ≫ β₀.left) :=
    Scheme.Hom.quasiFiniteAt_iff.mp (β₀.left.quasiFiniteAt (genericPoint W₀.left))
  haveI : LocallyQuasiFinite (η 0 ≫ e₀.hom.left) := by rw [hη₀]; infer_instance
  haveI : LocallyQuasiFinite (η 0) := LocallyQuasiFinite.of_comp (η 0) e₀.hom.left
  have hfieldQF := s2v_i2a_tower_field_points_locallyQuasiFinite r
    (fun t => (B t).left) (fun t => (b t).left) η hη
  haveI : LocallyQuasiFinite (η s) := hfieldQF s
  have hDeckη₀ : Spec.map δ.hom ≫ η 0 = η 0 := by
    apply (cancel_mono e₀.hom.left).mp
    calc
      (Spec.map δ.hom ≫ η 0) ≫ e₀.hom.left =
          Spec.map δ.hom ≫ (W₀.left.fromSpecStalk (genericPoint W₀.left) ≫ β₀.left) := by
        rw [Category.assoc, hη₀]
      _ = (Spec.map δ.hom ≫ W₀.left.fromSpecStalk (genericPoint W₀.left)) ≫ β₀.left :=
        (Category.assoc _ _ _).symm
      _ = (W₀.left.fromSpecStalk (genericPoint W₀.left) ≫ d₀.left) ≫ β₀.left := by rw [hδ]; rfl
      _ = W₀.left.fromSpecStalk (genericPoint W₀.left) ≫ β₀.left := by
        rw [Category.assoc, show d₀.left ≫ β₀.left = β₀.left from congrArg Over.Hom.left hd₀]
      _ = η 0 ≫ e₀.hom.left := hη₀.symm
  have hqorbits := s2v_i1a_original_quotient_orbits S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder i
  have hd₀fullorder : orderOf (End.of d₀) = S.m :=
    s2v_i2a_residual_order_eq S Y W₀ a e ha1 hamul hinj (h + 1) hh q₀
      (fun x z hx => (hqorbits x z).mp hx) d₀ hgenerator
      (s2v_i2a_retained_deck_period eW (d 0) d₀ hdinit S.m (horder 0))
  have hδfullorder : orderOf δ.commRingCatIsoToRingEquiv = S.m :=
    hδorder.trans hd₀fullorder
  have hγorbits := s2v_i1a_symmetric_quotient_orbits S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder i
  have hβorbits := s2v_i1b_residual_quotient_orbits S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder i
  have hβcategorical := s2v_i2a_residual_categorical_quotient W₀ B₀
    (zmtiso_normal_of_smooth B₀.left B₀.hom) d₀ S.m
    (by have := S.three_le; omega)
    (s2v_i2a_retained_deck_period eW (d 0) d₀ hdinit S.m (horder 0)) β₀ hd₀
    (n1bc_originalCover_points_surjective p₀ hpsurj (h + 1) q₀ γ hγsurj β₀ hβ₀)
    (fun x z hx => by
      obtain ⟨k, hk, heq⟩ := (hβorbits x z).mp hx
      exact ⟨k, heq⟩)
  let βinit : W₀ ⟶ B 0 := β₀ ≫ e₀.inv
  haveI : IsFinite βinit.left := inferInstanceAs (IsFinite (β₀.left ≫ e₀.inv.left))
  have hβinitd : d₀ ≫ βinit = βinit := by
    dsimp only [βinit]
    rw [← Category.assoc, hd₀]
  have hβinitcat (T : Over (Spec ↧ℂ)) (f : W₀ ⟶ T) (hf : d₀ ≫ f = f) :
      ∃! u : B 0 ⟶ T, βinit ≫ u = f := by
    obtain ⟨v, hv, hvunique⟩ := hβcategorical T f hf
    refine ⟨e₀.hom ≫ v, ?_, ?_⟩
    · change (β₀ ≫ e₀.inv) ≫ (e₀.hom ≫ v) = f
      rw [Category.assoc, e₀.inv_hom_id_assoc]
      exact hv
    · intro w hw
      have H : e₀.inv ≫ w = v := hvunique (e₀.inv ≫ w) (by
        change β₀ ≫ (e₀.inv ≫ w) = f
        rw [← Category.assoc]
        exact hw)
      apply (cancel_epi e₀.inv).mp
      change e₀.inv ≫ w = e₀.inv ≫ (e₀.hom ≫ v)
      rw [e₀.inv_hom_id_assoc]
      exact H
  let eWN : (η 0).normalization ≅ W₀.left := (Over.forget (Spec ↧ℂ)).mapIso eW
  have heWN : eWN.hom ≫ βinit.left = (η 0).fromNormalization := by
    have H := congrArg Over.Hom.left heW
    change eWN.hom ≫ β₀.left = (η 0).fromNormalization ≫ e₀.hom.left at H
    change eWN.hom ≫ (β₀.left ≫ e₀.inv.left) = (η 0).fromNormalization
    rw [← Category.assoc, H, Category.assoc, ← Over.comp_left, e₀.hom_inv_id,
      Over.id_left, Category.comp_id]
  obtain ⟨Vinit, hVinit, hxVinit, _⟩ := exists_isAffineOpen_mem_and_subset
    (show βinit.left (genericPoint W₀.left) ∈ (⊤ : (B 0).left.Opens) from trivial)
  haveI : Nonempty Vinit := ⟨⟨βinit.left (genericPoint W₀.left), hxVinit⟩⟩
  haveI : Nonempty (βinit.left ⁻¹ᵁ Vinit) := ⟨⟨genericPoint W₀.left, hxVinit⟩⟩
  obtain ⟨θfixed, hθfixedAffine, hθfixed, hθfixedIso⟩ :=
    s2v_i2a_retained_fixed_field_normalization W₀ (B 0) βinit d₀ hβinitd hβinitcat
      (η 0) eWN heWN hgeneric δ.commRingCatIsoToRingEquiv hδ Vinit hVinit
  letI : IsAffineHom θfixed := hθfixedAffine
  letI : IsIso θfixed.fromNormalization := hθfixedIso
  have hbranchPullback := s2v_l1a_branchIdeal_pullback S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder i
  have hcenters (j : Fin r) :
      (D j.castSucc ⟨2 * j.val, by omega⟩ ⊔
        D j.castSucc ⟨2 * j.val + 1, by omega⟩).support ≠ ⊤ :=
    s2v_i2a_center_support_ne_top (b j).left _ (hcartier j)
  haveI : IsDominant β₀.left := n1bc_dominant_of_points_surjective β₀
    (n1bc_originalCover_points_surjective p₀ hpsurj (h + 1) q₀ γ hγsurj β₀ hβ₀)
  haveI : IsDominant (η 0 ≫ e₀.hom.left) := by
    rw [hη₀]
    infer_instance
  have hdom : ∀ t, IsDominant (η t) := by
    intro t
    induction t using Fin.induction with
    | zero => exact IsDominant.of_comp_of_isOpenImmersion (η 0) e₀.hom.left
    | succ j ih =>
      letI := ih
      exact s2v_i2a_retained_field_lift_dominant (B j.succ) (B j.castSucc)
        (b j) _ (hcenters j) (hblowup j) (η j.castSucc) (η j.succ) (hη j)
  haveI : IsDominant (η 0) := hdom 0
  let Lfixed := s2e_step1_fixedField W₀.left Unit (fun _ => d₀.left)
  haveI : IsDominant (Spec.map (CommRingCat.ofHom Lfixed.subtype) ≫ θfixed) := by
    rw [hθfixed]
    infer_instance
  haveI : IsDominant θfixed := IsDominant.of_comp
    (Spec.map (CommRingCat.ofHom Lfixed.subtype)) θfixed
  have hpreFixed := s2v_i2a_dominant_field_preimage θfixed Vinit
  have hfixedIntegralCoefficients := s2v_i2a_field_normalization_integral_coefficients
    θfixed Vinit hVinit hpreFixed
  have hηinitTop : ⊤ ≤ (η 0) ⁻¹ᵁ Vinit := by
    rw [s2v_i2a_dominant_field_preimage (η 0) Vinit]
  have hθfixedTop : ⊤ ≤ θfixed ⁻¹ᵁ Vinit := by rw [hpreFixed]
  let φinitial : Γ((B 0).left, Vinit) →+* W₀.left.functionField :=
    ((η 0).appLE Vinit ⊤ hηinitTop ≫ (Scheme.ΓSpecIso W₀.left.functionField).hom).hom
  let φfixed : Γ((B 0).left, Vinit) →+* Lfixed :=
    (θfixed.appLE Vinit ⊤ hθfixedTop ≫ (Scheme.ΓSpecIso (CommRingCat.of Lfixed)).hom).hom
  letI : Algebra Γ((B 0).left, Vinit) W₀.left.functionField := φinitial.toAlgebra
  letI : Algebra Γ((B 0).left, Vinit) Lfixed := φfixed.toAlgebra
  haveI : Algebra.IsAlgebraic Γ((B 0).left, Vinit) W₀.left.functionField :=
    s2v_i2a_open_field_point_algebraic (η 0) Vinit hVinit hηinitTop
  have hφfixedFactor := s2v_i2a_field_point_open_coefficients_factor Lfixed.subtype
    (η 0) θfixed hθfixed Vinit hθfixedTop hηinitTop
  let κfixed : Lfixed →ₐ[Γ((B 0).left, Vinit)] W₀.left.functionField :=
    { Lfixed.subtype with commutes' r := congrArg (fun f : Γ((B 0).left, Vinit) →+* W₀.left.functionField => f r) hφfixedFactor }
  haveI : Algebra.IsAlgebraic Γ((B 0).left, Vinit) Lfixed :=
    Algebra.IsAlgebraic.of_injective κfixed Subtype.val_injective
  have hφfixedInjective := s2v_i2a_open_field_point_coefficient_injective θfixed Vinit hθfixedTop
  haveI : FaithfulSMul Γ((B 0).left, Vinit) Lfixed :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hφfixedInjective
  haveI : IsDomain Γ((B 0).left, Vinit) := IsDomain.of_faithfulSMul _ Lfixed
  have hfixedSurjective : Function.Surjective
      (algebraMap Γ((B 0).left, Vinit) (integralClosure Γ((B 0).left, Vinit) Lfixed)) := by
    change Function.Surjective
      (algebraMap Γ((B 0).left, Vinit) (integralClosure Γ((B 0).left, Vinit) Lfixed))
        at hfixedIntegralCoefficients
    exact hfixedIntegralCoefficients
  haveI : IsFractionRing Γ((B 0).left, Vinit) Lfixed :=
    s2v_i2a_fraction_field_of_integral_coefficients hφfixedInjective hfixedSurjective
  haveI : IsScalarTower Γ((B 0).left, Vinit) Lfixed W₀.left.functionField :=
    IsScalarTower.of_algebraMap_eq' hφfixedFactor.symm
  have hηinitialQuasiFinite : ((η 0).appLE Vinit ⊤ hηinitTop).hom.QuasiFinite :=
    LocallyQuasiFinite.quasiFinite_appLE hVinit (isAffineOpen_top _) hηinitTop
  have hΓinitialFinite : (Scheme.ΓSpecIso W₀.left.functionField).hom.hom.Finite :=
    RingHom.Finite.of_surjective _
      (Scheme.ΓSpecIso W₀.left.functionField).commRingCatIsoToRingEquiv.surjective
  haveI : Algebra.QuasiFinite Γ((B 0).left, Vinit) W₀.left.functionField :=
    (RingHom.QuasiFinite.of_finite hΓinitialFinite).comp hηinitialQuasiFinite
  haveI : Algebra.QuasiFinite Lfixed W₀.left.functionField :=
    .of_restrictScalars Γ((B 0).left, Vinit) _ _
  haveI : Module.Finite Lfixed W₀.left.functionField := Module.Finite.of_quasiFinite
  have hδrational := s2v_i2a_field_deck_eq_rational_pullback W₀.left d₀.left
    δ.commRingCatIsoToRingEquiv hδ
  let δL : W₀.left.functionField ≃ₐ[Lfixed] W₀.left.functionField :=
    { δ.commRingCatIsoToRingEquiv with
      commutes' z := by
        have H := (s2e_step1_mem_fixedField W₀.left Unit (fun _ => d₀.left) z.val).mp z.property ()
        change δ.commRingCatIsoToRingEquiv.toRingHom z.val = z.val
        rw [hδrational]
        exact H }
  have hδLfixed (z : W₀.left.functionField) (hz : δL z = z) :
      z ∈ Set.range (algebraMap Lfixed W₀.left.functionField) := by
    refine ⟨⟨z, ?_⟩, rfl⟩
    rw [s2e_step1_mem_fixedField]
    intro u
    rw [← hδrational]
    exact hz
  obtain ⟨hGaloisInitial, hCyclicInitial⟩ := s2v_i2a_cyclic_galois_of_fixed_elements δL hδLfixed
  letI : IsGalois Lfixed W₀.left.functionField := hGaloisInitial
  have hδLorder : orderOf δL = S.m := by
    let forget : (W₀.left.functionField ≃ₐ[Lfixed] W₀.left.functionField) →*
        (W₀.left.functionField ≃+* W₀.left.functionField) :=
      { toFun := AlgEquiv.toRingEquiv
        map_one' := rfl
        map_mul' _ _ := rfl }
    have H := orderOf_injective forget AlgEquiv.toRingEquiv_injective δL
    have hring : δL.toRingEquiv = δ.commRingCatIsoToRingEquiv := by ext z; rfl
    change orderOf δL.toRingEquiv = orderOf δL at H
    rw [hring] at H
    exact H.symm.trans hδfullorder
  letI : Algebra ℂ Γ((B 0).left, Vinit) := overSpecAlgebra (B 0) Vinit
  obtain ⟨rotationSign, hrotationSign, hcomparison⟩ :=
    s2v_l1b_rotation_action_comparison S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj
      p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch
  obtain ⟨vinitial, ainitial, hvinitialNonzero, hvinitialIntegral,
      hvinitialEigen, hvinitialPower, hvinitialField⟩ :=
    s2v_i2a_signed_affine_kummer_generator (R := Γ((B 0).left, Vinit)) (F := Lfixed)
      S.m (by have := S.three_le; omega) rotationSign hrotationSign δL hδLorder hCyclicInitial
  have hstepFields (j : Fin r) := s2v_n2a_functionField_iso S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder j
  have hκstageExists (t : Fin (r + 1)) :
      ∃ κ : (B t).left.functionField →+* W₀.left.functionField,
        Spec.map (CommRingCat.ofHom κ) ≫ (B t).left.fromSpecStalk (genericPoint (B t).left) = η t := by
    letI := hdom t
    exact (s2v_i2a_dominant_field_point_generic_factor (B t).left (η t)).exists
  choose κstage hκstage using hκstageExists
  have hκstageRangeStep (j : Fin r) : Set.range (κstage j.succ) = Set.range (κstage j.castSucc) := by
    obtain ⟨hg, E, hE, hEcoeff⟩ := hstepFields j
    have hEsquare : Spec.map E.hom ≫ (B j.castSucc).left.fromSpecStalk
        (genericPoint (B j.castSucc).left) =
          (B j.succ).left.fromSpecStalk (genericPoint (B j.succ).left) ≫ (b j).left := by
      rw [hE]
      exact s2v_i2a_generic_stalk_map_square (b j).left hg
    have H := s2v_i2a_generic_field_embeddings_comp (b j).left (η j.succ) (η j.castSucc)
      (hη j) (κstage j.succ) (κstage j.castSucc) (hκstage j.succ) (hκstage j.castSucc) E hEsquare
    have hsurj : Function.Surjective E.hom.hom := E.commRingCatIsoToRingEquiv.surjective
    calc
      Set.range (κstage j.succ) = Set.range ((κstage j.succ).comp E.hom.hom) := by
        change Set.range (κstage j.succ) = Set.range (κstage j.succ ∘ E.hom.hom)
        rw [Set.range_comp, Set.range_eq_univ.mpr hsurj, Set.image_univ]
      _ = Set.range (κstage j.castSucc) := by rw [H]
  have hκstageRange : ∀ t, Set.range (κstage t) = Set.range (κstage 0) := by
    intro t
    induction t using Fin.induction with
    | zero => rfl
    | succ j ih => exact (hκstageRangeStep j).trans ih
  have hκstageFieldRange (t : Fin (r + 1)) : (κstage t).fieldRange = (κstage 0).fieldRange := by
    apply SetLike.coe_injective
    simpa only [RingHom.coe_fieldRange] using hκstageRange t
  have hκinitialFieldRange : (κstage 0).fieldRange = Subfield.closure (Set.range φinitial) := by
    exact s2v_i2a_generic_field_range_eq_coefficient_closure (B 0).left (η 0) (κstage 0)
      (hκstage 0) Vinit hVinit hηinitTop
  have hvinitialGenericField (t : Fin (r + 1)) :
      Subfield.closure (Set.range (κstage t) ∪ {vinitial}) = ⊤ := by
    rw [hκstageRange t, Subfield.closure_union, ← RingHom.coe_fieldRange (κstage 0),
      Subfield.closure_eq, hκinitialFieldRange, ← Subfield.closure_union]
    exact hvinitialField
  have hηbase : η 0 ≫ (B 0).hom =
      W₀.left.fromSpecStalk (genericPoint W₀.left) ≫ W₀.hom := by
    calc
      η 0 ≫ (B 0).hom = η 0 ≫ e₀.hom.left ≫ B₀.hom := by rw [e₀.hom.w]
      _ = _ := by rw [← Category.assoc, hη₀, Category.assoc, β₀.w]
  have hvinitialCharacter : δ.commRingCatIsoToRingEquiv vinitial =
      ((Scheme.ΓSpecIso ↧ℂ).inv ≫ W₀.hom.appTop ≫ W₀.left.germToFunctionField ⊤).hom
        (Complex.exp ((rotationSign : ℂ) * (2 * Real.pi * Complex.I) / (S.m : ℂ))) * vinitial := by
    change δL vinitial = _
    rw [hvinitialEigen]
    congr 1
    exact s2v_i2a_original_field_chart_constants (B 0) W₀ (η 0) hηbase
      Vinit hηinitTop _
  obtain ⟨κoriginal, hκoriginal, hOriginalBranchEquation⟩ :=
    s2v_i2a_signed_original_branch_equation S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj
      p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair
      h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator
      rotationSign hrotationSign hcomparison vinitial δ.commRingCatIsoToRingEquiv
      hvinitialNonzero hδ hvinitialCharacter
  letI := hdom s
  obtain ⟨stageMaps, hstageLast, hstageArrows, hstageGeneric, hstageWeighted⟩ :=
    s2v_i2a_all_stage_weighted_transform S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj
      p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair
      h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator
      B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric
      w hw d hd hdinit hdw horder s
  letI : IsAffine U.left := hU
  letI : IsOpenImmersion u.left := hu
  obtain ⟨p, hp⟩ := hxU
  haveI : Nonempty U.left := ⟨p.underlying⟩
  haveI : IsIntegral U.left := isIntegral_of_isOpenImmersion u.left
  haveI : IsDominant (ηU ≫ u.left) := by rw [hηU]; infer_instance
  haveI : IsDominant ηU := IsDominant.of_comp_of_isOpenImmersion ηU u.left
  obtain ⟨κU, hκU, hκUunique⟩ := s2v_i2a_dominant_field_point_generic_factor U.left ηU
  obtain ⟨EU, hEU⟩ := s2v_i2a_open_immersion_generic_field_iso u.left
  have hκUcomp := s2v_i2a_generic_field_embeddings_comp u.left ηU (η s) hηU
    κU (κstage s) hκU (hκstage s) EU hEU
  have hκUFieldRange : κU.fieldRange = (κstage s).fieldRange := by
    apply SetLike.coe_injective
    change Set.range κU = Set.range (κstage s)
    rw [← hκUcomp]
    change Set.range κU = Set.range (κU ∘ EU.hom.hom)
    have hsurj : Function.Surjective EU.hom.hom := EU.commRingCatIsoToRingEquiv.surjective
    rw [Set.range_comp, Set.range_eq_univ.mpr hsurj, Set.image_univ]
  have hgenU : Subfield.closure (Set.range κU ∪ {vinitial}) = ⊤ := by
    rw [Subfield.closure_union, ← RingHom.coe_fieldRange κU, Subfield.closure_eq,
      hκUFieldRange]
    simpa only [Subfield.closure_union, ← RingHom.coe_fieldRange,
      Subfield.closure_eq] using hvinitialGenericField s
  have hstageZero : η s ≫ (stageMaps 0).left = η 0 := by
    simpa only [Fin.val_zero, Fin.mk_zero] using hstageGeneric 0
  let f : U ⟶ B₀ := u ≫ stageMaps 0 ≫ e₀.hom
  have hsq : Spec.map (CommRingCat.ofHom κU) ≫ U.left.fromSpecStalk
      (genericPoint U.left) ≫ f.left =
      Spec.map κoriginal ≫ B₀.left.fromSpecStalk (genericPoint B₀.left) := by
    change Spec.map (CommRingCat.ofHom κU) ≫ U.left.fromSpecStalk _ ≫
      u.left ≫ (stageMaps 0).left ≫ e₀.hom.left = _
    rw [← Category.assoc, hκU, ← Category.assoc, hηU,
      ← Category.assoc, hstageZero, hη₀, hκoriginal]
  let center (j : Fin s.val) :=
    D ⟨j.val, by omega⟩ ⟨2 * j.val, by omega⟩ ⊔
      D ⟨j.val, by omega⟩ ⟨2 * j.val + 1, by omega⟩
  let nextMap (j : Fin s.val) : U.left ⟶ (B ⟨j.val + 1, by omega⟩).left :=
    (u ≫ stageMaps j.succ).left
  have hnextGeneric (j : Fin s.val) : ηU ≫ nextMap j = η ⟨j.val + 1, by omega⟩ := by
    change ηU ≫ u.left ≫ (stageMaps j.succ).left = _
    rw [← Category.assoc, hηU, hstageGeneric]
    rfl
  have hnextDom : ∀ j, IsDominant (nextMap j) := fun j => by
    haveI : IsDominant (ηU ≫ nextMap j) := by rw [hnextGeneric]; exact hdom _
    exact IsDominant.of_comp ηU (nextMap j)
  let E : U.left.IdealSheafData := ∏ j : Fin s.val,
    ((center j).comap (b ⟨j.val, by omega⟩).left).comap (nextMap j)
  have hE : E = (∏ j : Fin s.val,
      (center j).comap (stageMaps j.castSucc).left).comap u.left := by
    rw [s2v_l1b_comap_prod]
    apply Finset.prod_congr rfl
    intro j _
    change ((center j).comap (b ⟨j.val, by omega⟩).left).comap
      (u.left ≫ (stageMaps j.succ).left) = _
    rw [← Scheme.IdealSheafData.comap_comp, Category.assoc,
      ← Over.comp_left, hstageArrows, Scheme.IdealSheafData.comap_comp]
  let D' := fun t => (D s t).comap u.left
  let I := fun t => s2c_branchIdeal Z B₀ h γ (Point.map p₀ (eY (y (σ t))))
  let n := fun t => (g32p_exponents S)[σ t]
  have hweighted : (∏ t, (I t) ^ n t).comap f.left =
      (∏ t, (D' t) ^ n t) * E ^ S.m := by
    rw [hE]
    have H := congrArg (fun A => A.comap u.left) hstageWeighted
    simp only [s2v_l1b_comap_mul, s2v_l1b_comap_pow, s2v_l1b_comap_prod] at H ⊢
    simp only [Fin.val_zero, Fin.mk_zero] at H
    convert H using 1
    apply Finset.prod_congr rfl
    intro t _
    rw [hD₀]
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp]
    rfl
  obtain ⟨e, he_ne, he⟩ := @s2v_i2a_cartier_product_germ_generator U.left inferInstance (Fin s.val) inferInstance
    (fun j : Fin s.val => (B ⟨j.val + 1, by omega⟩).left) (fun j => inferInstance) nextMap hnextDom
    (fun j => (center j).comap (b ⟨j.val, by omega⟩).left) p.underlying
    (fun j => hcartier ⟨j.val, by omega⟩ (nextMap j p.underlying))
    ⟨⊤, isAffineOpen_top _⟩ (by trivial)
  obtain ⟨O, hpO, g, ε₀, A, B₁, hA, hB₁, hg, heq⟩ :=
    hOriginalBranchEquation (Point.map f p)
  have hstalkgen : Subfield.closure
      (Set.range (s2v_l1b_kval_stalkMap U.left p.underlying (CommRingCat.ofHom κU)) ∪
        {vinitial}) = ⊤ := by
    rw [s2v_l1b_stalk_section_generated_subfield U.left p.underlying ηU
      (CommRingCat.ofHom κU) hκU ⟨⊤, isAffineOpen_top _⟩ le_top le_top vinitial]
    have hcoeff := s2v_i2a_generic_field_range_eq_coefficient_closure U.left ηU κU hκU
      ⊤ (isAffineOpen_top _) le_top
    rw [Subfield.closure_union, ← hcoeff]
    simpa only [Subfield.closure_union, ← RingHom.coe_fieldRange,
      Subfield.closure_eq] using hgenU
  obtain ⟨v, V, hV, k, ηV, cV, zV, ε, hk, hpV, hηV, hcV, hzV,
      hcVEt, hcVscalar, hlabels, habsentV, hidealV, hunit, hpower, hfield⟩ :=
    s2v_i2a_weighted_pullback_chart_assembly U p ηU (CommRingCat.ofHom κU) hκU
      D' z n hideal (h + 1) c hc hscalar J κ hz habsent f.left κoriginal hsq
      I E S.m hweighted O hpO g hg e he_ne he ε₀ A B₁ hA hB₁ vinitial hstalkgen heq
  refine ⟨V, hV, k, ηV, cV, zV, ε, v, hk, ?_, hηV, hcV, hzV,
    hcVEt, hcVscalar, hlabels, habsentV, ?_, hunit, hpower, hfield⟩
  · obtain ⟨q, hq⟩ := hpV
    refine ⟨q, ?_⟩
    change Point.map u (Point.map k q) = x
    rw [hq, hp]
  · intro t
    rw [Over.comp_left, Scheme.IdealSheafData.comap_comp]
    exact hidealV t

end HodgeLean.Foundations.Program
