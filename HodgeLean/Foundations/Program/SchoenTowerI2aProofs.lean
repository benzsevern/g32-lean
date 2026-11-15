import HodgeLean.Foundations.AlgebraicGeometry.TameMonomialCover
import HodgeLean.Foundations.Program.SchoenTowerI2aChartSplit
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
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

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
theorem s2v_i2a_original_field_chart_aux
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
                (integralClosure Γ(U.left, ⊤) W₀.left.functionField))) := by
  obtain ⟨U, hU, u, ηU, hu, hxU, hηU, c, J, κ, z,
    hc, hscalar, hJ, hz, habsent, hideal, hNormalization⟩ :=
    s2v_i2a_strict_transform_parameters S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder i s x
  obtain ⟨V, hV, k, ηV, cV, zV, ε, v, hk, hxV, hηV,
    hcVpull, hzVpull, hcV, hscalarV, hzV, habsentV, hidealV, hε, hv, hgen⟩ :=
    s2v_i2a_branch_monomial_coefficient S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder i s x
      U hU u ηU hu hxU hηU c J κ z hc hscalar hJ hz habsent hideal
  letI : IsOpenImmersion u.left := hu
  letI : IsOpenImmersion k.left := hk
  have hηComposite : ηV ≫ (k ≫ u).left = η s := by
    change ηV ≫ (k.left ≫ u.left) = η s
    rw [← Category.assoc, hηV, hηU]
  refine ⟨V, hV, k ≫ u, ηV,
    inferInstanceAs (IsOpenImmersion (k.left ≫ u.left)), hxV, hηComposite,
    cV, J, κ, zV, ε, v, hcV, hscalarV, hJ, hzV, habsentV, hidealV,
    hε, hv, hgen, ?_⟩
  exact hNormalization V hV k ηV hk hηV

/-- Dividing the generic generator by the exceptional coordinate retains every unpaired exponent on both charts.
Source: Schoen (1988), Lemmas 2.4–2.5, printed pp. 14–15, exceptional multiplicity m. -/
theorem s2v_i2a_blowup_exponents_aux
    (K : Type*) [Field K] (n m a b : ℕ) (hm : 0 < m)
    (hab : a + b = m) (α : Fin n → ℕ)
    (ε t x y : K) (z : Fin n → K) (hx : x ≠ 0) (hy : y ≠ 0)
    (ht : t ^ m = ε * x ^ a * y ^ b * ∏ j, z j ^ α j) :
    (t / x) ^ m = ε * (y / x) ^ b * ∏ j, z j ^ α j ∧
    (t / y) ^ m = ε * (x / y) ^ a * ∏ j, z j ^ α j := by
  exact TameMonomialCover.pair_rescaling K n m a b hm hab α ε t x y z hx hy ht

/-- Each vanishing coordinate contributes its exponent subgroup to pointwise inertia in the integral closure.
Source: Schoen (1988), Lemma 2.5, printed p. 15, and Sublemma 2.9, printed p. 19; G32 v0.16, Lemma 4.3, prime-free monomial inertia. -/
theorem s2v_i2a_normalized_monomial_inertia_aux
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
          simpa only [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply] using H.symm } := by
  let q : R := ε * ∏ k, (c (MvPolynomial.X k)) ^ α k
  have hvq : v ^ m = algebraMap R K q := by
    simpa only [q, map_mul, map_prod, map_pow] using hv
  have hvne : v ≠ 0 :=
    s2v_i2a_etale_monomial_generator_ne_zero hinj n m hm c hc α ε hε v hv
  have hζR : IsPrimitiveRoot (algebraMap ℂ R ζ) m :=
    hζ.map_of_injective (algebraMap ℂ R).injective
  have hBinomial : Irreducible ((Polynomial.X : Polynomial R) ^ m - Polynomial.C q) :=
    s2v_i2a_binomial_irreducible hinj m hm (algebraMap ℂ R ζ) hζR d v hvne
      (by rw [← IsScalarTower.algebraMap_apply ℂ R K]; exact hd) q hvq
  have hperiod : d ^ m = 1 := s2v_i2a_aut_pow_eq_one v hgen d
    (algebraMap ℂ R ζ) (by rw [← IsScalarTower.algebraMap_apply ℂ R K]; exact hd)
    m (by rw [← map_pow, hζ.pow_eq_one, map_one])
  have hperiodN : d.mapIntegralClosure ^ m = 1 :=
    s2v_i2a_integralClosure_pow_eq_one d m hperiod
  by_cases hdiv : m ∣ α j
  · obtain ⟨k, hk⟩ := hdiv
    rw [hk, pow_mul, hperiodN, one_pow]
    exact Subgroup.zpowers_le.mpr (Subgroup.one_mem _)
  · have hα : α j ≠ 0 := by
      intro hz
      apply hdiv
      rw [hz]
      exact dvd_zero m
    have hpq : p (algebraMap R (integralClosure R K) q) = 0 := by
      let f : R →+* ℂ := p.toRingHom.comp (algebraMap R (integralClosure R K))
      change f (ε * ∏ k, (c (MvPolynomial.X k)) ^ α k) = 0
      rw [map_mul, map_prod]
      have hprod : ∏ k, f ((c (MvPolynomial.X k)) ^ α k) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ j)
        rw [map_pow, show f (c (MvPolynomial.X j)) = 0 from hp, zero_pow hα]
      rw [hprod, mul_zero]
    have hvResidue := s2v_i2a_binomial_residue_zero m hm q v hvq p.toRingHom hpq
    obtain ⟨wroot, uroot, hwint, huint, pLift, hwroot, huroot, hvroot, hpLift⟩ :=
      s2v_i2a_etale_integral_root_choices n m hm R K c hc hinj α ε v hv p
    let f : K →ₐ[R] AlgebraicClosure K := IsScalarTower.toAlgHom R K (AlgebraicClosure K)
    have hpLiftBase : pLift (algebraMap R (integralClosure R (AlgebraicClosure K))
        (c (MvPolynomial.X j))) = 0 := by
      rw [← f.mapIntegralClosure.commutes (c (MvPolynomial.X j))]
      exact (hpLift _).trans hp
    have hwResidue : pLift ⟨wroot j, hwint j⟩ = 0 :=
      s2v_i2a_binomial_residue_zero m hm (c (MvPolynomial.X j)) (wroot j) (hwroot j)
        pLift.toRingHom hpLiftBase
    have hRootIntegral := s2v_i2a_root_adjoin_integral wroot uroot hwint huint
    obtain ⟨qRoot, hqRoots, hqUnit⟩ :=
      s2v_i2a_root_adjoin_evaluation wroot uroot hwint huint pLift
    have hqRootZero : qRoot ⟨wroot j, Algebra.subset_adjoin (Or.inl ⟨j, rfl⟩)⟩ = 0 :=
      (hqRoots j).trans hwResidue
    have hinjL : Function.Injective (algebraMap R (AlgebraicClosure K)) := by
      intro x y hxy
      apply hinj
      apply (algebraMap K (AlgebraicClosure K)).injective
      simpa only [← IsScalarTower.algebraMap_apply R K (AlgebraicClosure K)] using hxy
    obtain ⟨A, hA, hdom, hnormal, i, σ, qA, W, U, G,
      hσinj, hσi, hσW, hσU, hGi, hGW, hGU, hqG, hvalue⟩ :=
      s2v_i2a_pointed_normal_root_cover n m hm R (AlgebraicClosure K) c hc hinjL ε hε
        wroot hwroot hwint uroot huroot pLift.toRingHom j hwResidue ζ hζ
    letI := hA
    letI : IsDomain A := hdom
    letI : IsIntegrallyClosed A := hnormal
    letI : Algebra R A := i.toAlgebra
    let σA : A →ₐ[R] AlgebraicClosure K := { σ with commutes' := RingHom.congr_fun hσi }
    let GA : A ≃ₐ[R] A := { G with commutes' := hGi }
    let V : A := U * ∏ k, W k ^ α k
    have hV : σA V = f v := by
      change σ (U * ∏ k, W k ^ α k) = f v
      rw [map_mul, map_prod]
      simp_rw [map_pow, hσW]
      rw [hσU]
      exact hvroot.symm
    let z : R := algebraMap ℂ R ζ
    have hGW' (k : Fin n) : GA (W k) =
        if k = j then algebraMap R A z * W k else W k := by
      change G (W k) = _
      rw [hGW]
      have H : c (MvPolynomial.C ζ) = z := c.commutes ζ
      rw [H]
      rfl
    have hGV : GA V = algebraMap R A (z ^ α j) * V :=
      s2v_i2a_monomial_rotation n W U α j z GA hGW' hGU
    have hdz : d v = algebraMap R K z * v := by
      rw [← IsScalarTower.algebraMap_apply ℂ R K]
      exact hd
    have hdPower : (d ^ α j) v = algebraMap R K (z ^ α j) * v := by
      rw [map_pow]
      exact s2v_i2a_aut_pow_generator d v z hdz (α j)
    have hfixed := s2v_i2a_normal_generator_inertia v hgen f σA hσinj V hV
      (z ^ α j) (d ^ α j) hdPower GA hGV p.toRingHom qA
      (fun a => RingHom.congr_fun hqG a) (by
        intro a b hab
        exact (hvalue a (f.mapIntegralClosure b) hab).trans (hpLift b))
    apply Subgroup.zpowers_le.mpr
    intro b
    have H : (d.mapIntegralClosure ^ α j) b = (d ^ α j).mapIntegralClosure b :=
      Subtype.ext (s2v_i2a_integralClosure_pow_apply d (α j) b)
    rw [H]
    exact hfixed b

end HodgeLean.Foundations.Program
