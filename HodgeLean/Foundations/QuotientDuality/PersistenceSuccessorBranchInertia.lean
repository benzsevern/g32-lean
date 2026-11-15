import HodgeLean.Foundations.Program.SchoenTowerI2bProofs

/-! Actual branch exponent inertia at every retained normalization stage. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedVariables false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Adapters HodgeLean.Foundations.Program
open scoped BigOperators Manifold ContDiff OnePoint
namespace HodgeLean.Foundations.QuotientDuality

theorem persistence_retained_successor_branch_inertia
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
    (t : Fin (2 * r))
    (xW : ComplexPoint (s2b_normalizationOver (B i.succ) (η i.succ)))
    (hsupport : (Point.map (s2b_normalizationMap (B i.succ) (η i.succ)) xW).underlying ∈
      (D i.succ t).support) :
    (Point.map (d i.succ))^[(g32p_exponents S)[σ t]] xW = xW := by
  classical
  let β := s2b_normalizationMap (B i.succ) (η i.succ)
  let xB := Point.map β xW
  have hupperSupport : xB.left (IsLocalRing.closedPoint ℂ) ∈ (D i.succ t).support := hsupport
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
  exact hfixW

end HodgeLean.Foundations.QuotientDuality
