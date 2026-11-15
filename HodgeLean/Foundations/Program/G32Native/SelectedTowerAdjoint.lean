import HodgeLean.Foundations.Program.G32Native.SelectedAdjoint
import HodgeLean.Foundations.Program.SchoenCycleC2AbsoluteTransportHelpers

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular HodgeLean.Adapters HodgeLean.RealDefs
open HodgeLean.Foundations.QuotientDuality
open HodgeLean.Foundations.Analytic
open scoped BigOperators Manifold ContDiff OnePoint
namespace HodgeLean.Foundations.Program

/-- Invariance and equivariance give the action equation for the adjoint. -/
theorem g32n_adjoint_deck {V R : Type*} [AddCommGroup V] [Module ℚ V]
    [AddCommGroup R] [Module ℚ R]
    (B₀ : V →ₗ[ℚ] Module.Dual ℚ V) (hB₀ : Function.Bijective B₀)
    (Br : R →ₗ[ℚ] Module.Dual ℚ R) (f : V →ₗ[ℚ] R)
    (D₀ : V →ₗ[ℚ] V) (Dr : R →ₗ[ℚ] R)
    (hs : Function.Surjective D₀)
    (h₀ : ∀ u v, B₀ (D₀ u) (D₀ v) = B₀ u v)
    (hr : ∀ u v, Br (Dr u) (Dr v) = Br u v)
    (he : ∀ v, Dr (f v) = f (D₀ v)) (u : R) :
    s2e_pairingAdjoint B₀ hB₀ Br f (Dr u) =
      D₀ (s2e_pairingAdjoint B₀ hB₀ Br f u) := by
  apply hB₀.1
  ext v
  obtain ⟨z, rfl⟩ := hs v
  rw [s2e_pairingAdjoint_pair, ← he, hr, h₀, s2e_pairingAdjoint_pair]

variable
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
    (W : Over (Spec ↧ℂ)) [IsIntegral W.left] [IsProjective W.hom]
    (eFinal : s2b_normalizationOver (B (Fin.last r)) (η (Fin.last r)) ≅ W)

include S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder W eFinal


/-- Retain all joint trace witnesses while changing the displayed middle degree. -/
theorem g32n_selected_joint_traces (n : ℕ) (hn : h + 1 = n)
    : ∃ (o : LocalRationalOrientation (TopCat.of (ComplexPoint W)) (2 * n))
      (o₀ : LocalRationalOrientation (TopCat.of (ComplexPoint W₀)) (2 * n))
      (c : Homology ℚ (TopCat.of (ComplexPoint W)) (2 * n))
      (c₀ : Homology ℚ (TopCat.of (ComplexPoint W₀)) (2 * n)),
      (∀ x, localOrientation (TopCat.of (ComplexPoint W)) (2 * n) c x = o.generator x) ∧
      (∀ x, localOrientation (TopCat.of (ComplexPoint W₀)) (2 * n) c₀ x = o₀.generator x) ∧
      (∀ (x : ComplexPoint W)
        (E : OpenPartialHomeomorph (ComplexPoint W) (Fin n → ℂ))
        (hx : x ∈ E.source),
        (∀ j, (f4_analytification W).IsHolFun (fun y : E.source => E y j)) →
        localOrientation (TopCat.of (ComplexPoint W)) (2 * n) c x =
          localClassOfChart n E x hx) ∧ (∀ (x : ComplexPoint W₀)
        (E : OpenPartialHomeomorph (ComplexPoint W₀) (Fin n → ℂ))
        (hx : x ∈ E.source),
        (∀ j, (f4_analytification W₀).IsHolFun (fun y : E.source => E y j)) →
        localOrientation (TopCat.of (ComplexPoint W₀)) (2 * n) c₀ x =
          localClassOfChart n E x hx) ∧
      homologyMap ℚ (2 * n)
        (TopCat.ofHom (Point.continuousMap (eFinal.inv ≫ s2e_towerTotalMap (fun i => s2b_normalizationOver (B i) (η i)) eW.hom w (Fin.last r)))) c = c₀ ∧
      (∀ u, orientationIntegral (TopCat.of (ComplexPoint W)) (2 * n) c
        (cohomologyMap ℚ (2 * n)
          (TopCat.ofHom (Point.continuousMap (eFinal.inv ≫ s2e_towerTotalMap (fun i => s2b_normalizationOver (B i) (η i)) eW.hom w (Fin.last r)))) u) = orientationIntegral (TopCat.of (ComplexPoint W₀)) (2 * n) c₀ u) ∧
      (∀ u, orientationIntegral (TopCat.of (ComplexPoint W)) (2 * n) c
        (cohomologyMap ℚ (2 * n) (TopCat.ofHom (Point.continuousMap (eFinal.inv ≫ d (Fin.last r) ≫ eFinal.hom))) u) =
        orientationIntegral (TopCat.of (ComplexPoint W)) (2 * n) c u) ∧
      (∀ u, orientationIntegral (TopCat.of (ComplexPoint W₀)) (2 * n) c₀
        (cohomologyMap ℚ (2 * n) (TopCat.ofHom (Point.continuousMap d₀)) u) =
        orientationIntegral (TopCat.of (ComplexPoint W₀)) (2 * n) c₀ u) ∧
      (∀ (u v : Cohomology ℚ (TopCat.of (ComplexPoint W)) n),
        orientationIntegral (TopCat.of (ComplexPoint W)) (2 * n) c
          (HodgeLean.Foundations.Singular.cup (TopCat.of (ComplexPoint W)) (by omega)
            (cohomologyMap ℚ n (TopCat.ofHom (Point.continuousMap (eFinal.inv ≫ d (Fin.last r) ≫ eFinal.hom))) u)
            (cohomologyMap ℚ n (TopCat.ofHom (Point.continuousMap (eFinal.inv ≫ d (Fin.last r) ≫ eFinal.hom))) v)) =
        orientationIntegral (TopCat.of (ComplexPoint W)) (2 * n) c
          (HodgeLean.Foundations.Singular.cup (TopCat.of (ComplexPoint W)) (by omega) u v)) ∧
      (∀ (u v : Cohomology ℚ (TopCat.of (ComplexPoint W₀)) n),
        orientationIntegral (TopCat.of (ComplexPoint W₀)) (2 * n) c₀
          (HodgeLean.Foundations.Singular.cup (TopCat.of (ComplexPoint W₀)) (by omega)
            (cohomologyMap ℚ n (TopCat.ofHom (Point.continuousMap d₀)) u)
            (cohomologyMap ℚ n (TopCat.ofHom (Point.continuousMap d₀)) v)) =
        orientationIntegral (TopCat.of (ComplexPoint W₀)) (2 * n) c₀
          (HodgeLean.Foundations.Singular.cup (TopCat.of (ComplexPoint W₀)) (by omega) u v)) := by
  subst n
  exact s2e_chain_deck_trace_pairing S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder W eFinal

/-- The native T17–T18 adjoint for the retained tower and its joint geometric traces. -/
theorem g32n_selected_tower_adjoint (k : ℕ) (hselected : h + 1 = 2 * k)
    (f : ∀ i, s2b_normalizationOver (B i) (η i) ⟶ W₀)
    (hf : f 0 = eW.hom ∧ ∀ i : Fin r, f i.succ = w i ≫ f i.castSucc) :
    let Xr := TopCat.of (ComplexPoint W)
    let X₀ := TopCat.of (ComplexPoint W₀)
    let φ := eFinal.inv ≫ f (Fin.last r)
    let δ := eFinal.inv ≫ d (Fin.last r) ≫ eFinal.hom
    ∃ (trr : Cohomology ℚ Xr (2 * (2 * k)) →ₗ[ℚ] ℚ)
      (tr₀ : Cohomology ℚ X₀ (2 * (2 * k)) →ₗ[ℚ] ℚ),
      Function.Bijective (s2e_middlePairing Xr k trr) ∧
      Function.Bijective (s2e_middlePairing X₀ k tr₀) ∧
      ∃ G : Cohomology ℚ Xr (2 * k) →ₗ[ℚ] Cohomology ℚ X₀ (2 * k),
        (∀ u v, s2e_middlePairing X₀ k tr₀ (G u) v =
          s2e_middlePairing Xr k trr u (s2e_pullback ℚ φ (2 * k) v)) ∧
        (∀ v, G (s2e_pullback ℚ φ (2 * k) v) = v) ∧
        (∀ v, G (s2e_pullback ℚ δ (2 * k) v) =
          s2e_pullback ℚ d₀ (2 * k) (G v)) := by
  dsimp only
  have hfu := s2e_towerTotalMap_unique _ eW.hom w f hf.1 hf.2
  have hequiv := s2e_towerTotalMap_equivariant _ eW.hom w d d₀ hdinit hdw (Fin.last r)
  have hsquare : (eFinal.inv ≫ d (Fin.last r) ≫ eFinal.hom) ≫
      (eFinal.inv ≫ f (Fin.last r)) = (eFinal.inv ≫ f (Fin.last r)) ≫ d₀ := by
    simp only [Category.assoc, eFinal.hom_inv_id_assoc]
    rw [hfu, hequiv]
  have hjoint := g32n_selected_joint_traces S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder W eFinal (2 * k) hselected
  obtain ⟨o, o₀, c, c₀, hc, hc₀, hchart, hchart₀, hdegree, htrace, ht, ht₀, hp, hp₀⟩ := hjoint
  have hk : 0 < 2 * k := by omega
  have hperf := g32n_projective_middle_perfect W k hk o c hc
  have hperf₀ := g32n_projective_middle_perfect W₀ k hk o₀ c₀ hc₀
  let trr := orientationIntegral (TopCat.of (ComplexPoint W)) (2 * (2 * k)) c
  let tr₀ := orientationIntegral (TopCat.of (ComplexPoint W₀)) (2 * (2 * k)) c₀
  let F := s2e_pullback ℚ (eFinal.inv ≫ f (Fin.last r)) (2 * k)
  let Br := s2e_middlePairing (TopCat.of (ComplexPoint W)) k trr
  let Bzero := s2e_middlePairing (TopCat.of (ComplexPoint W₀)) k tr₀
  refine ⟨trr, tr₀, hperf, hperf₀, s2e_pairingAdjoint Bzero hperf₀ Br F, ?_, ?_, ?_⟩
  · exact s2e_pairingAdjoint_pair Bzero hperf₀ Br F
  · apply s2e_pairingAdjoint_retraction
    intro u v
    change trr (HodgeLean.Foundations.Singular.cup _ _ (F u) (F v)) =
      tr₀ (HodgeLean.Foundations.Singular.cup _ _ u v)
    dsimp only [trr, tr₀, F, s2e_pullback]
    rw [← HodgeLean.Foundations.Singular.cohomologyMap_cup]
    rw [hfu]
    exact htrace _
  · intro u
    have hm : S.m ≠ 0 := by have := S.three_le; omega
    haveI : IsIso (d 0) := (isUnit_iff_isIso _).mp (IsUnit.of_pow_eq_one (horder 0) hm)
    have he : d₀ = eW.inv ≫ d 0 ≫ eW.hom := by rw [hdinit, eW.inv_hom_id_assoc]
    haveI : IsIso d₀ := by rw [he]; infer_instance
    apply g32n_adjoint_deck Bzero hperf₀ Br F (s2e_pullback ℚ d₀ (2 * k))
      (s2e_pullback ℚ (eFinal.inv ≫ d (Fin.last r) ≫ eFinal.hom) (2 * k))
    · intro v
      refine ⟨s2e_pullback ℚ (inv d₀) (2 * k) v, ?_⟩
      have h := congrArg (fun L => L v) (s2e_quotient_pullback_comp d₀ (inv d₀) (2 * k))
      rw [IsIso.hom_inv_id, s2e_pullback_id] at h
      exact h.symm
    · exact hp₀
    · exact hp
    · intro v
      have h := congrArg (fun g => s2e_pullback ℚ g (2 * k) v) hsquare
      simpa only [F, s2e_quotient_pullback_comp, LinearMap.comp_apply] using h

end HodgeLean.Foundations.Program
