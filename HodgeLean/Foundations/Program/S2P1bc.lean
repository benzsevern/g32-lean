import HodgeLean.Foundations.QuotientDuality.RetainedLocalTrace
import HodgeLean.Foundations.QuotientDuality.RetainedTraceChecks

/-! # S2 P1b and P1c retained applications

The maps and normalizations are those of M8 stage 6.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular HodgeLean.Adapters HodgeLean.RealDefs
open HodgeLean.Foundations.Program
open HodgeLean.Foundations.Analytic
open scoped BigOperators Manifold ContDiff OnePoint
namespace HodgeLean.Foundations.QuotientDuality

private theorem compact_scheme_orientation_unique
    (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] [CompactSpace (ComplexPoint X)] (n : ℕ)
    (o : LocalRationalOrientation (TopCat.of (ComplexPoint X)) n)
    (c d : Homology ℚ (TopCat.of (ComplexPoint X)) n)
    (hc : ∀ x, localOrientation _ n c x = o.generator x)
    (hd : ∀ x, localOrientation _ n d x = o.generator x) : c = d := by
  letI : T2Space (ComplexPoint X) := f4_t2Space X
  obtain ⟨N, hN⟩ := compact_complex_open_homology_bound X
  have hdet := compact_detection_of_uniform_bound (TopCat.of (ComplexPoint X)) n (N + 1)
    (fun x i hi => o.vanishes x i (by omega))
    (fun A hA i hi => open_homology_compact_support_bound
      (TopCat.of (ComplexPoint X)) N hN A hA i hi)
  obtain ⟨z, hz, hu⟩ := fundamental_class_of_compact_detection
    (TopCat.of (ComplexPoint X)) n o hdet
  exact (hu c hc).trans (hu d hd).symm

private theorem scheme_deck_trace
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [CompactSpace (ComplexPoint X)]
    (d : ℕ) (o : LocalRationalOrientation (TopCat.of (ComplexPoint X)) (2 * d))
    (c : Homology ℚ (TopCat.of (ComplexPoint X)) (2 * d))
    (hc : ∀ x, localOrientation _ (2 * d) c x = o.generator x)
    (hnorm : ∀ (x : ComplexPoint X)
      (E : OpenPartialHomeomorph (ComplexPoint X) (Fin d → ℂ)) (hx : x ∈ E.source),
      (∀ i, (f4_analytification X).IsHolFun (fun y : E.source => E y i)) →
      localOrientation _ (2 * d) c x = localClassOfChart d E x hx)
    (f : X ⟶ X) (m : ℕ) (hm : 0 < m) (hpow : End.of f ^ m = 1) :
    ∀ u, orientationIntegral (TopCat.of (ComplexPoint X)) (2 * d) c
      (cohomologyMap ℚ (2 * d) (TopCat.ofHom (Point.continuousMap f)) u) =
      orientationIntegral (TopCat.of (ComplexPoint X)) (2 * d) c u := by
  obtain ⟨H, hH, hpres⟩ := finite_order_preserves_normalized_orientation
    X d o c hc (fun x E hx hh => (hc x).symm.trans (hnorm x E hx hh)) f m hm hpow
  have hmap : TopCat.ofHom (Point.continuousMap f) =
      TopCat.ofHom ⟨H, H.continuous⟩ := by
    apply TopCat.ext
    intro x
    exact (hH x).symm
  have hfix : homologyMap ℚ (2 * d) (TopCat.ofHom (Point.continuousMap f)) c = c := by
    apply compact_scheme_orientation_unique X (2 * d) o _ c ?_ hc
    intro y
    obtain ⟨x, rfl⟩ := H.surjective y
    rw [hmap]
    have hn := localOrientation_map
      (X := TopCat.of (ComplexPoint X)) (Y := TopCat.of (ComplexPoint X))
      (2 * d) x (H x) (pointComplementHomeomorphPairMap H x) c
    change relativeHomologyMap ℚ (2 * d) (pointComplementHomeomorphPairMap H x)
      (localOrientation (TopCat.of (ComplexPoint X)) (2 * d) c x) =
      localOrientation (TopCat.of (ComplexPoint X)) (2 * d)
        (homologyMap ℚ (2 * d) (TopCat.ofHom ⟨H, H.continuous⟩) c) (H x) at hn
    rw [hc x] at hn
    exact hn.symm.trans (hpres x)
  intro u
  change cohomologyEquivDualHomology ℚ _ _ (cohomologyMap ℚ _ _ u) c = _
  rw [cohomologyEquivDualHomology_cohomologyMap, hfix]
  rfl

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


/-- Retained application for the S2 rational duality contract.
Source: docs/notes/native-inputs/s2e-chain-contract.md:649–668;
QuotientDuality/RetainedLocalTrace.lean, `retained_initial_normalized_trace`.
HC no distance; AV milestone no distance. -/
theorem s2e_chain_quotient_trace_initial
    : ∃ (o : LocalRationalOrientation (TopCat.of (ComplexPoint W₀)) (2 * (h + 1)))
      (c : Homology ℚ (TopCat.of (ComplexPoint W₀)) (2 * (h + 1))),
      (∀ x, localOrientation (TopCat.of (ComplexPoint W₀)) (2 * (h + 1)) c x = o.generator x) ∧
      (∀ (x : ComplexPoint W₀)
        (E : OpenPartialHomeomorph (ComplexPoint W₀) (Fin (h + 1) → ℂ))
        (hx : x ∈ E.source),
        (∀ j, (f4_analytification W₀).IsHolFun (fun y : E.source => E y j)) →
        localOrientation (TopCat.of (ComplexPoint W₀)) (2 * (h + 1)) c x =
          localClassOfChart (h + 1) E x hx) ∧
      ∀ (x : ComplexPoint W₀) (v : RelativeCohomology ℚ (pointComplementPair x) (2 * (h + 1))),
        relativeCohomologyEquivDualHomology ℚ (pointComplementPair x) (2 * (h + 1)) v (o.generator x) = (1 : ℚ) →
        orientationIntegral (TopCat.of (ComplexPoint W₀)) (2 * (h + 1)) c (relativeCohomologyToAbsolute ℚ (pointComplementPair x) (2 * (h + 1)) v) = (1 : ℚ) :=
  retained_initial_normalized_trace S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder W eFinal

example := RetainedTraceChecks.retained_normalized_trace_model

/-- Retained application for the S2 rational duality contract.
Source: docs/notes/native-inputs/s2e-chain-contract.md:649–668;
QuotientDuality/RetainedLocalTrace.lean, `retained_final_normalized_trace`.
HC no distance; AV milestone no distance. -/
theorem s2e_chain_quotient_trace
    : ∃ (o : LocalRationalOrientation (TopCat.of (ComplexPoint W)) (2 * (h + 1)))
      (c : Homology ℚ (TopCat.of (ComplexPoint W)) (2 * (h + 1))),
      (∀ x, localOrientation (TopCat.of (ComplexPoint W)) (2 * (h + 1)) c x = o.generator x) ∧
      (∀ (x : ComplexPoint W)
        (E : OpenPartialHomeomorph (ComplexPoint W) (Fin (h + 1) → ℂ))
        (hx : x ∈ E.source),
        (∀ j, (f4_analytification W).IsHolFun (fun y : E.source => E y j)) →
        localOrientation (TopCat.of (ComplexPoint W)) (2 * (h + 1)) c x =
          localClassOfChart (h + 1) E x hx) ∧
      ∀ (x : ComplexPoint W) (v : RelativeCohomology ℚ (pointComplementPair x) (2 * (h + 1))),
        relativeCohomologyEquivDualHomology ℚ (pointComplementPair x) (2 * (h + 1)) v (o.generator x) = (1 : ℚ) →
        orientationIntegral (TopCat.of (ComplexPoint W)) (2 * (h + 1)) c (relativeCohomologyToAbsolute ℚ (pointComplementPair x) (2 * (h + 1)) v) = (1 : ℚ) :=
  retained_final_normalized_trace S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder W eFinal

example := RetainedTraceChecks.retained_normalized_trace_model

/-- Retained application for the S2 rational duality contract.
Source: docs/notes/native-inputs/s2e-chain-contract.md:649–668;
QuotientDuality/RetainedLocalTrace.lean, `retained_initial_deck_orientation`.
HC no distance; AV milestone no distance. -/
theorem s2e_chain_deck_orientation_initial
    : ∃ (o : LocalRationalOrientation (TopCat.of (ComplexPoint W₀)) (2 * (h + 1)))
      (H : ComplexPoint W₀ ≃ₜ ComplexPoint W₀),
      (∀ x, H x = Point.map (d₀) x) ∧
      (∀ x, relativeHomologyMap ℚ (2 * (h + 1))
        (pointComplementHomeomorphPairMap H x) (o.generator x) = o.generator (H x)) ∧
        (∀ (x : ComplexPoint W₀)
        (E : OpenPartialHomeomorph (ComplexPoint W₀) (Fin (h + 1) → ℂ))
        (hx : x ∈ E.source),
        (∀ j, (f4_analytification W₀).IsHolFun (fun y : E.source => E y j)) →
        o.generator x =
          localClassOfChart (h + 1) E x hx) :=
  retained_initial_deck_orientation S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder W eFinal

example := RetainedTraceChecks.connected_deck_orientation_falsification

/-- Retained application for the S2 rational duality contract.
Source: docs/notes/native-inputs/s2e-chain-contract.md:649–668;
QuotientDuality/RetainedLocalTrace.lean, `retained_final_deck_orientation`.
HC no distance; AV milestone no distance. -/
theorem s2e_chain_deck_orientation
    : ∃ (o : LocalRationalOrientation (TopCat.of (ComplexPoint W)) (2 * (h + 1)))
      (H : ComplexPoint W ≃ₜ ComplexPoint W),
      (∀ x, H x = Point.map (eFinal.inv ≫ d (Fin.last r) ≫ eFinal.hom) x) ∧
      (∀ x, relativeHomologyMap ℚ (2 * (h + 1))
        (pointComplementHomeomorphPairMap H x) (o.generator x) = o.generator (H x)) ∧
        (∀ (x : ComplexPoint W)
        (E : OpenPartialHomeomorph (ComplexPoint W) (Fin (h + 1) → ℂ))
        (hx : x ∈ E.source),
        (∀ j, (f4_analytification W).IsHolFun (fun y : E.source => E y j)) →
        o.generator x =
          localClassOfChart (h + 1) E x hx) :=
  retained_final_deck_orientation S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder W eFinal

example := RetainedTraceChecks.connected_deck_orientation_falsification

/-- Retained application for the S2 rational duality contract.
Source: docs/notes/native-inputs/s2e-chain-contract.md:649–668;
QuotientDuality/RetainedLocalTrace.lean, `retained_modification_degree_one`.
HC no distance; AV milestone no distance. -/
theorem s2e_chain_modification_trace
    : ∃ (o : LocalRationalOrientation (TopCat.of (ComplexPoint W)) (2 * (h + 1)))
      (o₀ : LocalRationalOrientation (TopCat.of (ComplexPoint W₀)) (2 * (h + 1)))
      (c : Homology ℚ (TopCat.of (ComplexPoint W)) (2 * (h + 1)))
      (c₀ : Homology ℚ (TopCat.of (ComplexPoint W₀)) (2 * (h + 1))),
      (∀ x, localOrientation (TopCat.of (ComplexPoint W)) (2 * (h + 1)) c x = o.generator x) ∧
      (∀ x, localOrientation (TopCat.of (ComplexPoint W₀)) (2 * (h + 1)) c₀ x = o₀.generator x) ∧
      (∀ (x : ComplexPoint W)
        (E : OpenPartialHomeomorph (ComplexPoint W) (Fin (h + 1) → ℂ))
        (hx : x ∈ E.source),
        (∀ j, (f4_analytification W).IsHolFun (fun y : E.source => E y j)) →
        localOrientation (TopCat.of (ComplexPoint W)) (2 * (h + 1)) c x =
          localClassOfChart (h + 1) E x hx) ∧ (∀ (x : ComplexPoint W₀)
        (E : OpenPartialHomeomorph (ComplexPoint W₀) (Fin (h + 1) → ℂ))
        (hx : x ∈ E.source),
        (∀ j, (f4_analytification W₀).IsHolFun (fun y : E.source => E y j)) →
        localOrientation (TopCat.of (ComplexPoint W₀)) (2 * (h + 1)) c₀ x =
          localClassOfChart (h + 1) E x hx) ∧
      homologyMap ℚ (2 * (h + 1))
        (TopCat.ofHom (Point.continuousMap (eFinal.inv ≫ s2e_towerTotalMap (fun i => s2b_normalizationOver (B i) (η i)) eW.hom w (Fin.last r)))) c = c₀ ∧
      ∀ u, orientationIntegral (TopCat.of (ComplexPoint W)) (2 * (h + 1)) c
        (cohomologyMap ℚ (2 * (h + 1))
          (TopCat.ofHom (Point.continuousMap (eFinal.inv ≫ s2e_towerTotalMap (fun i => s2b_normalizationOver (B i) (η i)) eW.hom w (Fin.last r)))) u) = orientationIntegral (TopCat.of (ComplexPoint W₀)) (2 * (h + 1)) c₀ u :=
  retained_modification_degree_one S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder W eFinal

example := RetainedTraceChecks.retained_modification_model

/-- Retained application for the S2 rational duality contract.
Source: docs/notes/native-inputs/s2e-chain-contract.md:649–668;
QuotientDuality/RetainedLocalTrace.lean, `retained_cup_comparison`.
HC no distance; AV milestone no distance. -/
theorem s2e_chain_cup_comparison
    : (∀ (p q : ℕ) (u : Cohomology ℚ (TopCat.of (ComplexPoint W)) p) (v : Cohomology ℚ (TopCat.of (ComplexPoint W)) q),
        localTraceCup (TopCat.of (ComplexPoint W)) p q u v =
          HodgeLean.Foundations.Singular.cup (TopCat.of (ComplexPoint W)) rfl u v) ∧
      (∀ (p q : ℕ) (u : Cohomology ℚ (TopCat.of (ComplexPoint W₀)) p) (v : Cohomology ℚ (TopCat.of (ComplexPoint W₀)) q),
        localTraceCup (TopCat.of (ComplexPoint W₀)) p q u v =
          HodgeLean.Foundations.Singular.cup (TopCat.of (ComplexPoint W₀)) rfl u v) ∧
      ∀ (p q : ℕ) (u : Cohomology ℚ (TopCat.of (ComplexPoint W₀)) p) (v : Cohomology ℚ (TopCat.of (ComplexPoint W₀)) q),
        cohomologyMap ℚ (p + q) (TopCat.ofHom (Point.continuousMap (eFinal.inv ≫ s2e_towerTotalMap (fun i => s2b_normalizationOver (B i) (η i)) eW.hom w (Fin.last r))))
          (localTraceCup (TopCat.of (ComplexPoint W₀)) p q u v) =
        localTraceCup (TopCat.of (ComplexPoint W)) p q
          (cohomologyMap ℚ p (TopCat.ofHom (Point.continuousMap (eFinal.inv ≫ s2e_towerTotalMap (fun i => s2b_normalizationOver (B i) (η i)) eW.hom w (Fin.last r)))) u)
          (cohomologyMap ℚ q (TopCat.ofHom (Point.continuousMap (eFinal.inv ≫ s2e_towerTotalMap (fun i => s2b_normalizationOver (B i) (η i)) eW.hom w (Fin.last r)))) v) :=
  retained_cup_comparison S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder W eFinal

example := RetainedTraceChecks.retained_cup_comparison_falsification

/-- Retained application for the S2 rational duality contract.
Source: docs/notes/native-inputs/s2e-chain-contract.md:649–668;
QuotientDuality/RetainedLocalTrace.lean, `retained_rational_comparison_square`.
HC no distance; AV milestone no distance. -/
theorem s2e_chain_rational_comparison_square
    : ∃ (hW : ∀ (x : ComplexPoint W) (U : Opens (ComplexPoint W)), x ∈ U →
        ∃ V : Opens (ComplexPoint W), x ∈ V ∧ ContractibleSpace V ∧ V ≤ U)
      (hW₀ : ∀ (x : ComplexPoint W₀) (U : Opens (ComplexPoint W₀)), x ∈ U →
        ∃ V : Opens (ComplexPoint W₀), x ∈ V ∧ ContractibleSpace V ∧ V ≤ U)
      (hbW : ∀ n, Function.Bijective (HodgeLean.Adapters.RationalSheafComparison.comparison W hW n))
      (hbW₀ : ∀ n, Function.Bijective (HodgeLean.Adapters.RationalSheafComparison.comparison W₀ hW₀ n)),
      (∀ (n : ℕ) (u : Cohomology ℚ (TopCat.of (ComplexPoint W₀)) n),
        HodgeLean.Adapters.RationalSheafComparison.comparison W hW n
          (cohomologyMap ℚ n (TopCat.ofHom (Point.continuousMap (eFinal.inv ≫ s2e_towerTotalMap (fun i => s2b_normalizationOver (B i) (η i)) eW.hom w (Fin.last r)))) u) =
        HodgeLean.Adapters.RationalSheafComparison.pullback (eFinal.inv ≫ s2e_towerTotalMap (fun i => s2b_normalizationOver (B i) (η i)) eW.hom w (Fin.last r)) n
          (HodgeLean.Adapters.RationalSheafComparison.comparison W₀ hW₀ n u)) ∧
      (∀ (n : ℕ) (u : Cohomology ℚ (TopCat.of (ComplexPoint W)) n),
        HodgeLean.Adapters.RationalSheafComparison.comparison W hW n
          (cohomologyMap ℚ n (TopCat.ofHom (Point.continuousMap (eFinal.inv ≫ d (Fin.last r) ≫ eFinal.hom))) u) =
        HodgeLean.Adapters.RationalSheafComparison.pullback (eFinal.inv ≫ d (Fin.last r) ≫ eFinal.hom) n
          (HodgeLean.Adapters.RationalSheafComparison.comparison W hW n u)) ∧
      (∀ (n : ℕ) (u : Cohomology ℚ (TopCat.of (ComplexPoint W₀)) n),
        HodgeLean.Adapters.RationalSheafComparison.comparison W₀ hW₀ n
          (cohomologyMap ℚ n (TopCat.ofHom (Point.continuousMap (d₀))) u) =
        HodgeLean.Adapters.RationalSheafComparison.pullback (d₀) n
          (HodgeLean.Adapters.RationalSheafComparison.comparison W₀ hW₀ n u)) ∧
        (∀ (p q : ℕ) (u : Cohomology ℚ (TopCat.of (ComplexPoint W)) p)
          (v : Cohomology ℚ (TopCat.of (ComplexPoint W)) q),
          HodgeLean.Adapters.RationalSheafComparison.comparison W hW (p + q)
            (localTraceCup (TopCat.of (ComplexPoint W)) p q u v) =
          comparisonSheafCup W hW hbW p q (HodgeLean.Adapters.RationalSheafComparison.comparison W hW p u)
            (HodgeLean.Adapters.RationalSheafComparison.comparison W hW q v)) ∧
        (∀ (p q : ℕ) (u : Cohomology ℚ (TopCat.of (ComplexPoint W₀)) p)
          (v : Cohomology ℚ (TopCat.of (ComplexPoint W₀)) q),
          HodgeLean.Adapters.RationalSheafComparison.comparison W₀ hW₀ (p + q)
            (localTraceCup (TopCat.of (ComplexPoint W₀)) p q u v) =
          comparisonSheafCup W₀ hW₀ hbW₀ p q (HodgeLean.Adapters.RationalSheafComparison.comparison W₀ hW₀ p u)
            (HodgeLean.Adapters.RationalSheafComparison.comparison W₀ hW₀ q v)) :=
  retained_rational_comparison_square S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder W eFinal

example := RetainedTraceChecks.retained_rational_comparison_model

/-- The retained degree-one modification preserves the literal singular cup pairing.
Source: docs/notes/native-inputs/s2e-chain-contract.md:362,659–668;
Hatcher, Algebraic Topology, sections 2.2 and 3.2.
HC no distance; AV milestone no distance. -/
theorem s2e_chain_modification_trace_pairing
    : ∃ (o : LocalRationalOrientation (TopCat.of (ComplexPoint W)) (2 * (h + 1)))
      (o₀ : LocalRationalOrientation (TopCat.of (ComplexPoint W₀)) (2 * (h + 1)))
      (c : Homology ℚ (TopCat.of (ComplexPoint W)) (2 * (h + 1)))
      (c₀ : Homology ℚ (TopCat.of (ComplexPoint W₀)) (2 * (h + 1))),
      (∀ x, localOrientation (TopCat.of (ComplexPoint W)) (2 * (h + 1)) c x = o.generator x) ∧
      (∀ x, localOrientation (TopCat.of (ComplexPoint W₀)) (2 * (h + 1)) c₀ x = o₀.generator x) ∧
      (∀ (x : ComplexPoint W)
        (E : OpenPartialHomeomorph (ComplexPoint W) (Fin (h + 1) → ℂ))
        (hx : x ∈ E.source),
        (∀ j, (f4_analytification W).IsHolFun (fun y : E.source => E y j)) →
        localOrientation (TopCat.of (ComplexPoint W)) (2 * (h + 1)) c x =
          localClassOfChart (h + 1) E x hx) ∧ (∀ (x : ComplexPoint W₀)
        (E : OpenPartialHomeomorph (ComplexPoint W₀) (Fin (h + 1) → ℂ))
        (hx : x ∈ E.source),
        (∀ j, (f4_analytification W₀).IsHolFun (fun y : E.source => E y j)) →
        localOrientation (TopCat.of (ComplexPoint W₀)) (2 * (h + 1)) c₀ x =
          localClassOfChart (h + 1) E x hx) ∧
      homologyMap ℚ (2 * (h + 1))
        (TopCat.ofHom (Point.continuousMap (eFinal.inv ≫ s2e_towerTotalMap (fun i => s2b_normalizationOver (B i) (η i)) eW.hom w (Fin.last r)))) c = c₀ ∧
      (∀ u, orientationIntegral (TopCat.of (ComplexPoint W)) (2 * (h + 1)) c
        (cohomologyMap ℚ (2 * (h + 1))
          (TopCat.ofHom (Point.continuousMap (eFinal.inv ≫ s2e_towerTotalMap (fun i => s2b_normalizationOver (B i) (η i)) eW.hom w (Fin.last r)))) u) = orientationIntegral (TopCat.of (ComplexPoint W₀)) (2 * (h + 1)) c₀ u) ∧
      ∀ (u v : Cohomology ℚ (TopCat.of (ComplexPoint W₀)) (h + 1)),
        orientationIntegral (TopCat.of (ComplexPoint W)) (2 * (h + 1)) c
          (HodgeLean.Foundations.Singular.cup (TopCat.of (ComplexPoint W)) (by omega)
            (cohomologyMap ℚ (h + 1) (TopCat.ofHom (Point.continuousMap (eFinal.inv ≫ s2e_towerTotalMap (fun i => s2b_normalizationOver (B i) (η i)) eW.hom w (Fin.last r)))) u)
            (cohomologyMap ℚ (h + 1) (TopCat.ofHom (Point.continuousMap (eFinal.inv ≫ s2e_towerTotalMap (fun i => s2b_normalizationOver (B i) (η i)) eW.hom w (Fin.last r)))) v)) =
        orientationIntegral (TopCat.of (ComplexPoint W₀)) (2 * (h + 1)) c₀
          (HodgeLean.Foundations.Singular.cup (TopCat.of (ComplexPoint W₀)) (by omega) u v) := by
  obtain ⟨o, o₀, c, c₀, hc, hc₀, hchart, hchart₀, hdegree, htrace⟩ :=
    retained_modification_degree_one S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder W eFinal
  refine ⟨o, o₀, c, c₀, hc, hc₀, hchart, hchart₀, hdegree, htrace, ?_⟩
  intro u v
  rw [← HodgeLean.Foundations.Singular.cohomologyMap_cup]
  exact htrace _

example := RetainedTraceChecks.retained_modification_model

/-- Both retained deck maps preserve the same complex-normalized traces and cup pairings.
The total modification has geometric degree one for those classes.
Source: docs/notes/native-inputs/s2e-chain-contract.md:360–362,659–668;
Bredon, Sheaf Theory, V.9; Hatcher, Algebraic Topology, section 3.2.
HC no distance; AV milestone no distance. -/
theorem s2e_chain_deck_trace_pairing
    : ∃ (o : LocalRationalOrientation (TopCat.of (ComplexPoint W)) (2 * (h + 1)))
      (o₀ : LocalRationalOrientation (TopCat.of (ComplexPoint W₀)) (2 * (h + 1)))
      (c : Homology ℚ (TopCat.of (ComplexPoint W)) (2 * (h + 1)))
      (c₀ : Homology ℚ (TopCat.of (ComplexPoint W₀)) (2 * (h + 1))),
      (∀ x, localOrientation (TopCat.of (ComplexPoint W)) (2 * (h + 1)) c x = o.generator x) ∧
      (∀ x, localOrientation (TopCat.of (ComplexPoint W₀)) (2 * (h + 1)) c₀ x = o₀.generator x) ∧
      (∀ (x : ComplexPoint W)
        (E : OpenPartialHomeomorph (ComplexPoint W) (Fin (h + 1) → ℂ))
        (hx : x ∈ E.source),
        (∀ j, (f4_analytification W).IsHolFun (fun y : E.source => E y j)) →
        localOrientation (TopCat.of (ComplexPoint W)) (2 * (h + 1)) c x =
          localClassOfChart (h + 1) E x hx) ∧ (∀ (x : ComplexPoint W₀)
        (E : OpenPartialHomeomorph (ComplexPoint W₀) (Fin (h + 1) → ℂ))
        (hx : x ∈ E.source),
        (∀ j, (f4_analytification W₀).IsHolFun (fun y : E.source => E y j)) →
        localOrientation (TopCat.of (ComplexPoint W₀)) (2 * (h + 1)) c₀ x =
          localClassOfChart (h + 1) E x hx) ∧
      homologyMap ℚ (2 * (h + 1))
        (TopCat.ofHom (Point.continuousMap (eFinal.inv ≫ s2e_towerTotalMap (fun i => s2b_normalizationOver (B i) (η i)) eW.hom w (Fin.last r)))) c = c₀ ∧
      (∀ u, orientationIntegral (TopCat.of (ComplexPoint W)) (2 * (h + 1)) c
        (cohomologyMap ℚ (2 * (h + 1))
          (TopCat.ofHom (Point.continuousMap (eFinal.inv ≫ s2e_towerTotalMap (fun i => s2b_normalizationOver (B i) (η i)) eW.hom w (Fin.last r)))) u) = orientationIntegral (TopCat.of (ComplexPoint W₀)) (2 * (h + 1)) c₀ u) ∧
      (∀ u, orientationIntegral (TopCat.of (ComplexPoint W)) (2 * (h + 1)) c
        (cohomologyMap ℚ (2 * (h + 1)) (TopCat.ofHom (Point.continuousMap (eFinal.inv ≫ d (Fin.last r) ≫ eFinal.hom))) u) =
        orientationIntegral (TopCat.of (ComplexPoint W)) (2 * (h + 1)) c u) ∧
      (∀ u, orientationIntegral (TopCat.of (ComplexPoint W₀)) (2 * (h + 1)) c₀
        (cohomologyMap ℚ (2 * (h + 1)) (TopCat.ofHom (Point.continuousMap d₀)) u) =
        orientationIntegral (TopCat.of (ComplexPoint W₀)) (2 * (h + 1)) c₀ u) ∧
      (∀ (u v : Cohomology ℚ (TopCat.of (ComplexPoint W)) (h + 1)),
        orientationIntegral (TopCat.of (ComplexPoint W)) (2 * (h + 1)) c
          (HodgeLean.Foundations.Singular.cup (TopCat.of (ComplexPoint W)) (by omega)
            (cohomologyMap ℚ (h + 1) (TopCat.ofHom (Point.continuousMap (eFinal.inv ≫ d (Fin.last r) ≫ eFinal.hom))) u)
            (cohomologyMap ℚ (h + 1) (TopCat.ofHom (Point.continuousMap (eFinal.inv ≫ d (Fin.last r) ≫ eFinal.hom))) v)) =
        orientationIntegral (TopCat.of (ComplexPoint W)) (2 * (h + 1)) c
          (HodgeLean.Foundations.Singular.cup (TopCat.of (ComplexPoint W)) (by omega) u v)) ∧
      (∀ (u v : Cohomology ℚ (TopCat.of (ComplexPoint W₀)) (h + 1)),
        orientationIntegral (TopCat.of (ComplexPoint W₀)) (2 * (h + 1)) c₀
          (HodgeLean.Foundations.Singular.cup (TopCat.of (ComplexPoint W₀)) (by omega)
            (cohomologyMap ℚ (h + 1) (TopCat.ofHom (Point.continuousMap d₀)) u)
            (cohomologyMap ℚ (h + 1) (TopCat.ofHom (Point.continuousMap d₀)) v)) =
        orientationIntegral (TopCat.of (ComplexPoint W₀)) (2 * (h + 1)) c₀
          (HodgeLean.Foundations.Singular.cup (TopCat.of (ComplexPoint W₀)) (by omega) u v)) := by
  obtain ⟨o, o₀, c, c₀, hc, hc₀, hchart, hchart₀, hdegree, htrace⟩ :=
    retained_modification_degree_one S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder W eFinal
  have hm : 0 < S.m := by have hm := S.three_le; omega
  have hpow := s2e_c1_transport_generator_order eFinal.symm
    (d (Fin.last r)) S.m (horder (Fin.last r))
  have he : eW.inv ≫ d 0 ≫ eW.hom = d₀ := by
    rw [hdinit, eW.inv_hom_id_assoc]
  have hpow₀ := s2e_c1_transport_generator_order eW.symm (d 0) S.m (horder 0)
  change End.of (eW.inv ≫ d 0 ≫ eW.hom) ^ S.m = 1 at hpow₀
  rw [he] at hpow₀
  have ht := scheme_deck_trace W (h + 1) o c hc hchart
    (eFinal.inv ≫ d (Fin.last r) ≫ eFinal.hom) S.m hm hpow
  have ht₀ := scheme_deck_trace W₀ (h + 1) o₀ c₀ hc₀ hchart₀ d₀ S.m hm hpow₀
  refine ⟨o, o₀, c, c₀, hc, hc₀, hchart, hchart₀, hdegree, htrace, ht, ht₀, ?_, ?_⟩
  · intro u v
    rw [← HodgeLean.Foundations.Singular.cohomologyMap_cup]
    exact ht _
  · intro u v
    rw [← HodgeLean.Foundations.Singular.cohomologyMap_cup]
    exact ht₀ _

example := LocalTraceChecks.check_local_deck_trace_pairing

/-- Retained deck compatibility with the complex-normalized trace.
Source: docs/notes/native-inputs/s2e-chain-contract.md:360–361,659–668;
Bredon, Sheaf Theory, V.9; Hatcher, Algebraic Topology, section 3.2.
HC no distance; AV milestone no distance. -/
theorem s2e_chain_deck_trace_invariant
    : ∃ (o : LocalRationalOrientation (TopCat.of (ComplexPoint W)) (2 * (h + 1)))
      (o₀ : LocalRationalOrientation (TopCat.of (ComplexPoint W₀)) (2 * (h + 1)))
      (c : Homology ℚ (TopCat.of (ComplexPoint W)) (2 * (h + 1)))
      (c₀ : Homology ℚ (TopCat.of (ComplexPoint W₀)) (2 * (h + 1))),
      (∀ x, localOrientation (TopCat.of (ComplexPoint W)) (2 * (h + 1)) c x = o.generator x) ∧
      (∀ x, localOrientation (TopCat.of (ComplexPoint W₀)) (2 * (h + 1)) c₀ x = o₀.generator x) ∧
      (∀ (x : ComplexPoint W)
        (E : OpenPartialHomeomorph (ComplexPoint W) (Fin (h + 1) → ℂ))
        (hx : x ∈ E.source),
        (∀ j, (f4_analytification W).IsHolFun (fun y : E.source => E y j)) →
        localOrientation (TopCat.of (ComplexPoint W)) (2 * (h + 1)) c x =
          localClassOfChart (h + 1) E x hx) ∧ (∀ (x : ComplexPoint W₀)
        (E : OpenPartialHomeomorph (ComplexPoint W₀) (Fin (h + 1) → ℂ))
        (hx : x ∈ E.source),
        (∀ j, (f4_analytification W₀).IsHolFun (fun y : E.source => E y j)) →
        localOrientation (TopCat.of (ComplexPoint W₀)) (2 * (h + 1)) c₀ x =
          localClassOfChart (h + 1) E x hx) ∧
      homologyMap ℚ (2 * (h + 1))
        (TopCat.ofHom (Point.continuousMap (eFinal.inv ≫ s2e_towerTotalMap (fun i => s2b_normalizationOver (B i) (η i)) eW.hom w (Fin.last r)))) c = c₀ ∧
      (∀ u, orientationIntegral (TopCat.of (ComplexPoint W)) (2 * (h + 1)) c
        (cohomologyMap ℚ (2 * (h + 1))
          (TopCat.ofHom (Point.continuousMap (eFinal.inv ≫ s2e_towerTotalMap (fun i => s2b_normalizationOver (B i) (η i)) eW.hom w (Fin.last r)))) u) = orientationIntegral (TopCat.of (ComplexPoint W₀)) (2 * (h + 1)) c₀ u) ∧
      (∀ u, orientationIntegral (TopCat.of (ComplexPoint W)) (2 * (h + 1)) c
        (cohomologyMap ℚ (2 * (h + 1)) (TopCat.ofHom (Point.continuousMap (eFinal.inv ≫ d (Fin.last r) ≫ eFinal.hom))) u) =
        orientationIntegral (TopCat.of (ComplexPoint W)) (2 * (h + 1)) c u) ∧
      (∀ u, orientationIntegral (TopCat.of (ComplexPoint W₀)) (2 * (h + 1)) c₀
        (cohomologyMap ℚ (2 * (h + 1)) (TopCat.ofHom (Point.continuousMap d₀)) u) =
        orientationIntegral (TopCat.of (ComplexPoint W₀)) (2 * (h + 1)) c₀ u) := by
  obtain ⟨o, o₀, c, c₀, hc, hc₀, hchart, hchart₀, hdegree, htrace, ht, ht₀, hp, hp₀⟩ :=
    s2e_chain_deck_trace_pairing S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder W eFinal
  exact ⟨o, o₀, c, c₀, hc, hc₀, hchart, hchart₀, hdegree, htrace, ht, ht₀⟩

example := LocalTraceChecks.check_local_deck_trace_pairing

/-- Retained deck compatibility with the complex-normalized trace.
Source: docs/notes/native-inputs/s2e-chain-contract.md:360–361,659–668;
Bredon, Sheaf Theory, V.9; Hatcher, Algebraic Topology, section 3.2.
HC no distance; AV milestone no distance. -/
theorem s2e_chain_deck_pairing_invariant
    : ∃ (o : LocalRationalOrientation (TopCat.of (ComplexPoint W)) (2 * (h + 1)))
      (o₀ : LocalRationalOrientation (TopCat.of (ComplexPoint W₀)) (2 * (h + 1)))
      (c : Homology ℚ (TopCat.of (ComplexPoint W)) (2 * (h + 1)))
      (c₀ : Homology ℚ (TopCat.of (ComplexPoint W₀)) (2 * (h + 1))),
      (∀ x, localOrientation (TopCat.of (ComplexPoint W)) (2 * (h + 1)) c x = o.generator x) ∧
      (∀ x, localOrientation (TopCat.of (ComplexPoint W₀)) (2 * (h + 1)) c₀ x = o₀.generator x) ∧
      (∀ (x : ComplexPoint W)
        (E : OpenPartialHomeomorph (ComplexPoint W) (Fin (h + 1) → ℂ))
        (hx : x ∈ E.source),
        (∀ j, (f4_analytification W).IsHolFun (fun y : E.source => E y j)) →
        localOrientation (TopCat.of (ComplexPoint W)) (2 * (h + 1)) c x =
          localClassOfChart (h + 1) E x hx) ∧ (∀ (x : ComplexPoint W₀)
        (E : OpenPartialHomeomorph (ComplexPoint W₀) (Fin (h + 1) → ℂ))
        (hx : x ∈ E.source),
        (∀ j, (f4_analytification W₀).IsHolFun (fun y : E.source => E y j)) →
        localOrientation (TopCat.of (ComplexPoint W₀)) (2 * (h + 1)) c₀ x =
          localClassOfChart (h + 1) E x hx) ∧
      homologyMap ℚ (2 * (h + 1))
        (TopCat.ofHom (Point.continuousMap (eFinal.inv ≫ s2e_towerTotalMap (fun i => s2b_normalizationOver (B i) (η i)) eW.hom w (Fin.last r)))) c = c₀ ∧
      (∀ u, orientationIntegral (TopCat.of (ComplexPoint W)) (2 * (h + 1)) c
        (cohomologyMap ℚ (2 * (h + 1))
          (TopCat.ofHom (Point.continuousMap (eFinal.inv ≫ s2e_towerTotalMap (fun i => s2b_normalizationOver (B i) (η i)) eW.hom w (Fin.last r)))) u) = orientationIntegral (TopCat.of (ComplexPoint W₀)) (2 * (h + 1)) c₀ u) ∧
      (∀ (u v : Cohomology ℚ (TopCat.of (ComplexPoint W)) (h + 1)),
        orientationIntegral (TopCat.of (ComplexPoint W)) (2 * (h + 1)) c
          (HodgeLean.Foundations.Singular.cup (TopCat.of (ComplexPoint W)) (by omega)
            (cohomologyMap ℚ (h + 1) (TopCat.ofHom (Point.continuousMap (eFinal.inv ≫ d (Fin.last r) ≫ eFinal.hom))) u)
            (cohomologyMap ℚ (h + 1) (TopCat.ofHom (Point.continuousMap (eFinal.inv ≫ d (Fin.last r) ≫ eFinal.hom))) v)) =
        orientationIntegral (TopCat.of (ComplexPoint W)) (2 * (h + 1)) c
          (HodgeLean.Foundations.Singular.cup (TopCat.of (ComplexPoint W)) (by omega) u v)) ∧
      (∀ (u v : Cohomology ℚ (TopCat.of (ComplexPoint W₀)) (h + 1)),
        orientationIntegral (TopCat.of (ComplexPoint W₀)) (2 * (h + 1)) c₀
          (HodgeLean.Foundations.Singular.cup (TopCat.of (ComplexPoint W₀)) (by omega)
            (cohomologyMap ℚ (h + 1) (TopCat.ofHom (Point.continuousMap d₀)) u)
            (cohomologyMap ℚ (h + 1) (TopCat.ofHom (Point.continuousMap d₀)) v)) =
        orientationIntegral (TopCat.of (ComplexPoint W₀)) (2 * (h + 1)) c₀
          (HodgeLean.Foundations.Singular.cup (TopCat.of (ComplexPoint W₀)) (by omega) u v)) := by
  obtain ⟨o, o₀, c, c₀, hc, hc₀, hchart, hchart₀, hdegree, htrace, ht, ht₀, hp, hp₀⟩ :=
    s2e_chain_deck_trace_pairing S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder W eFinal
  exact ⟨o, o₀, c, c₀, hc, hc₀, hchart, hchart₀, hdegree, htrace, hp, hp₀⟩

example := LocalTraceChecks.check_local_deck_trace_pairing

end HodgeLean.Foundations.QuotientDuality
