import HodgeLean.Foundations.QuotientDuality.RetainedFinalOrientation
import HodgeLean.Foundations.QuotientDuality.LocalComplexNormalization
import HodgeLean.Foundations.QuotientDuality.LocalDenseChartCalibration
import HodgeLean.Foundations.QuotientDuality.RetainedZeroTowerOrientation
import HodgeLean.Foundations.QuotientDuality.RetainedModificationLocalWitness
import HodgeLean.Foundations.QuotientDuality.ModificationPushforwardOrientation
import HodgeLean.Foundations.QuotientDuality.LocalRetainedConnectedness
import HodgeLean.Foundations.QuotientDuality.LocalAlgebraicOrientation
import HodgeLean.Foundations.QuotientDuality.LocalTrace
import HodgeLean.Foundations.QuotientDuality.LocalCupCompatibility
import HodgeLean.Foundations.AlgebraicGeometry.ComplexTopology.Basis
import HodgeLean.Foundations.Topology.RationalSheafComparison
import HodgeLean.Foundations.Program.SchoenTowerGeometryDefs
import HodgeLean.Foundations.Program.SchoenCycleTowerHelpers
import HodgeLean.Foundations.Analytic.Analytification
import HodgeLean.Adapters.RationalSheafComparisonDefs
import HodgeLean.Foundations.Singular.Cup
import HodgeLean.Foundations.QuotientDuality.ComparisonCupDefs

/-! # Retained quotient orientations and normalized traces

The tower, deck maps and modification are the retained algebraic constructions.
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


/-- The retained quotient has a class with the complex smooth-chart normalization.
Source: docs/notes/native-inputs/s2e-chain-contract.md:649–668;
Bredon, Sheaf Theory, V.9; Bott–Tu, Differential Forms in Algebraic Topology, sections 5–6. -/
theorem retained_initial_normalized_trace
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
        orientationIntegral (TopCat.of (ComplexPoint W₀)) (2 * (h + 1)) c (relativeCohomologyToAbsolute ℚ (pointComplementPair x) (2 * (h + 1)) v) = (1 : ℚ) := by
  obtain ⟨cP, o, c, hcP, hdegree, hc⟩ := retained_initial_coherent_orientation
    S Y W₀ a e ha1 hamul (h + 1) q₀ hqsurj hqinv hq hdimY
  obtain ⟨o', c', hc', hchart⟩ := normalize_complex_global_orientation W₀ (h + 1) o c hc
  refine ⟨o', c', hc', hchart, ?_⟩
  intro x v hv
  apply local_trace_normalization_aux (TopCat.of (ComplexPoint W₀)) (2 * (h + 1)) c' x v
  rw [hc' x]
  exact hv

example := LocalTraceChecks.check_local_trace_normalization

/-- The retained quotient has a class with the complex smooth-chart normalization.
Source: docs/notes/native-inputs/s2e-chain-contract.md:649–668;
Bredon, Sheaf Theory, V.9; Bott–Tu, Differential Forms in Algebraic Topology, sections 5–6. -/
theorem retained_final_normalized_trace
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
        orientationIntegral (TopCat.of (ComplexPoint W)) (2 * (h + 1)) c (relativeCohomologyToAbsolute ℚ (pointComplementPair x) (2 * (h + 1)) v) = (1 : ℚ) := by
  obtain ⟨o, c, hc⟩ :=
    retained_final_coherent_orientation S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder W eFinal
  obtain ⟨o', c', hc', hchart⟩ := normalize_complex_global_orientation W (h + 1) o c hc
  refine ⟨o', c', hc', hchart, ?_⟩
  intro x v hv
  apply local_trace_normalization_aux (TopCat.of (ComplexPoint W)) (2 * (h + 1)) c' x v
  rw [hc' x]
  exact hv

example := LocalTraceChecks.check_local_trace_normalization

/-- The retained algebraic deck generator preserves the complex local orientations.
Source: docs/notes/native-inputs/s2e-chain-contract.md:649–668;
Bredon, Sheaf Theory, V.9; Bott–Tu, Differential Forms in Algebraic Topology, sections 5–6. -/
theorem retained_initial_deck_orientation
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
          localClassOfChart (h + 1) E x hx) := by
  obtain ⟨o, c, hc, hchart, _⟩ :=
    retained_initial_normalized_trace S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder W eFinal
  have hnorm : ∀ (x : ComplexPoint W₀)
      (E : OpenPartialHomeomorph (ComplexPoint W₀) (Fin (h + 1) → ℂ))
      (hx : x ∈ E.source),
      (∀ j, (f4_analytification W₀).IsHolFun (fun y : E.source => E y j)) →
      o.generator x = localClassOfChart (h + 1) E x hx := by
    intro x E hx hhE
    exact (hc x).symm.trans (hchart x E hx hhE)
  have he : eW.inv ≫ d 0 ≫ eW.hom = d₀ := by
    rw [hdinit, eW.inv_hom_id_assoc]
  have hpow := s2e_c1_transport_generator_order eW.symm (d 0) S.m (horder 0)
  change End.of (eW.inv ≫ d 0 ≫ eW.hom) ^ S.m = 1 at hpow
  rw [he] at hpow
  obtain ⟨H, hH, hpres⟩ := finite_order_preserves_normalized_orientation
    W₀ (h + 1) o c hc hnorm d₀ S.m (by have hm := S.three_le; omega) hpow
  exact ⟨o, H, hH, hpres, hnorm⟩

example := LocalTraceChecks.check_local_homeomorph_fundamental

/-- The retained algebraic deck generator preserves the complex local orientations.
Source: docs/notes/native-inputs/s2e-chain-contract.md:649–668;
Bredon, Sheaf Theory, V.9; Bott–Tu, Differential Forms in Algebraic Topology, sections 5–6. -/
theorem retained_final_deck_orientation
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
          localClassOfChart (h + 1) E x hx) := by
  obtain ⟨o, c, hc, hchart, _⟩ :=
    retained_final_normalized_trace S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder W eFinal
  have hnorm : ∀ (x : ComplexPoint W)
      (E : OpenPartialHomeomorph (ComplexPoint W) (Fin (h + 1) → ℂ))
      (hx : x ∈ E.source),
      (∀ j, (f4_analytification W).IsHolFun (fun y : E.source => E y j)) →
      o.generator x = localClassOfChart (h + 1) E x hx := by
    intro x E hx hhE
    exact (hc x).symm.trans (hchart x E hx hhE)
  have hpow := s2e_c1_transport_generator_order eFinal.symm
    (d (Fin.last r)) S.m (horder (Fin.last r))
  obtain ⟨H, hH, hpres⟩ := finite_order_preserves_normalized_orientation
    W (h + 1) o c hc hnorm (eFinal.inv ≫ d (Fin.last r) ≫ eFinal.hom) S.m (by have hm := S.three_le; omega) hpow
  exact ⟨o, H, hH, hpres, hnorm⟩

example := LocalTraceChecks.check_local_homeomorph_fundamental

/-- The retained total modification has degree one with the same normalization at both ends.
Source: docs/notes/native-inputs/s2e-chain-contract.md:649–668;
Bredon, Sheaf Theory, V.9; Bott–Tu, Differential Forms in Algebraic Topology, sections 5–6. -/
theorem retained_modification_degree_one
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
          (TopCat.ofHom (Point.continuousMap (eFinal.inv ≫ s2e_towerTotalMap (fun i => s2b_normalizationOver (B i) (η i)) eW.hom w (Fin.last r)))) u) = orientationIntegral (TopCat.of (ComplexPoint W₀)) (2 * (h + 1)) c₀ u := by
  obtain ⟨o, c, hc, hchart, _⟩ := retained_final_normalized_trace S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder W eFinal
  obtain ⟨o₀, cold, hcold, hchartold, _⟩ := retained_initial_normalized_trace S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder W eFinal
  have hn : ∀ (x : ComplexPoint W)
      (E : OpenPartialHomeomorph (ComplexPoint W) (Fin (h + 1) → ℂ)) (hx : x ∈ E.source),
      (∀ i, (f4_analytification W).IsHolFun (fun y : E.source => E y i)) →
      o.generator x = localClassOfChart (h + 1) E x hx := by
    intro x E hx hhE
    exact (hc x).symm.trans (hchart x E hx hhE)
  have hn₀ : ∀ (x : ComplexPoint W₀)
      (E : OpenPartialHomeomorph (ComplexPoint W₀) (Fin (h + 1) → ℂ)) (hx : x ∈ E.source),
      (∀ i, (f4_analytification W₀).IsHolFun (fun y : E.source => E y i)) →
      o₀.generator x = localClassOfChart (h + 1) E x hx := by
    intro x E hx hhE
    exact (hcold x).symm.trans (hchartold x E hx hhE)
  obtain ⟨x, hf, hlocal⟩ := retained_total_complex_local_degree S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder W eFinal o o₀ hn hn₀
  let f := TopCat.ofHom (Point.continuousMap (eFinal.inv ≫ s2e_towerTotalMap
    (fun i => s2b_normalizationOver (B i) (η i)) eW.hom w (Fin.last r)))
  letI : T2Space (ComplexPoint W₀) := f4_t2Space W₀
  letI : PathConnectedSpace (ComplexPoint W₀) :=
    initial_quotient_pathConnected Y W₀ (h + 1) q₀ hqsurj
  have hlocalc : relativeHomologyMap ℚ (2 * (h + 1))
      (singletonFibrePairMap f x (f x) hf)
      (localOrientation (TopCat.of (ComplexPoint W)) (2 * (h + 1)) c x) =
      o₀.generator (f x) := by
    rw [hc x]
    exact hlocal
  have hc₀ := singletonFibre_pushforward_local_orientation
    (TopCat.of (ComplexPoint W)) (TopCat.of (ComplexPoint W₀))
    (2 * (h + 1)) o₀ c f x hf hlocalc
  refine ⟨o, o₀, c, homologyMap ℚ (2 * (h + 1)) f c, hc, hc₀, hchart, ?_, rfl, ?_⟩
  · intro z E hz hhE
    exact (hc₀ z).trans (hn₀ z E hz hhE)
  · intro u
    change cohomologyEquivDualHomology ℚ _ _ (cohomologyMap ℚ _ f u) c =
      cohomologyEquivDualHomology ℚ _ _ u (homologyMap ℚ _ f c)
    rw [cohomologyEquivDualHomology_cohomologyMap]

example := LocalTraceChecks.check_local_degree_one_trace

/-- The retained cap cup agrees with the project's singular cup on both spaces.
Source: Hatcher, Algebraic Topology, sections 3.2–3.3, cup-cap evaluation;
docs/notes/native-inputs/s2e-chain-contract.md:649–668. -/
theorem retained_cup_comparison
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
          (cohomologyMap ℚ q (TopCat.ofHom (Point.continuousMap (eFinal.inv ≫ s2e_towerTotalMap (fun i => s2b_normalizationOver (B i) (η i)) eW.hom w (Fin.last r)))) v) := by
  refine ⟨fun p q u v => localTraceCup_eq_singularCup _ p q u v,
    fun p q u v => localTraceCup_eq_singularCup _ p q u v, ?_⟩
  intro p q u v
  rw [localTraceCup_eq_singularCup, localTraceCup_eq_singularCup]
  exact HodgeLean.Foundations.Singular.cohomologyMap_cup _ _ rfl u v

example :
    HodgeLean.Foundations.Singular.cup (R := ℚ) (TopCat.of Unit) (p := 0) (q := 0) (k := 0) rfl
      ((2 : ℚ) • HodgeLean.Foundations.Singular.unit (R := ℚ) (TopCat.of Unit))
      ((3 : ℚ) • HodgeLean.Foundations.Singular.unit (R := ℚ) (TopCat.of Unit)) =
      (6 : ℚ) • HodgeLean.Foundations.Singular.unit (R := ℚ) (TopCat.of Unit) := by
  rw [HodgeLean.Foundations.Singular.cup_constants]
  norm_num

/-- M2 supplies the retained neighbourhood bases, and M1 compares the actual pullback maps.
Source: Bredon, Sheaf Theory, II.4, II.6, III.1;
docs/notes/native-inputs/s2e-chain-contract.md:649–668. -/
theorem retained_rational_comparison_square
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
            (HodgeLean.Adapters.RationalSheafComparison.comparison W₀ hW₀ q v)) := by
  let hW := HodgeLean.Foundations.ComplexTopology.finiteType_basis W
  let hW₀ := HodgeLean.Foundations.ComplexTopology.finiteType_basis W₀
  letI := f4_secondCountable W
  letI := f4_secondCountable W₀
  letI : ∀ U : Opens (ComplexPoint W), ParacompactSpace U := fun U => by
    letI : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
    infer_instance
  letI : ∀ U : Opens (ComplexPoint W₀), ParacompactSpace U := fun U => by
    letI : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
    infer_instance
  have hbW : ∀ n, Function.Bijective
      (HodgeLean.Adapters.RationalSheafComparison.comparison W hW n) := by
    intro n
    exact (HodgeLean.Topology.RationalSheafComparison.comparison_linearEquiv
      (TopCat.of (ComplexPoint W)) hW n).1
  have hbW₀ : ∀ n, Function.Bijective
      (HodgeLean.Adapters.RationalSheafComparison.comparison W₀ hW₀ n) := by
    intro n
    exact (HodgeLean.Topology.RationalSheafComparison.comparison_linearEquiv
      (TopCat.of (ComplexPoint W₀)) hW₀ n).1
  refine ⟨hW, hW₀, hbW, hbW₀, ?_, ?_, ?_, ?_, ?_⟩
  · intro n u
    exact HodgeLean.Topology.RationalSheafComparison.comparison_naturality
      (TopCat.of (ComplexPoint W)) hW (TopCat.of (ComplexPoint W₀)) hW₀ _ n u
  · intro n u
    exact HodgeLean.Topology.RationalSheafComparison.comparison_naturality
      (TopCat.of (ComplexPoint W)) hW (TopCat.of (ComplexPoint W)) hW _ n u
  · intro n u
    exact HodgeLean.Topology.RationalSheafComparison.comparison_naturality
      (TopCat.of (ComplexPoint W₀)) hW₀ (TopCat.of (ComplexPoint W₀)) hW₀ _ n u
  · intro p q u v
    rw [localTraceCup_eq_singularCup]
    let E (n : ℕ) := LinearEquiv.ofBijective
      (HodgeLean.Adapters.RationalSheafComparison.comparison W hW n).toRatLinearMap (hbW n)
    change E (p + q) (HodgeLean.Foundations.Singular.cup _ rfl u v) =
      E (p + q) (HodgeLean.Foundations.Singular.cup _ rfl
        ((E p).symm (E p u)) ((E q).symm (E q v)))
    rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  · intro p q u v
    rw [localTraceCup_eq_singularCup]
    let E (n : ℕ) := LinearEquiv.ofBijective
      (HodgeLean.Adapters.RationalSheafComparison.comparison W₀ hW₀ n).toRatLinearMap (hbW₀ n)
    change E (p + q) (HodgeLean.Foundations.Singular.cup _ rfl u v) =
      E (p + q) (HodgeLean.Foundations.Singular.cup _ rfl
        ((E p).symm (E p u)) ((E q).symm (E q v)))
    rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]

example := LocalTraceChecks.check_local_degree_one_trace

end HodgeLean.Foundations.QuotientDuality
