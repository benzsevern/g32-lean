import HodgeLean.Foundations.QuotientDuality.PersistenceQuotientBetti
import HodgeLean.Foundations.QuotientDuality.PersistenceWeightedTransport
import HodgeLean.Foundations.QuotientDuality.PersistenceTowerLifts
import HodgeLean.Foundations.QuotientDuality.PersistenceRetainedCentreVanishing
import HodgeLean.Foundations.QuotientDuality.PersistenceRetainedCentreZero
import HodgeLean.Foundations.QuotientDuality.PersistenceRetainedComparison
import HodgeLean.Foundations.QuotientDuality.PersistenceRelativeDuality
import HodgeLean.Foundations.QuotientDuality.PersistenceRetainedFibres
import HodgeLean.Foundations.QuotientDuality.PersistenceRetainedExactLifts
import HodgeLean.Foundations.QuotientDuality.PersistenceChecks
import HodgeLean.Foundations.QuotientDuality.PersistenceDefs
import HodgeLean.Foundations.QuotientDuality.PersistencePrimitiveComparison
import HodgeLean.Foundations.QuotientDuality.PersistenceExceptionalPair
import HodgeLean.Foundations.QuotientDuality.PersistenceSupport
import HodgeLean.Foundations.QuotientDuality.PersistencePairSequence
import HodgeLean.Foundations.Program.SchoenCycleC2Proofs
import HodgeLean.Foundations.Program.SchoenCycleTowerHelpers
import HodgeLean.Foundations.Program.SchoenCycleStageDefs

/-! # Primitive persistence in actual modification pairs

The retained normalization tower and its all-degree exceptional input remain explicit.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedVariables false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Foundations.Program
open AlgebraicTopology.Singular
open scoped BigOperators Manifold ContDiff OnePoint TensorProduct
namespace HodgeLean.Foundations.QuotientDuality
/-- The actual retained transition constructs the exceptional-pair comparison in every degree.
Source: Schoen (1988), Lemma 2.8; Hatcher, Algebraic Topology, sections 2.1 and 3.1.
HC no distance; AV milestone no distance. -/
theorem persistence_pair_comparison_aux
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
    (i : Fin r) :
    let I := D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
      D i.castSucc ⟨2 * i.val + 1, by omega⟩
    let kι := s2c_subschemeι (B i.castSucc) I
    let E := s2c_exceptional (b i) I
    let j : E ⟶ B i.succ := pullback.fst (b i) kι
    let β := s2b_normalizationMap (B i.succ) (η i.succ)
    let βprev := s2b_normalizationMap (B i.castSucc) (η i.castSucc)
    let A := Set.range (Point.map (s2b_toCover βprev kι))
    IsProper (w i).left ∧
    Point.map (w i) ⁻¹' A = Set.range (Point.map (s2b_toCover β j)) ∧
    (∀ y : ComplexPoint (s2b_normalizationOver (B i.castSucc) (η i.castSucc)),
      y ∉ A → ∃! x, Point.map (w i) x = y) ∧
    ∀ n : ℕ, Function.Bijective (persistenceRelativePullback ℂ
      (TopCat.ofHom (Point.continuousMap (w i))) A n) := by
  refine ⟨persistence_retained_transition_proper S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder i, ?_, persistence_retained_off_centre_fibre S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder i, ?_⟩
  · exact persistence_normalization_exceptional_support (η i.succ) (η i.castSucc)
      (b i) (hη i) (w i) (hw i)
      (s2c_subschemeι (B i.castSucc) (D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
        D i.castSucc ⟨2 * i.val + 1, by omega⟩))
  · intro n
    exact persistence_retained_relative_cohomology_comparison S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder i n

example := PersistenceChecks.check_persistence_pair_comparison

/-- The actual retained exceptional pair has unique primitive relative lifts.
Source: Schoen (1988), Lemma 2.8; Hatcher, Algebraic Topology, sections 2.1 and 3.1.
HC no distance; AV milestone no distance. -/
theorem persistence_retained_exact_aux
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
    (C₀ J : Over (Spec ↧ℂ))
    [IsIntegral C₀.left] [Smooth C₀.hom] [IsProjective C₀.hom]
    [GrpObj J] [IsCommMonObj J] [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    (aut : g32p_G → (J ⟶ J)) (P : g32p_Part J aut S)
    (qC : C₀ ⟶ Y) (jC : C₀ ⟶ J)
    (eC : C ≃ₜ ComplexPoint C₀) (eZ : rsq_Quot S.H C ≃ₜ ComplexPoint Z)
    (hqC : ∀ x, Point.map qC (eC x) = eY (rsq_proj S.χ.ker C x))
    (hpC : ∀ z, Point.map p₀ (eY z) = eZ (rsq_coarsen S.χ.ker z))
    (hχ : ∀ u : S.H, e (QuotientGroup.mk u) = S.χ u)
    (hjC : Function.Bijective (homPullback jC 1))
    (primitive : HQ P.P 1 ≃ₗ[ℚ] LinearMap.ker
      (Polynomial.aeval (homPullback (a (e.symm (Multiplicative.ofAdd 1))) 1)
        (Polynomial.cyclotomic S.m ℚ)))
    (hprimitive : ∀ v, homPullback qC 1 (primitive v) =
      homPullback jC 1 (homPullback P.proj 1 v))
    (hscalar : ∀ (u : S.H) v,
      homPullback (a ((QuotientGroup.mk u)⁻¹)) 1 (primitive v) =
        (primitive (cyc_scalar P.act.cyc_coordinates (g32p_fieldValue S u) v) : HQ Y 1))
    (hrank : Module.finrank ℚ (LinearMap.ker
      (Polynomial.aeval (homPullback (a (e.symm (Multiplicative.ofAdd 1))) 1)
        (Polynomial.cyclotomic S.m ℚ))) = 2 * P.k * Nat.totient S.m)
    (hselected : h + 1 = 2 * P.k)
    [ChartedSpace ℂ (rsq_Quot S.H C)]
    [IsManifold 𝓘(ℂ, ℂ) ω (rsq_Quot S.H C)]
    (hgenus : 2 * P.k + 2 = 2 * Module.finrank ℂ (b3_HolForm ℂ (rsq_Quot S.H C)) +
      (g32p_exponents S).length)
    (hExceptionalPrimitive : ∀ i : Fin r,
    let I := D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
      D i.castSucc ⟨2 * i.val + 1, by omega⟩
    let K := s2c_subscheme (B i.castSucc) I
    let kι := s2c_subschemeι (B i.castSucc) I
    let E := s2c_exceptional (b i) I
    let j : E ⟶ B i.succ := pullback.fst (b i) kι
    let p : E ⟶ K := pullback.snd (b i) kι
    let β := s2b_normalizationMap (B i.succ) (η i.succ)
    ∀ (n : ℕ) (ζ : ℂ), IsPrimitiveRoot ζ S.m →
      ∀ v : AlgebraicTopology.Singular.Cohomology ℂ
        (TopCat.of (ComplexPoint (s2b_preimage β j))) n,
        s2b_preimageCohomologyDeck β j (d i.succ) (hd i.succ) n v = ζ • v → v = 0)
    (i : Fin r) :
    let I := D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
      D i.castSucc ⟨2 * i.val + 1, by omega⟩
    let kι := s2c_subschemeι (B i.castSucc) I
    let E := s2c_exceptional (b i) I
    let j : E ⟶ B i.succ := pullback.fst (b i) kι
    let β := s2b_normalizationMap (B i.succ) (η i.succ)
    let βprev := s2b_normalizationMap (B i.castSucc) (η i.castSucc)
    let X := s2b_normalizationOver (B i.succ) (η i.succ)
    let A := Set.range (Point.map (s2b_toCover β j))
    let PX := TopPair.ofSubset (X := TopCat.of (ComplexPoint X)) A
    (∀ (n : ℕ) (ζ : ℂ), IsPrimitiveRoot ζ S.m →
      ∀ v : AlgebraicTopology.Singular.Cohomology ℂ
        (TopCat.of (ComplexPoint (s2b_preimage βprev kι))) n,
        s2b_preimageCohomologyDeck βprev kι (d i.castSucc) (hd i.castSucc) n v = ζ • v →
          v = 0) ∧
    ∃ Drel : PX ⟶ PX,
      TopPair.Hom.fst Drel = TopCat.ofHom (Point.continuousMap (d i.succ)) ∧
      ∀ (n : ℕ) (ζ : ℂ), IsPrimitiveRoot ζ S.m →
        ∀ v : AlgebraicTopology.Singular.Cohomology ℂ
          (TopCat.of (ComplexPoint X)) n,
          s2e_pullback ℂ (d i.succ) n v = ζ • v →
          ∃! u : AlgebraicTopology.Singular.RelativeCohomology ℂ PX n,
            AlgebraicTopology.Singular.relativeCohomologyMap ℂ n Drel u = ζ • u ∧
            AlgebraicTopology.Singular.relativeCohomologyToAbsolute ℂ PX n u = v := by
  refine ⟨?_, persistence_retained_exceptional_pair_lifts S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder C₀ J aut P qC jC eC eZ hqC hpC hχ hjC primitive hprimitive hscalar hrank hselected hgenus hExceptionalPrimitive i⟩
  exact persistence_retained_centre_primitive_vanishing S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder i

example := PersistenceChecks.check_persistence_retained_exact

/-- Each actual normalization transition has unique primitive pullback preimages.
Source: Schoen (1988), Lemma 2.8; Hatcher, Algebraic Topology, sections 2.1 and 3.1.
HC no distance; AV milestone no distance. -/
theorem persistence_retained_preimage_aux
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
    (C₀ J : Over (Spec ↧ℂ))
    [IsIntegral C₀.left] [Smooth C₀.hom] [IsProjective C₀.hom]
    [GrpObj J] [IsCommMonObj J] [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    (aut : g32p_G → (J ⟶ J)) (P : g32p_Part J aut S)
    (qC : C₀ ⟶ Y) (jC : C₀ ⟶ J)
    (eC : C ≃ₜ ComplexPoint C₀) (eZ : rsq_Quot S.H C ≃ₜ ComplexPoint Z)
    (hqC : ∀ x, Point.map qC (eC x) = eY (rsq_proj S.χ.ker C x))
    (hpC : ∀ z, Point.map p₀ (eY z) = eZ (rsq_coarsen S.χ.ker z))
    (hχ : ∀ u : S.H, e (QuotientGroup.mk u) = S.χ u)
    (hjC : Function.Bijective (homPullback jC 1))
    (primitive : HQ P.P 1 ≃ₗ[ℚ] LinearMap.ker
      (Polynomial.aeval (homPullback (a (e.symm (Multiplicative.ofAdd 1))) 1)
        (Polynomial.cyclotomic S.m ℚ)))
    (hprimitive : ∀ v, homPullback qC 1 (primitive v) =
      homPullback jC 1 (homPullback P.proj 1 v))
    (hscalar : ∀ (u : S.H) v,
      homPullback (a ((QuotientGroup.mk u)⁻¹)) 1 (primitive v) =
        (primitive (cyc_scalar P.act.cyc_coordinates (g32p_fieldValue S u) v) : HQ Y 1))
    (hrank : Module.finrank ℚ (LinearMap.ker
      (Polynomial.aeval (homPullback (a (e.symm (Multiplicative.ofAdd 1))) 1)
        (Polynomial.cyclotomic S.m ℚ))) = 2 * P.k * Nat.totient S.m)
    (hselected : h + 1 = 2 * P.k)
    [ChartedSpace ℂ (rsq_Quot S.H C)]
    [IsManifold 𝓘(ℂ, ℂ) ω (rsq_Quot S.H C)]
    (hgenus : 2 * P.k + 2 = 2 * Module.finrank ℂ (b3_HolForm ℂ (rsq_Quot S.H C)) +
      (g32p_exponents S).length)
    (hExceptionalPrimitive : ∀ i : Fin r,
    let I := D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
      D i.castSucc ⟨2 * i.val + 1, by omega⟩
    let K := s2c_subscheme (B i.castSucc) I
    let kι := s2c_subschemeι (B i.castSucc) I
    let E := s2c_exceptional (b i) I
    let j : E ⟶ B i.succ := pullback.fst (b i) kι
    let p : E ⟶ K := pullback.snd (b i) kι
    let β := s2b_normalizationMap (B i.succ) (η i.succ)
    ∀ (n : ℕ) (ζ : ℂ), IsPrimitiveRoot ζ S.m →
      ∀ v : AlgebraicTopology.Singular.Cohomology ℂ
        (TopCat.of (ComplexPoint (s2b_preimage β j))) n,
        s2b_preimageCohomologyDeck β j (d i.succ) (hd i.succ) n v = ζ • v → v = 0)
 :
    ∀ (i : Fin r) (n : ℕ) (ζ : ℂ), IsPrimitiveRoot ζ S.m →
      ∀ v : AlgebraicTopology.Singular.Cohomology ℂ
        (TopCat.of (ComplexPoint (s2b_normalizationOver (B i.succ) (η i.succ)))) n,
        s2e_pullback ℂ (d i.succ) n v = ζ • v →
        ∃! u : AlgebraicTopology.Singular.Cohomology ℂ
          (TopCat.of (ComplexPoint (s2b_normalizationOver (B i.castSucc) (η i.castSucc)))) n,
          s2e_pullback ℂ (d i.castSucc) n u = ζ • u ∧ s2e_pullback ℂ (w i) n u = v := by
  intro i n ζ hζ v hv
  have hc := persistence_pair_comparison_aux S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder i
  have he := persistence_retained_exact_aux S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder C₀ J aut P qC jC eC eZ hqC hpC hχ hjC primitive hprimitive hscalar hrank hselected hgenus hExceptionalPrimitive i
  let I := D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
    D i.castSucc ⟨2 * i.val + 1, by omega⟩
  let kι := s2c_subschemeι (B i.castSucc) I
  let j : s2c_exceptional (b i) I ⟶ B i.succ := pullback.fst (b i) kι
  let β := s2b_normalizationMap (B i.succ) (η i.succ)
  let βprev := s2b_normalizationMap (B i.castSucc) (η i.castSucc)
  let A := Set.range (Point.map (s2b_toCover βprev kι))
  let A' := Set.range (Point.map (s2b_toCover β j))
  let PX := TopPair.ofSubset (X := TopCat.of (ComplexPoint
    (s2b_normalizationOver (B i.succ) (η i.succ)))) A'
  let PY := TopPair.ofSubset (X := TopCat.of (ComplexPoint
    (s2b_normalizationOver (B i.castSucc) (η i.castSucc)))) A
  have hs : Point.map (w i) ⁻¹' A = A' := hc.2.1
  let f : PX ⟶ PY := TopPair.ofSubsetHom
    (TopCat.ofHom (Point.continuousMap (w i))) (by
      intro x hx
      change x ∈ Point.map (w i) ⁻¹' A
      rw [hs]
      exact hx)
  obtain ⟨dX, hdX, hX⟩ := he.2
  haveI : IsClosedImmersion kι.left := inferInstanceAs (IsClosedImmersion I.subschemeι)
  obtain ⟨dY, hdY, hY⟩ := persistence_preimage_pair_lifts ℂ βprev kι
    (d i.castSucc) (hd i.castSucc) S.m (by have := S.three_le; omega)
    (horder i.castSucc) (fun z hz t u hu => he.1 t z hz u hu)
  have hf : dX ≫ f = f ≫ dY := by
    apply persistence_pair_hom_ext
    change TopPair.Hom.fst dX ≫ TopPair.Hom.fst f =
      TopPair.Hom.fst f ≫ TopPair.Hom.fst dY
    rw [hdX, hdY]
    apply TopCat.ext
    intro x
    change (x ≫ d i.succ) ≫ w i = (x ≫ w i) ≫ d i.castSucc
    rw [Category.assoc, hdw, Category.assoc]
  have hb : Function.Bijective (relativeCohomologyMap ℂ n f) :=
    persistence_relative_bijective_of_equal_source_subset ℂ
      (TopCat.ofHom (Point.continuousMap (w i))) A A' hs _ n (hc.2.2.2 n)
  have hv' : cohomologyMap ℂ n (TopPair.Hom.fst dX) v = ζ • v := by
    rw [hdX]
    exact hv
  have hresult := persistence_preimage_of_unique_relative_lifts ℂ PX PY dX dY f hf
    ζ n hb (by
      intro u hu
      rw [hdX] at hu
      exact hX n ζ hζ u hu)
      (by
        intro u hu
        rw [hdY] at hu
        exact hY n ζ hζ u hu) v hv'
  rw [hdY] at hresult
  exact hresult

example := PersistenceChecks.check_persistence_retained_preimage

/-- The actual total tower map transports a nonzero weighted class in every degree.
Source: Schoen (1988), Lemma 2.8; Hatcher, Algebraic Topology, sections 2.1 and 3.1.
HC no distance; AV milestone no distance. -/
theorem persistence_retained_transport_aux
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
    (C₀ J : Over (Spec ↧ℂ))
    [IsIntegral C₀.left] [Smooth C₀.hom] [IsProjective C₀.hom]
    [GrpObj J] [IsCommMonObj J] [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    (aut : g32p_G → (J ⟶ J)) (P : g32p_Part J aut S)
    (qC : C₀ ⟶ Y) (jC : C₀ ⟶ J)
    (eC : C ≃ₜ ComplexPoint C₀) (eZ : rsq_Quot S.H C ≃ₜ ComplexPoint Z)
    (hqC : ∀ x, Point.map qC (eC x) = eY (rsq_proj S.χ.ker C x))
    (hpC : ∀ z, Point.map p₀ (eY z) = eZ (rsq_coarsen S.χ.ker z))
    (hχ : ∀ u : S.H, e (QuotientGroup.mk u) = S.χ u)
    (hjC : Function.Bijective (homPullback jC 1))
    (primitive : HQ P.P 1 ≃ₗ[ℚ] LinearMap.ker
      (Polynomial.aeval (homPullback (a (e.symm (Multiplicative.ofAdd 1))) 1)
        (Polynomial.cyclotomic S.m ℚ)))
    (hprimitive : ∀ v, homPullback qC 1 (primitive v) =
      homPullback jC 1 (homPullback P.proj 1 v))
    (hscalar : ∀ (u : S.H) v,
      homPullback (a ((QuotientGroup.mk u)⁻¹)) 1 (primitive v) =
        (primitive (cyc_scalar P.act.cyc_coordinates (g32p_fieldValue S u) v) : HQ Y 1))
    (hrank : Module.finrank ℚ (LinearMap.ker
      (Polynomial.aeval (homPullback (a (e.symm (Multiplicative.ofAdd 1))) 1)
        (Polynomial.cyclotomic S.m ℚ))) = 2 * P.k * Nat.totient S.m)
    (hselected : h + 1 = 2 * P.k)
    [ChartedSpace ℂ (rsq_Quot S.H C)]
    [IsManifold 𝓘(ℂ, ℂ) ω (rsq_Quot S.H C)]
    (hgenus : 2 * P.k + 2 = 2 * Module.finrank ℂ (b3_HolForm ℂ (rsq_Quot S.H C)) +
      (g32p_exponents S).length)
    (hExceptionalPrimitive : ∀ i : Fin r,
    let I := D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
      D i.castSucc ⟨2 * i.val + 1, by omega⟩
    let K := s2c_subscheme (B i.castSucc) I
    let kι := s2c_subschemeι (B i.castSucc) I
    let E := s2c_exceptional (b i) I
    let j : E ⟶ B i.succ := pullback.fst (b i) kι
    let p : E ⟶ K := pullback.snd (b i) kι
    let β := s2b_normalizationMap (B i.succ) (η i.succ)
    ∀ (n : ℕ) (ζ : ℂ), IsPrimitiveRoot ζ S.m →
      ∀ v : AlgebraicTopology.Singular.Cohomology ℂ
        (TopCat.of (ComplexPoint (s2b_preimage β j))) n,
        s2b_preimageCohomologyDeck β j (d i.succ) (hd i.succ) n v = ζ • v → v = 0)
    (W : Over (Spec ↧ℂ))
    (eWr : s2b_normalizationOver (B (Fin.last r)) (η (Fin.last r)) ≅ W)
    (n : ℕ)
    (cl : AlgebraicTopology.Singular.Cohomology ℚ
      (TopCat.of (ComplexPoint W)) n)
    (ζ : ℂ) (hζ : IsPrimitiveRoot ζ S.m)
    (hnonzero : let δ := eWr.inv ≫ d (Fin.last r) ≫ eWr.hom
      s2e_weightedSum S.m (fun t : ZMod S.m => ζ ^ t.val)
        (fun t : Fin S.m => TensorProduct.tmul ℚ (1 : ℂ)
          (s2e_pullback ℚ ((End.of δ ^ (S.m - t.val)).asHom) n cl)) ≠ 0) :
    let δ := eWr.inv ≫ d (Fin.last r) ≫ eWr.hom
    let v := s2e_weightedSum S.m (fun t : ZMod S.m => ζ ^ t.val)
      (fun t : Fin S.m => TensorProduct.tmul ℚ (1 : ℂ)
        (s2e_pullback ℚ ((End.of δ ^ (S.m - t.val)).asHom) n cl))
    let φ := eWr.inv ≫ s2e_towerTotalMap
      (fun i => s2b_normalizationOver (B i) (η i)) eW.hom w (Fin.last r)
    ∃! u : ℂ ⊗[ℚ] AlgebraicTopology.Singular.Cohomology ℚ
      (TopCat.of (ComplexPoint W₀)) n,
      u ≠ 0 ∧
      (s2e_pullback ℚ d₀ n).baseChange ℂ u = ζ⁻¹ • u ∧
      (s2e_pullback ℚ φ n).baseChange ℂ u = v := by
  dsimp only
  letI : Module.Finite ℚ (Homology ℚ (TopCat.of (ComplexPoint W₀)) n) :=
    persistence_initial_quotient_homology S Y W₀ a e ha1 hamul (h + 1) q₀ hqsurj hqinv hq n
  have hδ : End.of (eWr.inv ≫ d (Fin.last r) ≫ eWr.hom) ^ S.m = 1 := by
    have he := congrArg eWr.conj (horder (Fin.last r))
    rw [map_pow, map_one] at he
    exact he
  apply persistence_weighted_transport_of_complex_preimages W₀ W d₀
    (eWr.inv ≫ d (Fin.last r) ≫ eWr.hom)
    (eWr.inv ≫ s2e_towerTotalMap
      (fun i => s2b_normalizationOver (B i) (η i)) eW.hom w (Fin.last r))
    S.m hδ n ζ hζ ?_ cl hnonzero
  intro v hv
  apply persistence_tower_terminal_cohomology_preimages ℂ
    (fun i => s2b_normalizationOver (B i) (η i)) W₀ W eW w d d₀ hdinit hdw
    eWr n ζ⁻¹ ?_ v hv
  intro i v hv
  exact persistence_retained_preimage_aux S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj
    p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh
    q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀
    htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder
    C₀ J aut P qC jC eC eZ hqC hpC hχ hjC primitive hprimitive hscalar hrank hselected
    hgenus hExceptionalPrimitive i n ζ⁻¹ hζ.inv v hv

example := PersistenceChecks.check_persistence_retained_transport

/-- Finite order and all-degree subspace vanishing give unique relative eigen lifts.
Source: Hatcher, Algebraic Topology, section 3.1; Serre, Linear Representations of Finite Groups, section 2.6.
HC no distance; AV milestone no distance. -/
theorem persistence_primitive_exact_aux
    (K : Type) [Field K] [CharZero K] (X : TopPair.{0}) (d : X ⟶ X)
    (m : ℕ) (hm : 0 < m) (hd : End.of (TopPair.Hom.fst d) ^ m = 1)
    (ζ : K) (hvanish : ∀ n (v : Cohomology K X.snd n),
      cohomologyMap K n (TopPair.Hom.snd d) v = ζ • v → v = 0)
    (n : ℕ) (v : Cohomology K X.fst n)
    (hv : cohomologyMap K n (TopPair.Hom.fst d) v = ζ • v) :
    ∃! u : RelativeCohomology K X n,
      relativeCohomologyMap K n d u = ζ • u ∧
      relativeCohomologyToAbsolute K X n u = v := by
  exact persistence_pair_primitive_lift K X d m hm hd ζ hvanish n v hv

example := PersistenceChecks.check_persistence_primitive_exact

/-- Pair pullback preserves the restriction and support-forgetting squares.
Source: Schoen (1988), Lemma 2.8; Hatcher, Algebraic Topology, sections 2.1 and 3.1.
HC no distance; AV milestone no distance. -/
theorem persistence_pair_squares_aux
    (K : Type) [Field K] {X Y : TopCat.{0}} (f : X ⟶ Y)
    (A : Set Y) (n : ℕ) :
    (∀ u : RelativeCohomology K (TopPair.ofSubset A) n,
      relativeCohomologyToAbsolute K (TopPair.ofSubset (f ⁻¹' A)) n
        (persistenceRelativePullback K f A n u) =
      cohomologyMap K n f (relativeCohomologyToAbsolute K (TopPair.ofSubset A) n u)) ∧
    (∀ v : Cohomology K Y n,
      cohomologyMap K n (TopPair.ofSubset (f ⁻¹' A)).map (cohomologyMap K n f v) =
      cohomologyMap K n (TopPair.Hom.snd (persistencePairMap f A))
        (cohomologyMap K n (TopPair.ofSubset A).map v)) ∧
    (∀ Z : Set Y, ∀ u : CohomologyWithSupport K Y Z n,
      cohomologyMap K n f (forgetSupport K Y Z n u) =
      forgetSupport K X (f ⁻¹' Z) n (cohomologyWithSupportMap K n f Z u)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro u
    have hdual := congrArg HomologicalComplex.linearDualMap
      (TopPair.Homotopy.relativeChainProjection_naturality (R := K)
        (persistencePairMap f A))
    rw [HomologicalComplex.linearDualMap_comp, HomologicalComplex.linearDualMap_comp] at hdual
    have hhom := congrArg (fun t => HomologicalComplex.homologyMap t n) hdual
    rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hhom
    exact ConcreteCategory.congr_hom hhom u
  · intro v
    have h := cohomologyMap_comp K n
      (TopPair.ofSubset (f ⁻¹' A)).map f
    have h' := cohomologyMap_comp K n
      (TopPair.Hom.snd (persistencePairMap f A)) (TopPair.ofSubset A).map
    exact (LinearMap.congr_fun h v).symm.trans (LinearMap.congr_fun h' v)
  · intro Z u
    exact cohomologyMap_forgetSupport K n f Z u

example := PersistenceChecks.check_persistence_pair_squares

end HodgeLean.Foundations.QuotientDuality
