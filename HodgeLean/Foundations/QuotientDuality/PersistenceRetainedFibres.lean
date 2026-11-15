import HodgeLean.Foundations.QuotientDuality.PersistenceRetainedGeometry
import HodgeLean.Foundations.QuotientDuality.PersistenceNormalizationFibres

/-! Off-centre fibres from the original retained tower inputs. -/

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

theorem persistence_retained_off_centre_fibre
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
    let βprev := s2b_normalizationMap (B i.castSucc) (η i.castSucc)
    let A := Set.range (Point.map (s2b_toCover βprev kι))
    ∀ y : ComplexPoint (s2b_normalizationOver (B i.castSucc) (η i.castSucc)),
      y ∉ A → ∃! x, Point.map (w i) x = y := by
  dsimp only
  let I := D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
    D i.castSucc ⟨2 * i.val + 1, by omega⟩
  have hdom : IsDominant (η 0) := s2v_initial_genericSource_dominant
    p₀ hpsurj (h + 1) q₀ γ hγsurj β₀ hβ₀ e₀ (η 0) hη₀
  haveI : ∀ j, IsDominant (η j) := s2v_i2b_tower_genericSource_dominant B b
    (fun j => D j.castSucc ⟨2 * j.val, by omega⟩ ⊔
      D j.castSucc ⟨2 * j.val + 1, by omega⟩)
    hcartier hblowup η hη hdom
  intro y hy
  exact persistence_normalization_unique_complex_fibre_off_range (B i.succ) (B i.castSucc)
    (η i.succ) (η i.castSucc) (b i) (hη i) I
    (s2e_blowup_universal_property_on_schemes (b i) I (hblowup i)) (w i) (hw i) y hy

end HodgeLean.Foundations.QuotientDuality
