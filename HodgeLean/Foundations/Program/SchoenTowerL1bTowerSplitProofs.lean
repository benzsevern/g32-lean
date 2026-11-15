import HodgeLean.Foundations.Program.SchoenTowerL1bFiniteBaseCoordinates
import HodgeLean.Foundations.Program.SchoenTowerL1bTowerStepLocal
import HodgeLean.Foundations.Program.SchoenTowerInertiaSuppliers
import HodgeLean.Foundations.Program.SchoenTowerGeometryDefs
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Field.Subfield.Basic
import HodgeLean.Foundations.Program.SchoenTowerL1bCoordinatePairOrder

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedVariables false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Adapters
open scoped BigOperators Manifold ContDiff OnePoint
namespace HodgeLean.Foundations.Program

/-- Simultaneous coordinates for every remaining branch through each initial point, with absent branches removed from the neighborhood.
Source: Schoen (1988), Lemma 2.2, printed pp. 13–14; common symmetric quotient chart and etale generator extension. -/
theorem s2v_l1b_tower_initial_coordinates_aux
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
 :
    ∀ x : ComplexPoint (B (0 : Fin (r + 1))),
      ∃ (U : (B (0 : Fin (r + 1))).left.affineOpens)
        (z : Fin (h + 1) → Γ((B (0 : Fin (r + 1))).left, U))
        (f : {t : Fin (2 * r) // 2 * ((0 : Fin (r + 1))).val ≤ t.val ∧
          x.underlying ∈ (D (0 : Fin (r + 1)) t).support} ↪ Fin (h + 1)),
        x.underlying ∈ U.1 ∧
        (MvPolynomial.eval₂Hom ((B (0 : Fin (r + 1))).hom.appLE ⊤ U.1 le_top).hom z).Etale ∧
        (∀ t, (D (0 : Fin (r + 1)) t.val).ideal U = Ideal.span {z (f t)}) ∧
        (∀ t : Fin (2 * r), 2 * ((0 : Fin (r + 1))).val ≤ t.val →
          x.underlying ∉ (D (0 : Fin (r + 1)) t).support → (D (0 : Fin (r + 1)) t).ideal U = ⊤) := by
  intro x
  let bb (t : Fin (2 * r)) := Point.map p₀ (eY (y (σ t)))
  have hbb : Function.Injective bb := fun t s H => σ.injective (hy H)
  obtain ⟨U, z, f, hx, hEt, hI, htop⟩ :=
    s2v_l1b_finite_base_coordinates Z B₀ (B 0) hdimZ h γ hγsurj hγinv hγ
      (2 * r) bb hbb e₀ (D 0) hD₀ x
  let f' : {t : Fin (2 * r) // 2 * ((0 : Fin (r + 1))).val ≤ t.val ∧
      x.underlying ∈ (D (0 : Fin (r + 1)) t).support} ↪ Fin (h + 1) :=
    ⟨fun t => f ⟨t.val, t.property.2⟩, by
      intro t s H
      have Hval : t.val = s.val := Subtype.mk.inj (f.injective H)
      exact Subtype.ext Hval⟩
  exact ⟨U, z, f', hx, hEt, (fun t => hI ⟨t.val, t.property.2⟩),
    (fun t _ ht => htop t ht)⟩

/-- Simultaneous coordinates for remaining branches persist through the next retained blowup, including its exceptional points.
Source: Hartshorne, Algebraic Geometry, II.7.14; Schoen (1988), Lemma 2.2, printed pp. 13–14; etale blowup coordinate cover and branch transform. -/
theorem s2v_l1b_tower_step_aux
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
    (k : Fin r)
    (hcoords : ∀ x : ComplexPoint (B k.castSucc),
      ∃ (U : (B k.castSucc).left.affineOpens)
        (z : Fin (h + 1) → Γ((B k.castSucc).left, U))
        (f : {t : Fin (2 * r) // 2 * (k.castSucc).val ≤ t.val ∧
          x.underlying ∈ (D k.castSucc t).support} ↪ Fin (h + 1)),
        x.underlying ∈ U.1 ∧
        (MvPolynomial.eval₂Hom ((B k.castSucc).hom.appLE ⊤ U.1 le_top).hom z).Etale ∧
        (∀ t, (D k.castSucc t.val).ideal U = Ideal.span {z (f t)}) ∧
        (∀ t : Fin (2 * r), 2 * (k.castSucc).val ≤ t.val →
          x.underlying ∉ (D k.castSucc t).support → (D k.castSucc t).ideal U = ⊤)) :
    ∀ x : ComplexPoint (B k.succ),
      ∃ (U : (B k.succ).left.affineOpens)
        (z : Fin (h + 1) → Γ((B k.succ).left, U))
        (f : {t : Fin (2 * r) // 2 * (k.succ).val ≤ t.val ∧
          x.underlying ∈ (D k.succ t).support} ↪ Fin (h + 1)),
        x.underlying ∈ U.1 ∧
        (MvPolynomial.eval₂Hom ((B k.succ).hom.appLE ⊤ U.1 le_top).hom z).Etale ∧
        (∀ t, (D k.succ t.val).ideal U = Ideal.span {z (f t)}) ∧
        (∀ t : Fin (2 * r), 2 * (k.succ).val ≤ t.val →
          x.underlying ∉ (D k.succ t).support → (D k.succ t).ideal U = ⊤) := by
  classical
  intro x
  obtain ⟨U, z, f, hxU, het, hD, habs⟩ := hcoords (Point.map (b k) x)
  let aₖ : Fin (2 * r) := ⟨2 * k.val, by omega⟩
  let bₖ : Fin (2 * r) := ⟨2 * k.val + 1, by omega⟩
  have H := s2v_l1b_tower_step_local (B k.castSucc) (B k.succ) (b k)
    (D k.castSucc) (fun t => 2 * k.val ≤ t.val) (fun t => 2 * (k.val + 1) ≤ t.val)
    (by intro t ht; omega) aₖ bₖ (by intro he; have := congrArg Fin.val he; dsimp [aₖ, bₖ] at this; omega)
    (by dsimp [aₖ]; omega) (by dsimp [bₖ]; omega)
    (by dsimp [aₖ]; omega) (by dsimp [bₖ]; omega)
    (hcartier k) (hblowup k) x U z f hxU het hD habs
  have hDsucc : D k.succ = fun t => s2c_strictTransform (b k).left
      (D k.castSucc t) (D k.castSucc aₖ ⊔ D k.castSucc bₖ) :=
    funext (htransform k)
  rw [hDsucc]
  exact H

/-- Stage-zero coordinates and their successor transport supply coordinates at every finite stage.
Source: Finite induction on the stage index. -/
theorem s2v_l1b_tower_induction_aux
    (r h : ℕ) (B : Fin (r + 1) → Over (Spec ↧ℂ))
    (D : ∀ i, Fin (2 * r) → (B i).left.IdealSheafData)
    (hinit : ∀ x : ComplexPoint (B (0 : Fin (r + 1))),
      ∃ (U : (B (0 : Fin (r + 1))).left.affineOpens)
        (z : Fin (h + 1) → Γ((B (0 : Fin (r + 1))).left, U))
        (f : {t : Fin (2 * r) // 2 * ((0 : Fin (r + 1))).val ≤ t.val ∧
          x.underlying ∈ (D (0 : Fin (r + 1)) t).support} ↪ Fin (h + 1)),
        x.underlying ∈ U.1 ∧
        (MvPolynomial.eval₂Hom ((B (0 : Fin (r + 1))).hom.appLE ⊤ U.1 le_top).hom z).Etale ∧
        (∀ t, (D (0 : Fin (r + 1)) t.val).ideal U = Ideal.span {z (f t)}) ∧
        (∀ t : Fin (2 * r), 2 * ((0 : Fin (r + 1))).val ≤ t.val →
          x.underlying ∉ (D (0 : Fin (r + 1)) t).support → (D (0 : Fin (r + 1)) t).ideal U = ⊤))
    (hstep : ∀ k : Fin r,
      (∀ x : ComplexPoint (B k.castSucc),
      ∃ (U : (B k.castSucc).left.affineOpens)
        (z : Fin (h + 1) → Γ((B k.castSucc).left, U))
        (f : {t : Fin (2 * r) // 2 * (k.castSucc).val ≤ t.val ∧
          x.underlying ∈ (D k.castSucc t).support} ↪ Fin (h + 1)),
        x.underlying ∈ U.1 ∧
        (MvPolynomial.eval₂Hom ((B k.castSucc).hom.appLE ⊤ U.1 le_top).hom z).Etale ∧
        (∀ t, (D k.castSucc t.val).ideal U = Ideal.span {z (f t)}) ∧
        (∀ t : Fin (2 * r), 2 * (k.castSucc).val ≤ t.val →
          x.underlying ∉ (D k.castSucc t).support → (D k.castSucc t).ideal U = ⊤)) →
      ∀ x : ComplexPoint (B k.succ),
      ∃ (U : (B k.succ).left.affineOpens)
        (z : Fin (h + 1) → Γ((B k.succ).left, U))
        (f : {t : Fin (2 * r) // 2 * (k.succ).val ≤ t.val ∧
          x.underlying ∈ (D k.succ t).support} ↪ Fin (h + 1)),
        x.underlying ∈ U.1 ∧
        (MvPolynomial.eval₂Hom ((B k.succ).hom.appLE ⊤ U.1 le_top).hom z).Etale ∧
        (∀ t, (D k.succ t.val).ideal U = Ideal.span {z (f t)}) ∧
        (∀ t : Fin (2 * r), 2 * (k.succ).val ≤ t.val →
          x.underlying ∉ (D k.succ t).support → (D k.succ t).ideal U = ⊤))
    (k : Fin (r + 1)) :
    ∀ x : ComplexPoint (B k),
      ∃ (U : (B k).left.affineOpens)
        (z : Fin (h + 1) → Γ((B k).left, U))
        (f : {t : Fin (2 * r) // 2 * (k).val ≤ t.val ∧
          x.underlying ∈ (D k t).support} ↪ Fin (h + 1)),
        x.underlying ∈ U.1 ∧
        (MvPolynomial.eval₂Hom ((B k).hom.appLE ⊤ U.1 le_top).hom z).Etale ∧
        (∀ t, (D k t.val).ideal U = Ideal.span {z (f t)}) ∧
        (∀ t : Fin (2 * r), 2 * (k).val ≤ t.val →
          x.underlying ∉ (D k t).support → (D k t).ideal U = ⊤) := by
  induction k using Fin.induction with
  | zero => exact hinit
  | succ k ih => exact hstep k ih

end HodgeLean.Foundations.Program
