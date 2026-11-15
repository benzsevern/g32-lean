import HodgeLean.Foundations.Program.SchoenTowerL1bTowerGenerators
import HodgeLean.Foundations.Program.SchoenTowerL1bFlatRegularPair
import HodgeLean.Foundations.Program.SchoenTowerL1bComparisonIso
import HodgeLean.Foundations.Program.SchoenTowerL1bComparisonSections
import HodgeLean.Foundations.Program.SchoenTowerInertiaSuppliers
import HodgeLean.Foundations.Program.SchoenTowerGeometryDefs
import HodgeLean.Foundations.Program.SchoenTowerL1bModelIdeal
import HodgeLean.Foundations.Program.SchoenTowerL1bSourceDescent
import HodgeLean.Foundations.Program.SchoenTowerL1bModelDescent
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Field.Subfield.Basic

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

/-- The actual selected branch ideals have generators regular in both orders near the point.
Source: Schoen (1988), Lemma 2.2, printed pp. 13–14, successive transverse branch intersections. -/
theorem s2v_l1b_charts_tower_coordinates_aux
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
    (x : ComplexPoint (B i.castSucc))
    (hx₁ : x.left (IsLocalRing.closedPoint ℂ) ∈
      (D i.castSucc ⟨2 * i.val, by omega⟩).support)
    (hx₂ : x.left (IsLocalRing.closedPoint ℂ) ∈
      (D i.castSucc ⟨2 * i.val + 1, by omega⟩).support)
    (havoid : ∀ t : Fin (2 * r), t.val ≠ 2 * i.val → t.val ≠ 2 * i.val + 1 →
      x.left (IsLocalRing.closedPoint ℂ) ∉ (D i.castSucc t).support) :
    ∃ (U : (B i.castSucc).left.affineOpens)
      (u v : Γ((B i.castSucc).left, U)),
      x.left (IsLocalRing.closedPoint ℂ) ∈ U.1 ∧
      (D i.castSucc ⟨2 * i.val, by omega⟩).ideal U = Ideal.span {u} ∧
      (D i.castSucc ⟨2 * i.val + 1, by omega⟩).ideal U = Ideal.span {v} ∧
      IsRegular v ∧ IsRegular (Ideal.Quotient.mk (Ideal.span {v}) u) ∧
      IsRegular u ∧ IsRegular (Ideal.Quotient.mk (Ideal.span {u}) v) := by
  obtain ⟨U, hn, z, hxU, het, hu, hv⟩ :=
    s2v_l1b_tower_branch_generators S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder i x hx₁ hx₂ havoid
  have h01 : (⟨0, by omega⟩ : Fin (h + 1)) ≠ ⟨1, by omega⟩ := by
    intro heq
    have H : (0 : ℕ) = 1 := congrArg Fin.val heq
    omega
  obtain ⟨hvreg, hureg⟩ := s2v_l1b_etale_coordinate_pair
    ((B i.castSucc).hom.appLE ⊤ U.1 le_top).hom z het _ _ h01
  obtain ⟨hureg', hvreg'⟩ := s2v_l1b_etale_coordinate_pair
    ((B i.castSucc).hom.appLE ⊤ U.1 le_top).hom z het _ _ h01.symm
  exact ⟨U, z ⟨0, by omega⟩, z ⟨1, by omega⟩,
    hxU, hu, hv, hvreg, hureg, hureg', hvreg'⟩

/-- The regular binomial charts descend to a model with unique lifts from arbitrary sources.
Source: Hartshorne, Algebraic Geometry, II.7.14; the reciprocal transition in
SchoenTowerL1bChartOverlap and source gluing in SchoenTowerL1bSourceDescent. -/
theorem s2v_l1b_charts_overlap_descent_aux
    (R : Type) [CommRing R] (u v : R)
    (hv : IsRegular v) (hu : IsRegular (Ideal.Quotient.mk (Ideal.span {v}) u))
    (hu' : IsRegular u) (hv' : IsRegular (Ideal.Quotient.mk (Ideal.span {u}) v)) :
    ∃ (M : Scheme)
      (j₁ : Spec (CommRingCat.of (s2v_L1bChart u v)) ⟶ M)
      (j₂ : Spec (CommRingCat.of (s2v_L1bChart v u)) ⟶ M)
      (π : M ⟶ Spec (CommRingCat.of R)),
      IsOpenImmersion j₁ ∧ IsOpenImmersion j₂ ∧
      (∀ z : M, (∃ a, j₁ a = z) ∨ ∃ a, j₂ a = z) ∧
      j₁ ≫ π = Spec.map (CommRingCat.ofHom
        ((Ideal.Quotient.mk (Ideal.span {Polynomial.C u - Polynomial.X * Polynomial.C v})).comp Polynomial.C)) ∧
      j₂ ≫ π = Spec.map (CommRingCat.ofHom
        ((Ideal.Quotient.mk (Ideal.span {Polynomial.C v - Polynomial.X * Polynomial.C u})).comp Polynomial.C)) ∧
      (let ε := Classical.choose (s2v_l1b_overlap_equiv u v)
       Spec.map (CommRingCat.ofHom
         (algebraMap (s2v_L1bChart u v) (s2v_L1bOverlap u v))) ≫ j₁ =
       Spec.map (CommRingCat.ofHom ε.symm.toRingHom) ≫
         Spec.map (CommRingCat.ofHom
           (algebraMap (s2v_L1bChart v u) (s2v_L1bOverlap v u))) ≫ j₂) ∧
      ∀ (T : Scheme) (f : T ⟶ Spec (CommRingCat.of R)),
        (∀ z : T, ∃ V : T.affineOpens, z ∈ V.1 ∧
          let g := ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ V.1
            (by intro a ha; trivial)).hom
          Nonempty ((Ideal.span {g u, g v}) ≃ₗ[Γ(T, V)] Γ(T, V))) →
        ∃! k : T ⟶ M, k ≫ π = f := by
  obtain ⟨M, j₁, j₂, π, hj₁, hj₂, hcover, hp₁, hp₂, ht⟩ :=
    s2v_l1b_binomial_chart_scheme_transition u v
  letI := hj₁
  letI := hj₂
  refine ⟨M, j₁, j₂, π, hj₁, hj₂, hcover, hp₁, hp₂, ht, ?_⟩
  intro T f hf
  exact s2v_l1b_model_source_lift u v M j₁ j₂ π hcover hp₁ hp₂ ht T f hf

/-- Local model comparison transports the two coefficient maps to actual affine section maps.
Source: Hartshorne, Algebraic Geometry, II.7.14, uniqueness of the blowup;
SchoenTowerL1bBlowupComparison and SchoenTowerL1bChartSections. -/
theorem s2v_l1b_charts_blowup_comparison_aux
    (B X : Over (Spec ↧ℂ)) (p : X ⟶ B) (I : B.left.IdealSheafData)
    (hcartier : ∀ z : X.left, ∃ V : X.left.affineOpens, z ∈ V.1 ∧
      Nonempty (((I.comap p.left).ideal V) ≃ₗ[Γ(X.left, V)] Γ(X.left, V)))
    (hblowup : ∀ (T : Over (Spec ↧ℂ)) (f : T ⟶ B),
      (∀ z : T.left, ∃ V : T.left.affineOpens, z ∈ V.1 ∧
        Nonempty (((I.comap f.left).ideal V) ≃ₗ[Γ(T.left, V)] Γ(T.left, V))) →
      ∃! k : T ⟶ X, k ≫ p = f)
    (U : B.left.affineOpens) (u v : Γ(B.left, U))
    (hI : I.ideal U = Ideal.span {u, v})
    (hv : IsRegular v) (hu : IsRegular (Ideal.Quotient.mk (Ideal.span {v}) u))
    (hu' : IsRegular u) (hv' : IsRegular (Ideal.Quotient.mk (Ideal.span {u}) v))
    (M : Scheme)
    (j₁ : Spec (CommRingCat.of (s2v_L1bChart u v)) ⟶ M)
    (j₂ : Spec (CommRingCat.of (s2v_L1bChart v u)) ⟶ M)
    (π : M ⟶ Spec Γ(B.left, U))
    (hmodel :
      IsOpenImmersion j₁ ∧ IsOpenImmersion j₂ ∧
      (∀ z : M, (∃ a, j₁ a = z) ∨ ∃ a, j₂ a = z) ∧
      j₁ ≫ π = Spec.map (CommRingCat.ofHom
        ((Ideal.Quotient.mk (Ideal.span {Polynomial.C u - Polynomial.X * Polynomial.C v})).comp Polynomial.C)) ∧
      j₂ ≫ π = Spec.map (CommRingCat.ofHom
        ((Ideal.Quotient.mk (Ideal.span {Polynomial.C v - Polynomial.X * Polynomial.C u})).comp Polynomial.C)) ∧
      ∀ (T : Scheme) (f : T ⟶ Spec (Γ(B.left, U))),
        (∀ z : T, ∃ V : T.affineOpens, z ∈ V.1 ∧
          let g := ((Scheme.ΓSpecIso (Γ(B.left, U))).inv ≫ f.appLE ⊤ V.1
            (by intro a ha; trivial)).hom
          Nonempty ((Ideal.span {g u, g v}) ≃ₗ[Γ(T, V)] Γ(T, V))) →
        ∃! k : T ⟶ M, k ≫ π = f) :
    ∃ e : (p.left ⁻¹ᵁ U.1).toScheme ≅ M,
      e.hom ≫ π ≫ U.2.fromSpec = (p.left ⁻¹ᵁ U.1).ι ≫ p.left ∧
      ∃ (V₁ V₂ : X.left.affineOpens)
        (h₁ : V₁.1 ≤ p.left ⁻¹ᵁ U.1) (h₂ : V₂.1 ≤ p.left ⁻¹ᵁ U.1)
        (e₁ : s2v_L1bChart u v ≃+* Γ(X.left, V₁))
        (e₂ : s2v_L1bChart v u ≃+* Γ(X.left, V₂)),
        V₁.1 ⊔ V₂.1 = p.left ⁻¹ᵁ U.1 ∧
        e₁.toRingHom.comp
          ((Ideal.Quotient.mk (Ideal.span {Polynomial.C u - Polynomial.X * Polynomial.C v})).comp Polynomial.C) =
          (p.left.appLE U.1 V₁.1 h₁).hom ∧
        e₂.toRingHom.comp
          ((Ideal.Quotient.mk (Ideal.span {Polynomial.C v - Polynomial.X * Polynomial.C u})).comp Polynomial.C) =
          (p.left.appLE U.1 V₂.1 h₂).hom := by
  obtain ⟨hj₁, hj₂, hcover, hp₁, hp₂, hlift⟩ := hmodel
  letI := hj₁
  letI := hj₂
  let J := I.comap U.2.fromSpec
  have hJ := s2v_l1b_centre_fromSpec I U u v hI
  have hfree := s2v_l1b_given_model_invertible u v hv hu hu' hv' J hJ
    M j₁ j₂ π hcover hp₁ hp₂
  have hM : ∀ (T : Scheme) (f : T ⟶ Spec Γ(B.left, U)),
      (∀ z : T, ∃ V : T.affineOpens, z ∈ V.1 ∧
        Nonempty (((J.comap f).ideal V) ≃ₗ[Γ(T, V)] Γ(T, V))) →
      ∃! k : T ⟶ M, k ≫ π = f := by
    intro T f hf
    apply hlift T f
    intro z
    obtain ⟨V, hz, hV⟩ := hf z
    refine ⟨V, hz, ?_⟩
    have heq := s2v_l1b_spectrum_pair_pullback J u v hJ f V
    dsimp only at heq ⊢
    exact heq ▸ hV
  obtain ⟨e, he⟩ := s2v_l1b_restricted_model_iso p.left I hcartier
    (s2v_l1b_blowup_scheme_lift B X p I hblowup) U M π hfree hM
  have heB : e.hom ≫ π ≫ U.2.fromSpec = (p.left ⁻¹ᵁ U.1).ι ≫ p.left := by
    rw [← Category.assoc, he, Category.assoc, IsAffineOpen.fromSpec,
      Iso.hom_inv_id_assoc, morphismRestrict_ι]
  refine ⟨e, heB, ?_⟩
  let k₁ := j₁ ≫ e.inv ≫ (p.left ⁻¹ᵁ U.1).ι
  let k₂ := j₂ ≫ e.inv ≫ (p.left ⁻¹ᵁ U.1).ι
  have hei : e.inv ≫ (p.left ⁻¹ᵁ U.1).ι ≫ p.left = π ≫ U.2.fromSpec := by
    rw [← heB]
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hk₁ : k₁ ≫ p.left = Spec.map (CommRingCat.ofHom
      ((Ideal.Quotient.mk (Ideal.span {Polynomial.C u - Polynomial.X * Polynomial.C v})).comp Polynomial.C)) ≫
        U.2.fromSpec := by
    change (j₁ ≫ e.inv ≫ (p.left ⁻¹ᵁ U.1).ι) ≫ p.left = _
    rw [Category.assoc, Category.assoc, hei, ← Category.assoc, hp₁]
  have hk₂ : k₂ ≫ p.left = Spec.map (CommRingCat.ofHom
      ((Ideal.Quotient.mk (Ideal.span {Polynomial.C v - Polynomial.X * Polynomial.C u})).comp Polynomial.C)) ≫
        U.2.fromSpec := by
    change (j₂ ≫ e.inv ≫ (p.left ⁻¹ᵁ U.1).ι) ≫ p.left = _
    rw [Category.assoc, Category.assoc, hei, ← Category.assoc, hp₂]
  obtain ⟨V₁, h₁, e₁, hV₁, he₁⟩ := s2v_l1b_chart_image_sections p.left U
    (CommRingCat.of (s2v_L1bChart u v)) k₁ _ hk₁
  obtain ⟨V₂, h₂, e₂, hV₂, he₂⟩ := s2v_l1b_chart_image_sections p.left U
    (CommRingCat.of (s2v_L1bChart v u)) k₂ _ hk₂
  refine ⟨V₁, V₂, h₁, h₂, e₁, e₂, ?_, he₁, he₂⟩
  rw [hV₁, hV₂]
  exact s2v_l1b_iso_chart_cover (p.left ⁻¹ᵁ U.1) e j₁ j₂ hcover


end HodgeLean.Foundations.Program
