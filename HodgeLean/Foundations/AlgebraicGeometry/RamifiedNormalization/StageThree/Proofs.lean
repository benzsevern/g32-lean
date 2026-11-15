import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageThree.NormalizationHelpers
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageThree.ChartHelpers
import HodgeLean.Foundations.Program.SchoenTowerL1b

/-! # Retained normalization chart interfaces
HC no distance; AV milestone no distance. -/

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits
open HodgeLean.Adapters HodgeLean.Foundations.Program
open scoped BigOperators Manifold ContDiff OnePoint
namespace AlgebraicGeometry.RamifiedNormalization.StageThree

/-- Source: Stacks Project, tag 035H; Mathlib, Scheme.Hom.normalizationPullback.
HC no distance; AV milestone no distance. -/
theorem affine_restriction_aux
    {K : Type} [Field K] {Y V : Scheme}
    (f : Spec ↧K ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (u : V ⟶ Y) [IsOpenImmersion u] [IsAffine V]
    (η : Spec ↧K ⟶ V) (hη : η ≫ u = f) :
    ∃ E : pullback f.fromNormalization u ≅ Spec ↧(normalizedChart (fieldCoeff η)),
      restrictedFieldPoint f u η hη ≫ E.hom =
        Spec.map (CommRingCat.ofHom (normalizedChart (fieldCoeff η)).subtype) ∧
      E.hom ≫ Spec.map (CommRingCat.ofHom (StageTwo.integralCoeff (fieldCoeff η))) =
        pullback.snd f.fromNormalization u ≫ V.toSpecΓ ∧
      ∀ (T : Scheme) (k : T ⟶ V),
        ∃ F : pullback (pullback.snd f.fromNormalization u) k ≅
            pullback (Spec.map (CommRingCat.ofHom (StageTwo.integralCoeff (fieldCoeff η))))
              (k ≫ V.toSpecΓ),
          F.hom ≫ pullback.fst _ _ = pullback.fst _ _ ≫ E.hom ∧
          F.hom ≫ pullback.snd _ _ = pullback.snd _ _ := by
  let p := pullback.snd f u
  have hp : pullback.fst f u ≫ η = p := by
    apply (cancel_mono u).mp
    rw [Category.assoc, hη, pullback.condition]
  haveI : IsIso (pullback.fst f u) := by
    apply isIso_of_isOpenImmersion_of_opensRange_eq_top
    rw [Scheme.Hom.opensRange_pullbackFst]
    apply top_unique
    intro z hz
    change f z ∈ u.opensRange
    rw [← hη, Scheme.Hom.comp_apply]
    exact ⟨η z, rfl⟩
  let eX := asIso (pullback.fst f u)
  let g := Spec.map (CommRingCat.ofHom (fieldCoeff η))
  have H : eX.hom ≫ g = p ≫ V.isoSpec.hom := by
    change pullback.fst f u ≫ g = p ≫ V.toSpecΓ
    rw [show g = _ from fieldCoeff_spec η, ← Category.assoc, hp]
  let C := normalizationCongr p g eX V.isoSpec H
  obtain ⟨A, hA, hAb⟩ := StageTwo.affine_chart_comparison (fieldCoeff η)
  let P := asIso (f.normalizationPullback u)
  let E := P.symm ≪≫ C ≪≫ A
  have hl : restrictedFieldPoint f u η hη =
      eX.inv ≫ p.toNormalization ≫ P.hom := by
    apply pullback.hom_ext
    · simp only [restrictedFieldPoint, pullback.lift_fst, Category.assoc]
      dsimp only [P, asIso_hom]
      rw [f.toNormalization_normalizationPullback_fst u]
      change f.toNormalization = eX.inv ≫ eX.hom ≫ f.toNormalization
      simp
    · simp only [restrictedFieldPoint, pullback.lift_snd, Category.assoc]
      dsimp only [P, asIso_hom]
      rw [f.normalizationPullback_snd u, p.toNormalization_fromNormalization]
      rw [← hp]
      change η = eX.inv ≫ eX.hom ≫ η
      simp
  have hEp : restrictedFieldPoint f u η hη ≫ E.hom =
      Spec.map (CommRingCat.ofHom (normalizedChart (fieldCoeff η)).subtype) := by
    rw [hl]
    change (eX.inv ≫ p.toNormalization ≫ P.hom) ≫ (P.inv ≫ C.hom ≫ A.hom) = _
    simp only [Category.assoc, P.hom_inv_id_assoc]
    rw [← Category.assoc p.toNormalization, normalizationCongr_point]
    simp only [Category.assoc, eX.inv_hom_id_assoc]
    exact hA
  have hEb : E.hom ≫ Spec.map (CommRingCat.ofHom
      (StageTwo.integralCoeff (fieldCoeff η))) =
      pullback.snd f.fromNormalization u ≫ V.toSpecΓ := by
    change (P.inv ≫ C.hom ≫ A.hom) ≫ _ = _
    rw [Category.assoc, Category.assoc, hAb]
    have hCb : C.hom ≫ g.fromNormalization = p.fromNormalization ≫ V.toSpecΓ :=
      normalizationCongr_base p g eX V.isoSpec H
    rw [hCb]
    rw [← f.normalizationPullback_snd u]
    change P.inv ≫ P.hom ≫ pullback.snd f.fromNormalization u ≫ V.toSpecΓ = _
    simp only [P.inv_hom_id_assoc]
  refine ⟨E, hEp, hEb, ?_⟩
  intro T k
  let β := pullback.snd f.fromNormalization u
  let π := Spec.map (CommRingCat.ofHom (StageTwo.integralCoeff (fieldCoeff η)))
  let j := V.toSpecΓ
  let a := pullback.lift (pullback.fst β k ≫ E.hom) (pullback.snd β k) (by
    rw [Category.assoc, hEb, ← Category.assoc, pullback.condition, Category.assoc])
  let b : pullback π (k ≫ j) ⟶ pullback β k :=
    pullback.lift (pullback.fst π (k ≫ j) ≫ E.inv) (pullback.snd π (k ≫ j)) (by
      apply (cancel_mono j).mp
      rw [Category.assoc, ← hEb, Category.assoc, E.inv_hom_id_assoc,
        pullback.condition, Category.assoc])
  refine ⟨⟨a, b, ?_, ?_⟩, ?_, ?_⟩
  · apply pullback.hom_ext <;> simp [a, b, β, π, j, Category.assoc]
  · apply pullback.hom_ext <;> simp [a, b, β, π, j, Category.assoc]
  · exact pullback.lift_fst _ _ _
  · exact pullback.lift_snd _ _ _


example : restrictedFieldPoint (𝟙 (Spec ↧ℚ)) (𝟙 _) (𝟙 _) (by simp) ≫
    pullback.fst _ _ = Scheme.Hom.toNormalization (𝟙 (Spec ↧ℚ)) := by
  simp [restrictedFieldPoint]

/-- Source: Stacks Project, tag 01R5, dominant morphisms to reduced schemes.
HC no distance; AV milestone no distance. -/
theorem coefficient_embedding_aux
    {K : Type} [Field K] {Y V : Scheme} [IsIntegral Y]
    (f : Spec ↧K ⟶ Y) [QuasiCompact f] [IsDominant f]
    (u : V ⟶ Y) [IsOpenImmersion u] [IsAffine V]
    (η : Spec ↧K ⟶ V) (hη : η ≫ u = f) :
    Function.Injective (fieldCoeff η) := by
  haveI : IsDominant (η ≫ u) := hη.symm ▸ inferInstance
  haveI : IsDominant η := IsDominant.of_comp_of_isOpenImmersion η u
  haveI : QuasiCompact η := QuasiCompact.of_comp η u
  haveI : IsReduced V := isReduced_of_isOpenImmersion u
  haveI := IsSchemeTheoreticallyDominant.of_isDominant η
  change Function.Injective (η.appTop ≫ (Scheme.ΓSpecIso ↧K).hom).hom
  exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso ↧K).hom).injective.comp
    (η.app_injective ⊤)


example : Function.Injective (fieldCoeff (𝟙 (Spec ↧ℚ))) := by
  exact (ConcreteCategory.bijective_of_isIso
    (Scheme.Hom.appTop (𝟙 (Spec ↧ℚ)) ≫ (Scheme.ΓSpecIso ↧ℚ).hom)).injective

/-- Source: Esnault–Viehweg, Lectures on Vanishing Theorems, §3; normalization uniqueness.
HC no distance; AV milestone no distance. -/
theorem deck_restriction_aux
    {K : Type} [Field K] {Y V : Scheme}
    (f : Spec ↧K ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (u : V ⟶ Y) [IsOpenImmersion u] [IsAffine V]
    (η : Spec ↧K ⟶ V) (hη : η ≫ u = f)
    (δ : f.normalization ⟶ f.normalization) (hδ : δ ≫ f.fromNormalization = f.fromNormalization)
    (σ : K ≃+* K)
    (hσ : Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ f.toNormalization =
      f.toNormalization ≫ δ)
    (E : pullback f.fromNormalization u ≅ Spec ↧(normalizedChart (fieldCoeff η)))
    (hE : restrictedFieldPoint f u η hη ≫ E.hom =
      Spec.map (CommRingCat.ofHom (normalizedChart (fieldCoeff η)).subtype)) :
    (∀ a, σ (fieldCoeff η a) = fieldCoeff η a) ∧
    ∃ ρ : normalizedChart (fieldCoeff η) ≃+* normalizedChart (fieldCoeff η),
      (∀ a, (ρ a : K) = σ (a : K)) ∧
      restrictedDeck f.fromNormalization δ hδ u ≫ E.hom =
        E.hom ≫ Spec.map (CommRingCat.ofHom ρ.toRingHom) := by
  let α := Spec.map (CommRingCat.ofHom σ.toRingHom)
  have hα : α ≫ η = η := by
    apply (cancel_mono u).mp
    rw [Category.assoc, hη]
    calc
      α ≫ f = α ≫ f.toNormalization ≫ f.fromNormalization := by
        rw [f.toNormalization_fromNormalization]
      _ = f.toNormalization ≫ δ ≫ f.fromNormalization := by
        rw [← Category.assoc, hσ, Category.assoc]
      _ = f := by rw [hδ, f.toNormalization_fromNormalization]
  have hc : ∀ a, σ (fieldCoeff η a) = fieldCoeff η a := by
    have H : α ≫ Spec.map (CommRingCat.ofHom (fieldCoeff η)) =
        Spec.map (CommRingCat.ofHom (fieldCoeff η)) := by
      rw [fieldCoeff_spec, ← Category.assoc, hα]
    rw [show α = Spec.map (CommRingCat.ofHom σ.toRingHom) from rfl,
      ← Spec.map_comp] at H
    exact fun a => congrArg (fun q => q.hom a) (Spec.map_injective H)
  let ρ := integralAction (fieldCoeff η) σ hc
  refine ⟨hc, ρ, fun _ => rfl, ?_⟩
  let l := restrictedFieldPoint f u η hη
  let D := restrictedDeck f.fromNormalization δ hδ u
  have hl : l ≫ D = α ≫ l := by
    apply pullback.hom_ext
    · simp only [l, D, restrictedFieldPoint, restrictedDeck, pullback.lift_fst,
        pullback.lift_fst_assoc, Category.assoc]
      exact hσ.symm
    · simp only [l, D, restrictedFieldPoint, restrictedDeck, pullback.lift_snd,
        pullback.lift_snd_assoc, Category.assoc]
      exact hα.symm
  have hρ : Spec.map (CommRingCat.ofHom (normalizedChart (fieldCoeff η)).subtype) ≫
      Spec.map (CommRingCat.ofHom ρ.toRingHom) =
      α ≫ Spec.map (CommRingCat.ofHom (normalizedChart (fieldCoeff η)).subtype) := by
    rw [show α = Spec.map (CommRingCat.ofHom σ.toRingHom) from rfl,
      ← Spec.map_comp, ← Spec.map_comp]
    rfl
  have H : l ≫ D ≫ E.hom = l ≫ E.hom ≫ Spec.map (CommRingCat.ofHom ρ.toRingHom) := by
    rw [← Category.assoc, hl, Category.assoc, hE, ← Category.assoc, hE, hρ]
  apply (cancel_epi E.inv).mp
  apply eq_of_SpecMap_comp_eq_of_isAffineOpen
    (CommRingCat.ofHom (normalizedChart (fieldCoeff η)).subtype) Subtype.val_injective
    ⊤ (isAffineOpen_top _) (by simp) (by simp)
  rw [← hE]
  simpa only [Category.assoc, E.hom_inv_id_assoc] using H


example : (3 : ℂ) ∈ StageTwo.fixedCoefficients Complex.conjAe.toRingEquiv := by
  change (starRingEnd ℂ) (3 : ℂ) = 3
  exact map_ofNat _ _

/-- Source: Hartshorne, Algebraic Geometry, II.7.14; Stacks Project, tag 035H.
HC no distance; AV milestone no distance. -/
theorem retained_normalization_blowup_chart_restriction_aux
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
      ∃ (V₁ V₂ : (B i.succ).left.affineOpens)
        (h₁ : V₁.1 ≤ (b i).left ⁻¹ᵁ U.1)
        (h₂ : V₂.1 ≤ (b i).left ⁻¹ᵁ U.1)
        (s : Γ((B i.succ).left, V₁)) (t : Γ((B i.succ).left, V₂)),
        V₁.1 ⊔ V₂.1 = (b i).left ⁻¹ᵁ U.1 ∧
        let f₁ := ((b i).left.appLE U.1 V₁.1 h₁).hom
        let f₂ := ((b i).left.appLE U.1 V₂.1 h₂).hom
        f₁ u = s * f₁ v ∧ f₂ v = t * f₂ u ∧
        Function.Surjective (Polynomial.eval₂RingHom f₁ s) ∧
        RingHom.ker (Polynomial.eval₂RingHom f₁ s) =
          Ideal.span {Polynomial.C u - Polynomial.X * Polynomial.C v} ∧
        Function.Surjective (Polynomial.eval₂RingHom f₂ t) ∧
        RingHom.ker (Polynomial.eval₂RingHom f₂ t) =
          Ideal.span {Polynomial.C v - Polynomial.X * Polynomial.C u} ∧
        ∃ (eQ₁ : RegularPairChart.ring u v ≃+* Γ((B i.succ).left, V₁))
          (eQ₂ : RegularPairChart.ring v u ≃+* Γ((B i.succ).left, V₂)),
          eQ₁.toRingHom.comp (Ideal.Quotient.mk _) = Polynomial.eval₂RingHom f₁ s ∧
          eQ₂.toRingHom.comp (Ideal.Quotient.mk _) = Polynomial.eval₂RingHom f₂ t ∧
        ∀ (V : (B i.succ).left.affineOpens), V = V₁ ∨ V = V₂ →
          ∃ (ηV : Spec W₀.left.functionField ⟶ V.1.toScheme)
            (hηV : ηV ≫ V.1.ι = η i.succ),
            Function.Injective (fieldCoeff ηV) ∧
            ∃ E : pullback (η i.succ).fromNormalization V.1.ι ≅
                Spec ↧(normalizedChart (fieldCoeff ηV)),
              restrictedFieldPoint (η i.succ) V.1.ι ηV hηV ≫ E.hom =
                Spec.map (CommRingCat.ofHom (normalizedChart (fieldCoeff ηV)).subtype) ∧
              E.hom ≫ Spec.map (CommRingCat.ofHom (StageTwo.integralCoeff (fieldCoeff ηV))) =
                pullback.snd (η i.succ).fromNormalization V.1.ι ≫ V.1.toScheme.toSpecΓ ∧
              ∀ (T : Scheme) (k : T ⟶ V.1.toScheme),
                ∃ F : pullback (pullback.snd (η i.succ).fromNormalization V.1.ι) k ≅
                    pullback (Spec.map (CommRingCat.ofHom (StageTwo.integralCoeff (fieldCoeff ηV))))
                      (k ≫ V.1.toScheme.toSpecΓ),
                  F.hom ≫ pullback.fst _ _ = pullback.fst _ _ ≫ E.hom ∧
                  F.hom ≫ pullback.snd _ _ = pullback.snd _ _ := by
  have hdom := s2v_l1b_original_tower_generic_dominant p₀ hpsurj (h + 1)
    q₀ γ hγsurj β₀ hβ₀ B e₀ b
    (fun j => D j.castSucc ⟨2 * j.val, by omega⟩ ⊔
      D j.castSucc ⟨2 * j.val + 1, by omega⟩)
    hcartier hblowup η hη₀ hη
  haveI : ∀ j, IsDominant (η j) := hdom
  obtain ⟨U, u, v, hxU, hu, hv, V₁, V₂, h₁, h₂, s, t,
    hcov, hs, ht, hsurj₁, hker₁, hsurj₂, hker₂⟩ :=
    s2v_l1b_blowup_charts S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj
      p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair
      h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator
      B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric
      w hw d hd hdinit hdw horder i x hx₁ hx₂ havoid
  let f₁ := ((b i).left.appLE U.1 V₁.1 h₁).hom
  let f₂ := ((b i).left.appLE U.1 V₂.1 h₂).hom
  have hu' : ¬ IsUnit u := branch_generator_not_isUnit _ U _ hxU hx₁ u hu
  have hv' : ¬ IsUnit v := branch_generator_not_isUnit _ U _ hxU hx₂ v hv
  haveI : Nontrivial Γ((B i.succ).left, V₁) :=
    quotient_chart_nontrivial f₁ s u v hu' hker₁
  haveI : Nontrivial Γ((B i.succ).left, V₂) :=
    quotient_chart_nontrivial f₂ t v u hv' hker₂
  have hne₁ : Nonempty V₁.1 := affineOpen_nonempty _ V₁
  have hne₂ : Nonempty V₂.1 := affineOpen_nonempty _ V₂
  refine ⟨U, u, v, hxU, hu, hv, V₁, V₂, h₁, h₂, s, t,
    hcov, hs, ht, hsurj₁, hker₁, hsurj₂, hker₂,
    quotientChartEquiv f₁ s u v hsurj₁ hker₁,
    quotientChartEquiv f₂ t v u hsurj₂ hker₂,
    quotientChartEquiv_mk f₁ s u v hsurj₁ hker₁,
    quotientChartEquiv_mk f₂ t v u hsurj₂ hker₂, ?_⟩
  intro V hV
  haveI : Nonempty V.1 := by rcases hV with rfl | rfl <;> assumption
  obtain ⟨ηV, ⟨hηV, _⟩, _⟩ :=
    s2v_i2a_dominant_field_point_open_factor V.1.ι (η i.succ)
  refine ⟨ηV, hηV, coefficient_embedding_aux (η i.succ) V.1.ι ηV hηV, ?_⟩
  exact affine_restriction_aux (η i.succ) V.1.ι ηV hηV


example : fieldCoeff (Spec.map (CommRingCat.ofHom
      (chartMap (RingHom.id ℚ) 6 2 (by norm_num))))
    ((Scheme.ΓSpecIso ↧(RegularPairChart.ring (6 : ℚ) 2)).inv
      (RegularPairChart.ratio (6 : ℚ) 2)) = 3 := by
  change ((Spec.map _).appTop ≫ (Scheme.ΓSpecIso ↧ℚ).hom).hom _ = _
  rw [Scheme.ΓSpecIso_naturality]
  simp [chartMap, RegularPairChart.ratio] <;> norm_num

/-- Source: Schoen (1988), Lemma 2.5, printed p. 15; Esnault–Viehweg, §3.
HC no distance; AV milestone no distance. -/
theorem retained_deck_field_comparison_aux
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
 :
    ∃ σ : W₀.left.functionField ≃+* W₀.left.functionField,
      orderOf σ = S.m ∧
      (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
        W₀.left.fromSpecStalk (genericPoint W₀.left) =
        W₀.left.fromSpecStalk (genericPoint W₀.left) ≫ d₀.left) ∧
      (∀ s, Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ (η s).toNormalization =
        (η s).toNormalization ≫ (d s).left) ∧
      ∀ (V : (B i.succ).left.affineOpens)
        (ηV : Spec W₀.left.functionField ⟶ V.1.toScheme)
        (hηV : ηV ≫ V.1.ι = η i.succ)
        (E : pullback (η i.succ).fromNormalization V.1.ι ≅
          Spec ↧(normalizedChart (fieldCoeff ηV))),
        restrictedFieldPoint (η i.succ) V.1.ι ηV hηV ≫ E.hom =
          Spec.map (CommRingCat.ofHom (normalizedChart (fieldCoeff ηV)).subtype) →
        ∃ ρ : normalizedChart (fieldCoeff ηV) ≃+* normalizedChart (fieldCoeff ηV),
          (∀ a, (ρ a : W₀.left.functionField) = σ (a : W₀.left.functionField)) ∧
          restrictedDeck (η i.succ).fromNormalization (d i.succ).left (congrArg (fun f => f.left) (hd i.succ)) V.1.ι ≫ E.hom =
            E.hom ≫ Spec.map (CommRingCat.ofHom ρ.toRingHom) := by
  have hm : 0 < S.m := by have := S.three_le; omega
  haveI : ∀ j, IsIso (d j) := fun j =>
    (isUnit_iff_isIso (End.of (d j))).mp
      (IsUnit.of_pow_eq_one (horder j) (Nat.ne_of_gt hm))
  haveI : IsIso d₀ := s2v_l1b_finite_order_transport_isIso eW (d 0) d₀
    hdinit (Nat.ne_of_gt hm) (horder 0)
  obtain ⟨φ, hφ, hord⟩ := s2v_l1b_original_deck_field_symmetry S Y W₀
    a e ha1 hamul hinj (h + 1) hh q₀ d₀ hqinv hq hgenerator
  haveI : IsIso (CommRingCat.ofHom φ.toRingHom) := φ.toCommRingCatIso.isIso_hom
  haveI : ∀ j, IsIntegral (s2b_normalizationOver (B j) (η j)).left := fun j => by
    change IsIntegral (η j).normalization
    infer_instance
  haveI : ∀ j, IsDominant (d j).left := fun j => inferInstance
  have hn : ∀ j, Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (η j).toNormalization =
      (η j).toNormalization ≫ (d j).left := fun j =>
    s2v_l1b_generic_deck_tower
      (fun j => s2b_normalizationOver (B j) (η j)) w W₀
      (fun j => (η j).toNormalization) hw d hdw eW d₀ hdinit hgeneric
      (Spec.map (CommRingCat.ofHom φ.toRingHom)) hφ j
  refine ⟨φ, hord, hφ, hn, ?_⟩
  intro V ηV hηV E hE
  exact (deck_restriction_aux (η i.succ) V.1.ι ηV hηV (d i.succ).left
    (congrArg Over.Hom.left (hd i.succ)) φ (hn i.succ) E hE).2


example : (starRingEnd ℂ) Complex.I ≠ Complex.I := by
  rw [Complex.conj_I]
  intro h
  have hi := congrArg Complex.im h
  norm_num at hi

end AlgebraicGeometry.RamifiedNormalization.StageThree
