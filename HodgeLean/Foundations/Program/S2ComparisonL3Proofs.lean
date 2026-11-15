import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.FibreProofs
import HodgeLean.Foundations.Program.S2ComparisonL2
/-! # S2 comparison L3 on retained cyclic-cover fibres
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
open AlgebraicGeometry AlgebraicGeometry.RamifiedNormalization
open AlgebraicGeometry.RamifiedNormalization.StageFour
namespace HodgeLean.Foundations.Program

private def centreFibreIso {B' B K : Over (Spec ↧ℂ)}
    (b : B' ⟶ B) (ι : K ⟶ B) (k : ComplexPoint K) :
    pullback (pullback.snd b ι) k ≅ pullback b (k ≫ ι) :=
  pullbackLeftPullbackSndIso b ι k

private def coverFibreIso {W E K : Over (Spec ↧ℂ)}
    (β : W ⟶ E) {B : Over (Spec ↧ℂ)} (j : B ⟶ E) (p : B ⟶ K)
    (k : ComplexPoint K) :
    s2b_coveringFibre β j p k ≅ pullback β (pullback.fst p k ≫ j) :=
  pullbackAssoc β j p k

private def changeSliceIso {W X Y B : Over (Spec ↧ℂ)}
    (β : W ⟶ B) (g : X ⟶ B) (g' : Y ⟶ B)
    (e : X ≅ Y) (he : e.hom ≫ g' = g) : pullback β g ≅ pullback β g' where
  hom := pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ e.hom)
    (by rw [Category.assoc, he]; exact pullback.condition)
  inv := pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ e.inv)
    (by rw [Category.assoc, ← he, Iso.inv_hom_id_assoc]; exact pullback.condition)
  hom_inv_id := by apply pullback.hom_ext <;> simp
  inv_hom_id := by apply pullback.hom_ext <;> simp

private def retainedFibreIso {W B' B K : Over (Spec ↧ℂ)}
    (β : W ⟶ B') (b : B' ⟶ B) (ι : K ⟶ B) (k : ComplexPoint K) :
    s2b_coveringFibre β (pullback.fst b ι) (pullback.snd b ι) k ≅
      coveringSlice β b (k ≫ ι) :=
  coverFibreIso β (pullback.fst b ι) (pullback.snd b ι) k ≪≫
    changeSliceIso β _ _ (centreFibreIso b ι k) (by simp [centreFibreIso])

private def pointIso {X Y : Over (Spec ↧ℂ)} (e : X ≅ Y) :
    ComplexPoint X ≃ₜ ComplexPoint Y where
  toFun := Point.map e.hom
  invFun := Point.map e.inv
  left_inv z := by
    change (z ≫ e.hom) ≫ e.inv = z
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  right_inv z := by
    change (z ≫ e.inv) ≫ e.hom = z
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  continuous_toFun := (Point.continuousMap e.hom).continuous
  continuous_invFun := (Point.continuousMap e.inv).continuous

private theorem pointIso_apply {X Y : Over (Spec ↧ℂ)} (e : X ≅ Y)
    (z : ComplexPoint X) : pointIso e z = Point.map e.hom z := rfl

private theorem centreFibreIso_projection {B' B K : Over (Spec ↧ℂ)}
    (b : B' ⟶ B) (ι : K ⟶ B) (k : ComplexPoint K) :
    (centreFibreIso b ι k).hom ≫ pullback.fst b (k ≫ ι) =
      pullback.fst (pullback.snd b ι) k ≫ pullback.fst b ι := by
  simp [centreFibreIso]

private theorem retainedFibreIso_projection {W B' B K : Over (Spec ↧ℂ)}
    (β : W ⟶ B') (b : B' ⟶ B) (ι : K ⟶ B) (k : ComplexPoint K) :
    (retainedFibreIso β b ι k).hom ≫ sliceProjection β b (k ≫ ι) =
      s2c_coveringFibreProjection β (pullback.fst b ι) (pullback.snd b ι) k ≫
        (centreFibreIso b ι k).hom := by
  apply (cancel_mono (centreFibreIso b ι k).inv).mp
  apply pullback.hom_ext <;>
    simp [retainedFibreIso, coverFibreIso, changeSliceIso, sliceProjection,
      s2c_coveringFibreProjection, s2b_toExceptional, Category.assoc]

private theorem retainedFibreIso_deck {W B' B K : Over (Spec ↧ℂ)}
    (β : W ⟶ B') (b : B' ⟶ B) (ι : K ⟶ B) (k : ComplexPoint K)
    (d : W ⟶ W) (hd : d ≫ β = β) :
    s2c_coveringFibreDeck β (pullback.fst b ι) (pullback.snd b ι) d hd k ≫
        (retainedFibreIso β b ι k).hom =
      (retainedFibreIso β b ι k).hom ≫ sliceDeck β b (k ≫ ι) d hd := by
  apply pullback.hom_ext
  · simp [retainedFibreIso, coverFibreIso, changeSliceIso, sliceDeck,
      s2c_coveringFibreDeck, s2b_preimageDeck, s2b_toExceptional, s2b_toCover]
  · apply (cancel_mono (centreFibreIso b ι k).inv).mp
    apply pullback.hom_ext <;>
      simp [retainedFibreIso, coverFibreIso, changeSliceIso, sliceDeck,
        s2c_coveringFibreDeck, s2b_preimageDeck, s2b_toExceptional,
        Category.assoc]

private theorem model_iterate (m a : ℕ) (c : ℂ) (hc : c ≠ 0)
    (n : ℕ) (l : ZMod (Nat.gcd m a)) (z : OnePoint ℂ) :
    (s2c_twoPointDeck m a c hc)^[n] (l, z) =
      (l + n, Option.map (fun w : ℂ => c ^ n * w) z) := by
  induction n with
  | zero => cases z <;> simp [s2c_twoPointDeck]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    apply Prod.ext
    · change l + (n : ZMod (Nat.gcd m a)) + 1 = l + (n + 1 : ℕ)
      simp only [Nat.cast_add, Nat.cast_one, add_assoc]
    · cases z with
      | infty => rfl
      | coe z =>
        change ((c * (c ^ n * z) : ℂ) : OnePoint ℂ) = ((c ^ (n + 1) * z : ℂ) : OnePoint ℂ)
        rw [pow_succ']; congr 1; ring

private theorem model_period (m a : ℕ) (c : ℂ) (hc : c ≠ 0) (h : c ^ m = 1)
    (z : s2c_twoPointFibre m a) : (s2c_twoPointDeck m a c hc)^[m] z = z := by
  obtain ⟨l, z⟩ := z
  rw [model_iterate, h, (ZMod.natCast_eq_zero_iff _ _).mpr (Nat.gcd_dvd_left m a)]
  cases z <;> simp

private abbrev testBase : Over (Spec ↧ℂ) := Over.mk (𝟙 (Spec ↧ℂ))
private def testStructural : projectiveLine ⟶ testBase :=
  Over.homMk projectiveLine.hom (by simp [testBase])
private def testCentreIso := centreFibreIso testStructural (𝟙 testBase) (𝟙 testBase)
private def testFibreIso :=
  retainedFibreIso (𝟙 projectiveLine) testStructural (𝟙 testBase) (𝟙 testBase)
private def testBaseLineIso :=
  asIso (pullback.fst testStructural ((𝟙 testBase) ≫ (𝟙 testBase)))
private def testSliceLineIso :=
  asIso (pullback.snd (𝟙 projectiveLine)
    (pullback.fst testStructural ((𝟙 testBase) ≫ (𝟙 testBase)))) ≪≫ testBaseLineIso
private def testNestedLineIso := testFibreIso ≪≫ testSliceLineIso
private def testNestedPoint :=
  Point.map testNestedLineIso.inv (lineCoordinate.symm ((2 : ℂ) : OnePoint ℂ))
private def testNestedProjection :=
  s2c_coveringFibreProjection (𝟙 projectiveLine)
    (pullback.fst testStructural (𝟙 testBase))
    (pullback.snd testStructural (𝟙 testBase)) (𝟙 testBase)

private theorem nested_transport_projection_check :
    lineCoordinate (Point.map testBaseLineIso.hom
      (Point.map testCentreIso.hom (Point.map testNestedProjection testNestedPoint))) =
        ((2 : ℂ) : OnePoint ℂ) := by
  have h : testNestedProjection ≫ testCentreIso.hom ≫ testBaseLineIso.hom =
      testNestedLineIso.hom := by
    dsimp only [testNestedProjection, testCentreIso]
    rw [← Category.assoc, ← retainedFibreIso_projection]
    simp only [testNestedLineIso, testSliceLineIso, testFibreIso,
      Iso.trans_hom, asIso_hom, sliceProjection, Category.assoc]
  change lineCoordinate (((((lineCoordinate.symm ((2 : ℂ) : OnePoint ℂ)) ≫
    testNestedLineIso.inv) ≫ testNestedProjection) ≫ testCentreIso.hom) ≫ testBaseLineIso.hom) = _
  simp only [Category.assoc, h, Iso.inv_hom_id, Category.comp_id, Homeomorph.apply_symm_apply]

private theorem nested_transport_projection_falsification :
    lineCoordinate (Point.map testBaseLineIso.hom
      (Point.map testCentreIso.hom (Point.map testNestedProjection testNestedPoint))) ≠
        ((3 : ℂ) : OnePoint ℂ) := by
  rw [nested_transport_projection_check]
  norm_num

#print axioms nested_transport_projection_check
#print axioms nested_transport_projection_falsification

/-- Source: Schoen (1988), Lemmas 2.4–2.5, printed pp. 14–15;
Barth–Hulek–Peters–Van de Ven, Compact Complex Surfaces, III.5;
Esnault–Viehweg, Lectures on Vanishing Theorems, section 3.
Example: the labelled projective line at label one and coordinate two maps to minus eight.
HC no distance; AV milestone no distance. -/
theorem s2l3_fibre_homeomorphisms_aux
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
    let α := (g32p_exponents S)[σ ⟨2 * i.val, by omega⟩]
    let β := s2b_normalizationMap (B i.succ) (η i.succ)
    let F := coveringSlice β (b i) x
    let E := exceptionalSlice (b i) x
    let P := sliceProjection β (b i) x
    let A := pullback.fst (b i) x
    ∃ (u : ComplexPoint F ≃ₜ componentModel S.m α)
      (v : ComplexPoint E ≃ₜ OnePoint ℂ) (c : ℂ) (hc : c ≠ 0),
      (∀ z, u (Point.map (sliceDeck β (b i) x (d i.succ) (hd i.succ)) z) =
        deck S.m α c hc (u z)) ∧
      (∀ z, v (Point.map P z) = projection S.m α c (u z)) ∧
      (∀ z, ((Point.map A z).left (IsLocalRing.closedPoint ℂ) ∈
        (D i.succ ⟨2 * i.val, by omega⟩).support ↔ v z = ((0 : ℂ) : OnePoint ℂ))) ∧
      (∀ z, ((Point.map A z).left (IsLocalRing.closedPoint ℂ) ∈
        (D i.succ ⟨2 * i.val + 1, by omega⟩).support ↔ v z = (∞ : OnePoint ℂ))) ∧
      orderOf (End.of (sliceDeck β (b i) x (d i.succ) (hd i.succ))) = S.m ∧
      c ^ S.m = 1 := by
  obtain ⟨j, v, c, hc, hperiod, hj, hex, hdeck, hproj, hzero, hinfty⟩ :=
    s2l2_deck_coordinates S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder i x hx₁ hx₂ havoid
  obtain ⟨_, _, _, _, _, _, _, _, hord, _⟩ :=
    retained_fibre_homeomorphisms_deck_projection_aux S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder i x hx₁ hx₂ havoid
  have hm : 0 < S.m := by have := S.three_le; omega
  let α := (g32p_exponents S)[σ ⟨2 * i.val, by omega⟩]
  let β := s2b_normalizationMap (B i.succ) (η i.succ)
  let F := coveringSlice β (b i) x
  obtain ⟨hnormproj, hfinite⟩ := s2v_n2b_selected_instances S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder i
  haveI := hnormproj
  haveI := hfinite
  haveI : T2Space (ComplexPoint (exceptionalSlice (b i) x)) :=
    (s2v_separatedPointFibreHomeomorph (b i) x).isEmbedding.t2Space
  haveI : T2Space (ComplexPoint F) :=
    s2v_pullback_points_t2 β (pullback.fst (b i) x)
  let u := (componentParametrizationHomeomorph S.m α hm F j hj hex).symm
  obtain ⟨hD, hP⟩ := componentParametrization_transport S.m α hm F
    (exceptionalSlice (b i) x) j hj hex
    (sliceDeck β (b i) x (d i.succ) (hd i.succ))
    (sliceProjection β (b i) x) v c hc hdeck hproj
  exact ⟨u, v, c, hc, hD, hP, hzero, hinfty, hord, hperiod⟩

example : projection 6 2 (-1) (1, ((2 : ℂ) : OnePoint ℂ)) =
    ((-8 : ℂ) : OnePoint ℂ) := by
  change (( (-1 : ℂ) ^ (-((6 / Nat.gcd 6 2 *
    (1 : ZMod (Nat.gcd 6 2)).val : ℕ) : ℤ)) * 2 ^ (6 / Nat.gcd 6 2) : ℂ) :
      OnePoint ℂ) = _
  norm_num [ZMod.val_one_eq_one_mod]

#print axioms s2l3_fibre_homeomorphisms_aux


/-- Source: Schoen (1988), Lemmas 2.4–2.5, printed pp. 14–15;
Barth–Hulek–Peters–Van de Ven, Compact Complex Surfaces, III.5;
Esnault–Viehweg, Lectures on Vanishing Theorems, section 3.
Example: the labelled projective line at label one and coordinate two maps to minus eight.
HC no distance; AV milestone no distance. -/
theorem s2l3_deck_equivariance_aux
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
    let α := (g32p_exponents S)[σ ⟨2 * i.val, by omega⟩]
    let β := s2b_normalizationMap (B i.succ) (η i.succ)
    let F := coveringSlice β (b i) x
    let E := exceptionalSlice (b i) x
    let P := sliceProjection β (b i) x
    let A := pullback.fst (b i) x
    ∃ (u : ComplexPoint F ≃ₜ componentModel S.m α)
      (v : ComplexPoint E ≃ₜ OnePoint ℂ) (c : ℂ) (hc : c ≠ 0),
      (∀ z, u (Point.map (sliceDeck β (b i) x (d i.succ) (hd i.succ)) z) =
        deck S.m α c hc (u z)) ∧
      (∀ z, v (Point.map P z) = projection S.m α c (u z)) ∧
      (∀ z, ((Point.map A z).left (IsLocalRing.closedPoint ℂ) ∈
        (D i.succ ⟨2 * i.val, by omega⟩).support ↔ v z = ((0 : ℂ) : OnePoint ℂ))) ∧
      (∀ z, ((Point.map A z).left (IsLocalRing.closedPoint ℂ) ∈
        (D i.succ ⟨2 * i.val + 1, by omega⟩).support ↔ v z = (∞ : OnePoint ℂ))) ∧
      orderOf (End.of (sliceDeck β (b i) x (d i.succ) (hd i.succ))) = S.m ∧
      c ^ S.m = 1  :=
  s2l3_fibre_homeomorphisms_aux S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder i x hx₁ hx₂ havoid

example : projection 6 2 (-1) (1, ((2 : ℂ) : OnePoint ℂ)) =
    ((-8 : ℂ) : OnePoint ℂ) := by
  change (( (-1 : ℂ) ^ (-((6 / Nat.gcd 6 2 *
    (1 : ZMod (Nat.gcd 6 2)).val : ℕ) : ℤ)) * 2 ^ (6 / Nat.gcd 6 2) : ℂ) :
      OnePoint ℂ) = _
  norm_num [ZMod.val_one_eq_one_mod]


#print axioms s2l3_deck_equivariance_aux

/-- Source: Schoen (1988), Lemmas 2.4–2.5, printed pp. 14–15;
Barth–Hulek–Peters–Van de Ven, Compact Complex Surfaces, III.5;
Esnault–Viehweg, Lectures on Vanishing Theorems, section 3.
Example: the labelled projective line at label one and coordinate two maps to minus eight.
HC no distance; AV milestone no distance. -/
theorem s2l3_projection_square_aux
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
    let α := (g32p_exponents S)[σ ⟨2 * i.val, by omega⟩]
    let β := s2b_normalizationMap (B i.succ) (η i.succ)
    let F := coveringSlice β (b i) x
    let E := exceptionalSlice (b i) x
    let P := sliceProjection β (b i) x
    let A := pullback.fst (b i) x
    ∃ (u : ComplexPoint F ≃ₜ componentModel S.m α)
      (v : ComplexPoint E ≃ₜ OnePoint ℂ) (c : ℂ) (hc : c ≠ 0),
      (∀ z, u (Point.map (sliceDeck β (b i) x (d i.succ) (hd i.succ)) z) =
        deck S.m α c hc (u z)) ∧
      (∀ z, v (Point.map P z) = projection S.m α c (u z)) ∧
      (∀ z, ((Point.map A z).left (IsLocalRing.closedPoint ℂ) ∈
        (D i.succ ⟨2 * i.val, by omega⟩).support ↔ v z = ((0 : ℂ) : OnePoint ℂ))) ∧
      (∀ z, ((Point.map A z).left (IsLocalRing.closedPoint ℂ) ∈
        (D i.succ ⟨2 * i.val + 1, by omega⟩).support ↔ v z = (∞ : OnePoint ℂ))) ∧
      orderOf (End.of (sliceDeck β (b i) x (d i.succ) (hd i.succ))) = S.m ∧
      c ^ S.m = 1  :=
  s2l3_fibre_homeomorphisms_aux S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder i x hx₁ hx₂ havoid

example : projection 6 2 (-1) (1, ((2 : ℂ) : OnePoint ℂ)) =
    ((-8 : ℂ) : OnePoint ℂ) := by
  change (( (-1 : ℂ) ^ (-((6 / Nat.gcd 6 2 *
    (1 : ZMod (Nat.gcd 6 2)).val : ℕ) : ℤ)) * 2 ^ (6 / Nat.gcd 6 2) : ℂ) :
      OnePoint ℂ) = _
  norm_num [ZMod.val_one_eq_one_mod]


#print axioms s2l3_projection_square_aux

/-- Source: Schoen (1988), Lemmas 2.4–2.5, printed pp. 14–15;
Barth–Hulek–Peters–Van de Ven, Compact Complex Surfaces, III.5;
Esnault–Viehweg, Lectures on Vanishing Theorems, section 3.
Example: the labelled projective line at label one and coordinate two maps to minus eight.
HC no distance; AV milestone no distance. -/
theorem s2l3_endpoint_supports_order_aux
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
    let α := (g32p_exponents S)[σ ⟨2 * i.val, by omega⟩]
    let β := s2b_normalizationMap (B i.succ) (η i.succ)
    let F := coveringSlice β (b i) x
    let E := exceptionalSlice (b i) x
    let P := sliceProjection β (b i) x
    let A := pullback.fst (b i) x
    ∃ (u : ComplexPoint F ≃ₜ componentModel S.m α)
      (v : ComplexPoint E ≃ₜ OnePoint ℂ) (c : ℂ) (hc : c ≠ 0),
      (∀ z, u (Point.map (sliceDeck β (b i) x (d i.succ) (hd i.succ)) z) =
        deck S.m α c hc (u z)) ∧
      (∀ z, v (Point.map P z) = projection S.m α c (u z)) ∧
      (∀ z, ((Point.map A z).left (IsLocalRing.closedPoint ℂ) ∈
        (D i.succ ⟨2 * i.val, by omega⟩).support ↔ v z = ((0 : ℂ) : OnePoint ℂ))) ∧
      (∀ z, ((Point.map A z).left (IsLocalRing.closedPoint ℂ) ∈
        (D i.succ ⟨2 * i.val + 1, by omega⟩).support ↔ v z = (∞ : OnePoint ℂ))) ∧
      orderOf (End.of (sliceDeck β (b i) x (d i.succ) (hd i.succ))) = S.m ∧
      c ^ S.m = 1  :=
  s2l3_fibre_homeomorphisms_aux S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder i x hx₁ hx₂ havoid

example : projection 6 2 (-1) (1, ((2 : ℂ) : OnePoint ℂ)) =
    ((-8 : ℂ) : OnePoint ℂ) := by
  change (( (-1 : ℂ) ^ (-((6 / Nat.gcd 6 2 *
    (1 : ZMod (Nat.gcd 6 2)).val : ℕ) : ℤ)) * 2 ^ (6 / Nat.gcd 6 2) : ℂ) :
      OnePoint ℂ) = _
  norm_num [ZMod.val_one_eq_one_mod]


#print axioms s2l3_endpoint_supports_order_aux

/-- Source: G32 v0.16, Lemma 4.3; Schoen (1988), Lemma 2.5, printed p. 15.
Example: a primitive sixth-root action on three labelled projective lines has a six-step return.
HC no distance; AV milestone no distance. -/
theorem s2d_two_point_covering_fibre_aux
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
    let K := s2c_subscheme (B i.castSucc) I
    let kι := s2c_subschemeι (B i.castSucc) I
    let E := s2c_exceptional (b i) I
    let j : E ⟶ B i.succ := pullback.fst (b i) kι
    let p : E ⟶ K := pullback.snd (b i) kι
    let β := s2b_normalizationMap (B i.succ) (η i.succ)
    ∀ k : ComplexPoint K,
      (∀ t : Fin (2 * r), t.val ≠ 2 * i.val → t.val ≠ 2 * i.val + 1 →
        (Point.map kι k).left.base (IsLocalRing.closedPoint ℂ) ∉
          (D i.castSucc t).support) →
      let α := (g32p_exponents S)[σ ⟨2 * i.val, by omega⟩]
      ∃ (c : ℂ) (hc : c ≠ 0)
        (u : ComplexPoint (s2b_coveringFibre β j p k) ≃ₜ s2c_twoPointFibre S.m α)
        (v : ComplexPoint (pullback p k) ≃ₜ OnePoint ℂ),
        c ^ S.m = 1 ∧
        (∀ x, u (Point.map (s2c_coveringFibreDeck β j p (d i.succ) (hd i.succ) k) x) =
          s2c_twoPointDeck S.m α c hc (u x)) ∧
        (∀ x, v (Point.map (s2c_coveringFibreProjection β j p k) x) =
          s2c_twoPointProjection S.m α c (u x)) ∧
        (∀ x : s2c_twoPointFibre S.m α,
          (s2c_twoPointDeck S.m α c hc)^[S.m] x = x) ∧
        (∀ x : ComplexPoint (pullback p k),
          (Point.map (pullback.fst p k ≫ j) x).left.base (IsLocalRing.closedPoint ℂ) ∈
            (D i.succ ⟨2 * i.val, by omega⟩).support ↔ v x = (0 : ℂ)) ∧
        (∀ x : ComplexPoint (pullback p k),
          (Point.map (pullback.fst p k ≫ j) x).left.base (IsLocalRing.closedPoint ℂ) ∈
            (D i.succ ⟨2 * i.val + 1, by omega⟩).support ↔ v x = (∞ : OnePoint ℂ)) := by
  dsimp only
  dsimp only [s2c_exceptional]
  intro k havoid
  let I := D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
    D i.castSucc ⟨2 * i.val + 1, by omega⟩
  let ι := s2c_subschemeι (B i.castSucc) I
  let x := Point.map ι k
  have hx : x.left (IsLocalRing.closedPoint ℂ) ∈ I.support := by
    exact (Scheme.IdealSheafData.range_subschemeι I).le
      ⟨k.left (IsLocalRing.closedPoint ℂ), rfl⟩
  have hxs : x.left (IsLocalRing.closedPoint ℂ) ∈
      (D i.castSucc ⟨2 * i.val, by omega⟩).support ∧
      x.left (IsLocalRing.closedPoint ℂ) ∈
      (D i.castSucc ⟨2 * i.val + 1, by omega⟩).support := by
    dsimp only [I] at hx
    rw [Scheme.IdealSheafData.support_sup] at hx
    exact hx
  obtain ⟨u, v, c, hc, hu, hv, hz, hi, hord, hphase⟩ :=
    s2l3_fibre_homeomorphisms_aux S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder i x hxs.1 hxs.2 havoid
  let β := s2b_normalizationMap (B i.succ) (η i.succ)
  let eE := centreFibreIso (b i) ι k
  let eF := retainedFibreIso β (b i) ι k
  refine ⟨c, hc, (pointIso eF).trans u, (pointIso eE).trans v, hphase, ?_, ?_,
    model_period S.m _ c hc hphase, ?_, ?_⟩
  · intro z
    change u ((z ≫ _) ≫ eF.hom) = _
    rw [Category.assoc, retainedFibreIso_deck]
    simpa only [Homeomorph.trans_apply, pointIso_apply, Point.map, Category.assoc,
      eF, β, x, ι, I] using hu (Point.map eF.hom z)
  · intro z
    change v ((z ≫ _) ≫ eE.hom) = _
    rw [Category.assoc, ← retainedFibreIso_projection]
    simpa only [Homeomorph.trans_apply, pointIso_apply, Point.map, Category.assoc,
      eF, β, x, ι, I] using hv (Point.map eF.hom z)
  · intro z
    have hpoint : Point.map (pullback.fst (b i) x) (Point.map eE.hom z) =
        Point.map (pullback.fst (pullback.snd (b i) ι) k ≫ pullback.fst (b i) ι) z := by
      simpa only [Point.map, Category.assoc, eE, x] using
        congrArg (fun f => z ≫ f) (centreFibreIso_projection (b i) ι k)
    have hh := hz (Point.map eE.hom z)
    rw [hpoint] at hh
    exact hh
  · intro z
    have hpoint : Point.map (pullback.fst (b i) x) (Point.map eE.hom z) =
        Point.map (pullback.fst (pullback.snd (b i) ι) k ≫ pullback.fst (b i) ι) z := by
      simpa only [Point.map, Category.assoc, eE, x] using
        congrArg (fun f => z ≫ f) (centreFibreIso_projection (b i) ι k)
    have hh := hi (Point.map eE.hom z)
    rw [hpoint] at hh
    exact hh

example : projection 6 2 (-1) (1, ((2 : ℂ) : OnePoint ℂ)) =
    ((-8 : ℂ) : OnePoint ℂ) := by
  change (( (-1 : ℂ) ^ (-((6 / Nat.gcd 6 2 *
    (1 : ZMod (Nat.gcd 6 2)).val : ℕ) : ℤ)) * 2 ^ (6 / Nat.gcd 6 2) : ℂ) :
      OnePoint ℂ) = _
  norm_num [ZMod.val_one_eq_one_mod]


#print axioms s2d_two_point_covering_fibre_aux

#print axioms centreFibreIso
#print axioms coverFibreIso
#print axioms changeSliceIso
#print axioms retainedFibreIso
#print axioms pointIso
#print axioms pointIso_apply
#print axioms centreFibreIso_projection
#print axioms retainedFibreIso_projection
#print axioms retainedFibreIso_deck
#print axioms model_iterate
#print axioms model_period

end HodgeLean.Foundations.Program
