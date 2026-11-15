import HodgeLean.Foundations.WitnessSelection.ComparisonHelpers
import HodgeLean.Foundations.WitnessSelection.SliceHelpers
import HodgeLean.Foundations.Program.SchoenCycleS3
import HodgeLean.Foundations.Program.SchoenCycleC1UnmarkedNormalizationTower
import HodgeLean.Foundations.Program.SchoenTransferOrbitSupport
import HodgeLean.Foundations.Program.SchoenCycleClassDefs

/-! # Geometric slice selection obligations

The slice and normalization tower use the existing project carriers.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open HodgeLean.Foundations HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Foundations.Program
open scoped BigOperators Manifold ContDiff OnePoint
namespace HodgeLean.WitnessSelection

/-- Select the actual projective slice with its incidence and transition equations,
with generic avoidance of every initial paired branch divisor.
Source: Schoen (1988), Lemmas 2.3–2.5, pp. 14–16;
SchoenCycleS3.lean:135–282, retained projective slice construction. -/
theorem slice_generic_branch_avoidance_aux
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
    (hr : 0 < r) :
    let PP : Over (Spec ↧ℂ) :=
      Over.mk (ProjectiveSpace.toBase (Fin (P.k + 1)) (Spec ↧ℂ))
    ∃ ℓ : ∀ i, PP ⟶ B i,
      (∀ t : Fin (2 * r), ∀ x : PP.left, IsGenericPoint x Set.univ → (ℓ 0).left x ∉ (D 0 t).support) ∧
      (∀ i, IsClosedImmersion (ℓ i).left) ∧
      (∀ i : Fin r, ℓ i.succ ≫ b i = ℓ i.castSucc) ∧
      (∀ i : Fin r, (ℓ i.succ).left.ker =
        s2c_strictTransform (b i).left (ℓ i.castSucc).left.ker
          (D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
            D i.castSucc ⟨2 * i.val + 1, by omega⟩)) ∧
      (∀ i : Fin r,
        (D 0 ⟨2 * i.val, by omega⟩).comap (ℓ 0).left =
          (D 0 ⟨2 * i.val + 1, by omega⟩).comap (ℓ 0).left) ∧
      (∀ T : Finset (Fin r),
        let I := T.sup (fun i =>
          (D 0 ⟨2 * i.val, by omega⟩).comap (ℓ 0).left)
        (T.card ≤ P.k → Nonempty (s2c_subscheme PP I ≅
          Over.mk (ProjectiveSpace.toBase (Fin (P.k - T.card + 1)) (Spec ↧ℂ)))) ∧
        (P.k < T.card → IsEmpty (s2c_subscheme PP I).left) ∧
        (∀ x : (s2c_subscheme PP I).left,
          ∃ U : (s2c_subscheme PP I).left.Opens, x ∈ U ∧
            Nonempty (Scheme.Modules.restrict
              (s2c_conormal (s2c_subschemeι PP I).left) U.ι ≅
              (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin T.card) :
                U.toScheme.Modules)))) ∧
      (∀ (i : Fin (r + 1)) (t : Fin (2 * r)), t.val < 2 * i.val →
        Disjoint (Set.range (ℓ i).left) (D i t).support) := by
  dsimp only
  obtain ⟨ℓ, hℓ⟩ := s2e_projective_slice S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder C₀ J aut P qC jC eC eZ hqC hpC hχ hjC primitive hprimitive hscalar hrank hselected hgenus hr
  refine ⟨ℓ, ?_, hℓ⟩
  let PP : Over (Spec ↧ℂ) := Over.mk (ProjectiveSpace.toBase (Fin (P.k + 1)) (Spec ↧ℂ))
  haveI : IsIntegral PP.left := s0_complex_projective_integral P.k
  apply paired_generic_avoidance PP P.k r (by omega) (Iso.refl _) (B 0).left
    (ℓ 0).left (D 0) hℓ.2.2.2.1
  intro i
  have hi := (hℓ.2.2.2.2.1 {i}).1 (by simp; omega)
  simp only [Finset.card_singleton, Finset.sup_singleton] at hi
  exact hi

/-- The actual paired blowup tower and its field-source normalizations have
compatible comparison isomorphisms over the initial branch-free open.
Source: Schoen (1988), pp. 15–18;
SchoenCycleC1UnmarkedNormalizationTower.lean:15;
SchoenCycleC1NormalizationComparisonHelpers.lean:15. -/
theorem tower_branch_free_comparison_aux
    {K : Type} [Field K] (r : ℕ) (X : Fin (r + 1) → Scheme)
    [∀ i, IsIntegral (X i)]
    (f : ∀ i, Spec (CommRingCat.of K) ⟶ X i)
    [∀ i, QuasiCompact (f i)] [∀ i, QuasiSeparated (f i)] [∀ i, IsDominant (f i)]
    (b : ∀ i : Fin r, X i.succ ⟶ X i.castSucc) [∀ i, Surjective (b i)]
    (hf : ∀ i : Fin r, f i.succ ≫ b i = f i.castSucc)
    (J : Type*) (D : ∀ i, J → (X i).IdealSheafData) (p q : Fin r → J)
    (hD : ∀ (i : Fin r) t, D i.succ t = s2c_strictTransform (b i) (D i.castSucc t)
      (D i.castSucc (p i) ⊔ D i.castSucc (q i)))
    (hblowup : ∀ i : Fin r, ∀ (T : Scheme) (j : T ⟶ X i.castSucc),
      (∀ x : T, ∃ V : T.affineOpens, x ∈ V.1 ∧
        Nonempty ((((D i.castSucc (p i) ⊔ D i.castSucc (q i)).comap j).ideal V)
          ≃ₗ[Γ(T, V)] Γ(T, V))) →
      ∃! u : T ⟶ X i.succ, u ≫ b i = j)
    (U : (X 0).Opens) (hU : (U : Set (X 0)).Nonempty)
    (havoid : ∀ t, ∀ x ∈ U, x ∉ (D 0 t).support)
    : ∀ i,
      let V := (s2e_towerTotalMap X (𝟙 (X 0)) b i) ⁻¹ᵁ U
      ∃ (e : V.toScheme ≅ U.toScheme)
        (E : ((f i).fromNormalization ⁻¹ᵁ V).toScheme ≅
          ((f 0).fromNormalization ⁻¹ᵁ U).toScheme),
        e.hom = s2e_towerTotalMap X (𝟙 (X 0)) b i ∣_ U ∧
        E.hom ≫ ((f 0).fromNormalization ∣_ U) =
          ((f i).fromNormalization ∣_ V) ≫ e.hom := by
  have hftall : ∀ i, f i ≫ s2e_towerTotalMap X (𝟙 (X 0)) b i = f 0 := by
    intro i
    induction i using Fin.induction with
    | zero => simp
    | succ j ih => rw [s2e_towerTotalMap_succ, ← Category.assoc, hf j, ih]
  intro i
  let t := s2e_towerTotalMap X (𝟙 (X 0)) b i
  let V := t ⁻¹ᵁ U
  haveI : IsIso (t ∣_ U) := tower_restriction_isIso r X b J D p q hD hblowup U havoid i
  let e := asIso (t ∣_ U)
  have hft : f i ≫ t = f 0 := hftall i
  have hV : (V : Set (X i)).Nonempty := by
    obtain ⟨y, hy⟩ := hU
    obtain ⟨x, _⟩ := (t ∣_ U).surjective ⟨y, hy⟩
    exact ⟨x.val, x.property⟩
  obtain ⟨fV, hfqc, hfqs, hfv⟩ := s2e_c1_generic_source_lift_to_open (X i) (f i) V hV
  obtain ⟨fU, huqc, huqs, hfu⟩ := s2e_c1_generic_source_lift_to_open (X 0) (f 0) U hU
  letI := hfqc
  letI := hfqs
  letI := huqc
  letI := huqs
  have hc : fV ≫ e.hom = fU := by
    rw [← cancel_mono U.ι, Category.assoc]
    change fV ≫ (t ∣_ U) ≫ U.ι = _
    rw [morphismRestrict_ι, ← Category.assoc, hfv, hfu, hft]
  obtain ⟨E, u, v, hu, hbase, hus, hvs, huv⟩ :=
    s2e_c1_normalization_open_base_iso (f i) (f 0) V U e fV fU hfv hfu hc
  exact ⟨e, E, rfl, hbase⟩

/-- Identify the comparison with the specified retained normalization tower map,
including its literal equation after the open inclusions.
Source: Schoen (1988), pp. 15–18;
SchoenCycleC1UnmarkedNormalizationTower.lean:15;
SchoenCycleC1NormalizationComparisonHelpers.lean:15. -/
theorem retained_tower_comparison_identification_aux
    {K : Type} [Field K] (r : ℕ) (X : Fin (r + 1) → Scheme)
    [∀ i, IsIntegral (X i)]
    (f : ∀ i, Spec (CommRingCat.of K) ⟶ X i)
    [∀ i, QuasiCompact (f i)] [∀ i, QuasiSeparated (f i)] [∀ i, IsDominant (f i)]
    (b : ∀ i : Fin r, X i.succ ⟶ X i.castSucc) [∀ i, Surjective (b i)]
    (hf : ∀ i : Fin r, f i.succ ≫ b i = f i.castSucc)
    (J : Type*) (D : ∀ i, J → (X i).IdealSheafData) (p q : Fin r → J)
    (hD : ∀ (i : Fin r) t, D i.succ t = s2c_strictTransform (b i) (D i.castSucc t)
      (D i.castSucc (p i) ⊔ D i.castSucc (q i)))
    (hblowup : ∀ i : Fin r, ∀ (T : Scheme) (j : T ⟶ X i.castSucc),
      (∀ x : T, ∃ V : T.affineOpens, x ∈ V.1 ∧
        Nonempty ((((D i.castSucc (p i) ⊔ D i.castSucc (q i)).comap j).ideal V)
          ≃ₗ[Γ(T, V)] Γ(T, V))) →
      ∃! u : T ⟶ X i.succ, u ≫ b i = j)
    (w : ∀ i : Fin r, (f i.succ).normalization ⟶ (f i.castSucc).normalization)
    (hw : ∀ i : Fin r, (f i.succ).toNormalization ≫ w i =
      (f i.castSucc).toNormalization)
    (hwbase : ∀ i : Fin r, w i ≫ (f i.castSucc).fromNormalization =
      (f i.succ).fromNormalization ≫ b i)
    (W₀ : Scheme) (e₀ : (f 0).normalization ≅ W₀)
    (W : Fin (r + 1) → Scheme) (eW : ∀ i, W i ≅ (f i).normalization)
    (φ : ∀ i, W i ⟶ W₀)
    (hφ : ∀ i, (eW i).hom ≫
      s2e_towerTotalMap (fun j => (f j).normalization)
        (𝟙 (f 0).normalization) w i ≫ e₀.hom = φ i)
    (U : (X 0).Opens) (hU : (U : Set (X 0)).Nonempty)
    (havoid : ∀ t, ∀ x ∈ U, x ∉ (D 0 t).support)
    : ∀ i,
      let V := (s2e_towerTotalMap X (𝟙 (X 0)) b i) ⁻¹ᵁ U
      ∃ (e : V.toScheme ≅ U.toScheme)
        (E : ((f i).fromNormalization ⁻¹ᵁ V).toScheme ≅
          ((f 0).fromNormalization ⁻¹ᵁ U).toScheme),
        e.hom = s2e_towerTotalMap X (𝟙 (X 0)) b i ∣_ U ∧
        E.hom ≫ ((f 0).fromNormalization ⁻¹ᵁ U).ι =
          ((f i).fromNormalization ⁻¹ᵁ V).ι ≫
            s2e_towerTotalMap (fun j => (f j).normalization)
              (𝟙 (f 0).normalization) w i ∧
        E.hom ≫ ((f 0).fromNormalization ∣_ U) =
          ((f i).fromNormalization ∣_ V) ≫ e.hom ∧
        IsIso (φ i ∣_ (e₀.inv ⁻¹ᵁ ((f 0).fromNormalization ⁻¹ᵁ U))) := by
  have hftall : ∀ i, f i ≫ s2e_towerTotalMap X (𝟙 (X 0)) b i = f 0 := by
    intro i
    induction i using Fin.induction with
    | zero => simp
    | succ j ih => rw [s2e_towerTotalMap_succ, ← Category.assoc, hf j, ih]
  have hwtall : ∀ i, (f i).toNormalization ≫
      s2e_towerTotalMap (fun j => (f j).normalization) (𝟙 _) w i = (f 0).toNormalization := by
    intro i
    induction i using Fin.induction with
    | zero => simp
    | succ j ih => rw [s2e_towerTotalMap_succ, ← Category.assoc, hw j, ih]
  have hbtall : ∀ i, s2e_towerTotalMap (fun j => (f j).normalization) (𝟙 _) w i ≫
      (f 0).fromNormalization = (f i).fromNormalization ≫
        s2e_towerTotalMap X (𝟙 (X 0)) b i := by
    intro i
    induction i using Fin.induction with
    | zero => simp
    | succ j ih =>
      rw [s2e_towerTotalMap_succ, s2e_towerTotalMap_succ, Category.assoc, ih,
        ← Category.assoc, hwbase j, Category.assoc]
  intro i
  let t := s2e_towerTotalMap X (𝟙 (X 0)) b i
  let V := t ⁻¹ᵁ U
  haveI : IsIso (t ∣_ U) := tower_restriction_isIso r X b J D p q hD hblowup U havoid i
  let e := asIso (t ∣_ U)
  have hft : f i ≫ t = f 0 := hftall i
  have hV : (V : Set (X i)).Nonempty := by
    obtain ⟨y, hy⟩ := hU
    obtain ⟨x, _⟩ := (t ∣_ U).surjective ⟨y, hy⟩
    exact ⟨x.val, x.property⟩
  obtain ⟨fV, hfqc, hfqs, hfv⟩ := s2e_c1_generic_source_lift_to_open (X i) (f i) V hV
  obtain ⟨fU, huqc, huqs, hfu⟩ := s2e_c1_generic_source_lift_to_open (X 0) (f 0) U hU
  letI := hfqc
  letI := hfqs
  letI := huqc
  letI := huqs
  have hc : fV ≫ e.hom = fU := by
    rw [← cancel_mono U.ι, Category.assoc]
    change fV ≫ (t ∣_ U) ≫ U.ι = _
    rw [morphismRestrict_ι, ← Category.assoc, hfv, hfu, hft]
  obtain ⟨E, u, v, hu, hbase, hus, hvs, huv⟩ :=
    s2e_c1_normalization_open_base_iso (f i) (f 0) V U e fV fU hfv hfu hc
  let n := s2e_towerTotalMap (fun j => (f j).normalization) (𝟙 _) w i
  let A := (f 0).fromNormalization ⁻¹ᵁ U
  let C := (f i).fromNormalization ⁻¹ᵁ V
  haveI : IsDominant u := hu
  have hi : E.hom ≫ A.ι = C.ι ≫ n := by
    apply ext_of_isDominant_of_isSeparated (ι := u) (f 0).fromNormalization
    · rw [Category.assoc, ← morphismRestrict_ι, ← Category.assoc, hbase]
      change ((f i).fromNormalization ∣_ V) ≫ (t ∣_ U) ≫ U.ι = _
      rw [morphismRestrict_ι, ← Category.assoc, morphismRestrict_ι]
      simp only [Category.assoc, n, hbtall i]
      rfl
    · rw [← Category.assoc, huv, hvs, ← Category.assoc, hus, hwtall i]
  have hpre : n ⁻¹ᵁ A = C := by
    dsimp only [A, C, V]
    rw [← Scheme.Hom.comp_preimage, hbtall i, Scheme.Hom.comp_preimage]
  haveI : IsIso (n ∣_ A) := restriction_isIso_of_open_iso n C A E hi hpre
  refine ⟨e, E, rfl, hi, hbase, ?_⟩
  rw [← hφ i, morphismRestrict_comp, morphismRestrict_comp]
  have hepre : e₀.hom ⁻¹ᵁ (e₀.inv ⁻¹ᵁ A) = A := by
    rw [← Scheme.Hom.comp_preimage, e₀.hom_inv_id, Scheme.Hom.id_preimage]
  haveI : IsIso (n ∣_ (e₀.hom ⁻¹ᵁ (e₀.inv ⁻¹ᵁ A))) := by
    rw [hepre]
    infer_instance
  infer_instance

end HodgeLean.WitnessSelection
