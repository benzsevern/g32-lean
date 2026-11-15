import HodgeLean.Foundations.Program.SchoenCycleC1NoPairsProofs
import HodgeLean.Foundations.Program.SchoenCycleC1UnmarkedNormalizationTower
import HodgeLean.Foundations.Program.SchoenCycleC1AffineGenericEtaleHelpers
import HodgeLean.Foundations.Program.SchoenCycleC1TransitionSurjective

/-! # The actual retained neighbourhood over the initial unmarked locus -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.Adapters HodgeLean.RealDefs
open scoped BigOperators Manifold ContDiff OnePoint
namespace HodgeLean.Foundations.Program

/-- A slice projecting outside every initial branch support has its actual
finite etale neighbourhood after every specified normalization and blowup stage. -/
theorem s2e_c1_chain_cover_etale_near_slice_of_initial_avoidance
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
    (W : Over (Spec ↧ℂ))
    (eFinal : W ≅ s2b_normalizationOver (B (Fin.last r)) (η (Fin.last r)))
    (k : ℕ)
    (ℓ : Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)) ⟶ B (Fin.last r))
    [IsClosedImmersion ℓ.left]
    (havoid : ∀ t, Disjoint (Set.range ℓ.left) (D (Fin.last r) t).support)
    (hinitial : ∀ t : Fin (g32p_exponents S).length,
      Disjoint (Set.range (ℓ.left ≫
        s2e_towerTotalMap (fun i : Fin (r + 1) => (B i).left) (𝟙 (B 0).left)
          (fun i => (b i).left) (Fin.last r) ≫ e₀.hom.left))
        (s2c_branchIdeal Z B₀ h γ (Point.map p₀ (eY (y t)))).support) :
    let β := eFinal.hom ≫ s2b_normalizationMap (B (Fin.last r)) (η (Fin.last r))
    ∃ U : (B (Fin.last r)).left.Opens,
      Set.range ℓ.left ⊆ U ∧ IsFinite (β.left ∣_ U) ∧ Etale (β.left ∣_ U) := by
  let marks : Fin (g32p_exponents S).length → ComplexPoint Z := fun t => Point.map p₀ (eY (y t))
  obtain ⟨xgood, hxgood⟩ := s2e_c1_exists_initial_base_point_off_branches S Y Z B₀ a ha1 hamul hinj p₀
    (rsq_Quot S.χ.ker C) (Fin (g32p_exponents S).length) eY.toEquiv hpointAction marks hbranch
    h γ hγsurj hγinv hγ
  let Vraw : B₀.left.Opens :=
    ⟨⋂ t : Fin (g32p_exponents S).length, ((s2c_branchIdeal Z B₀ h γ (marks t)).support : Set B₀.left)ᶜ,
      isOpen_iInter_of_finite fun t => (s2c_branchIdeal Z B₀ h γ (marks t)).support.isClosed.isOpen_compl⟩
  have hxV : xgood.underlying ∈ Vraw := Set.mem_iInter.mpr hxgood
  let Vzero := e₀.hom.left ⁻¹ᵁ Vraw
  have hVzero : (Vzero : Set (B 0).left).Nonempty := by
    obtain ⟨x, hx⟩ := e₀.hom.left.surjective xgood.underlying
    exact ⟨x, by change e₀.hom.left x ∈ Vraw; rw [hx]; exact hxV⟩
  have hconj : eW.inv ≫ d 0 ≫ eW.hom = d₀ := by rw [hdinit, eW.inv_hom_id_assoc]
  have hdorder : End.of d₀ ^ S.m = 1 := by
    have hpow := s2e_c1_transport_generator_order eW.symm (d 0) S.m (horder 0)
    change End.of (eW.inv ≫ d 0 ≫ eW.hom) ^ S.m = 1 at hpow
    rwa [hconj] at hpow
  haveI : Etale (β₀.left ∣_ Vraw) := s2e_c1_initial_etale_over_unmarked_open S Y Z W₀ B₀
    a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit (rsq_Quot S.χ.ker C)
    (Fin (g32p_exponents S).length) eY.toEquiv hpointAction marks hbranch
    h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hdorder hgenerator Vraw
    (fun t x hx => Set.mem_iInter.mp hx t)
  haveI : Etale ((η 0).fromNormalization ∣_ Vzero) :=
    s2e_c1_etale_restriction_of_iso_square (s2b_normalizationMap (B 0) (η 0)).left β₀.left
      (asIso eW.hom.left) (asIso e₀.hom.left) (congrArg Over.Hom.left heW).symm Vraw
  haveI (i : Fin (r + 1)) : IsDominant (η i) :=
    s2v_n2b_dominant S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder i
  let X := fun i : Fin (r + 1) => (B i).left
  let bs := fun i : Fin r => (b i).left
  haveI (i : Fin r) : Surjective (bs i) :=
    s2e_c1_transition_surjective_of_generic_square (B i.succ) (B i.castSucc)
      (b i) (η i.succ) (η i.castSucc) (hη i)
  have htower : ∀ i, Etale ((η i).fromNormalization ∣_
      ((s2e_towerTotalMap X (𝟙 (X 0)) bs i) ⁻¹ᵁ Vzero)) := by
    apply s2e_c1_normalization_tower_etale_over_initial_unmarked_open r X η bs hη
      (Fin (2 * r)) D (fun i => ⟨2 * i.val, by omega⟩)
      (fun i => ⟨2 * i.val + 1, by omega⟩) htransform
    · intro i
      exact s2e_blowup_universal_property_on_schemes (b i)
        (D i.castSucc ⟨2 * i.val, by omega⟩ ⊔ D i.castSucc ⟨2 * i.val + 1, by omega⟩)
        (hblowup i)
    · exact hVzero
    · intro t x hx hmem
      rw [hD₀ t, Scheme.IdealSheafData.support_comap] at hmem
      exact Set.mem_iInter.mp hx (σ t) hmem
  let U := (s2e_towerTotalMap X (𝟙 (X 0)) bs (Fin.last r)) ⁻¹ᵁ Vzero
  haveI : Etale ((η (Fin.last r)).fromNormalization ∣_ U) := htower (Fin.last r)
  letI := s2v_n2b_finite S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder (Fin.last r)
  let β := eFinal.hom ≫ s2b_normalizationMap (B (Fin.last r)) (η (Fin.last r))
  haveI : IsFinite β.left := by change IsFinite (eFinal.hom.left ≫ _); infer_instance
  haveI : Etale (β.left ∣_ U) := by
    change Etale ((eFinal.hom.left ≫ (η (Fin.last r)).fromNormalization) ∣_ U)
    rw [morphismRestrict_comp]
    infer_instance
  refine ⟨U, ?_, inferInstance, inferInstance⟩
  rintro _ ⟨p, rfl⟩
  apply Set.mem_iInter.mpr
  intro t
  exact Set.disjoint_left.mp (hinitial t) ⟨p, rfl⟩

end HodgeLean.Foundations.Program
