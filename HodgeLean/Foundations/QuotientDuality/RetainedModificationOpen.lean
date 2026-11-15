import HodgeLean.Foundations.QuotientDuality.ModificationBaseOpen
import HodgeLean.Foundations.QuotientDuality.ModificationTowerMaps
import HodgeLean.Foundations.QuotientDuality.ModificationNormalizationOpen
import HodgeLean.Foundations.Program.SchoenCycleC1BranchComplementHelpers
import HodgeLean.Foundations.Program.SchoenTowerN2b
import HodgeLean.Foundations.Program.SchoenTowerComplexPointsExist

/-! A nonempty isomorphism domain of the actual retained total modification. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedVariables false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.Foundations.Program HodgeLean.Adapters HodgeLean.RealDefs
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


theorem retained_total_open_singleton_domain :
    ∃ A : (s2b_normalizationOver (B (Fin.last r)) (η (Fin.last r))).left.Opens,
      (A : Set (s2b_normalizationOver (B (Fin.last r)) (η (Fin.last r))).left).Nonempty ∧
      IsOpenImmersion (A.ι ≫ (s2e_towerTotalMap (fun i => s2b_normalizationOver (B i) (η i)) eW.hom w (Fin.last r)).left) ∧
      ∀ x : ComplexPoint (s2b_normalizationOver (B (Fin.last r)) (η (Fin.last r))), x ∈ Point.overOpen A →
        ∀ z : ComplexPoint W,
          Point.map (eFinal.inv ≫ s2e_towerTotalMap (fun i => s2b_normalizationOver (B i) (η i)) eW.hom w (Fin.last r)) z = Point.map (eFinal.inv ≫ s2e_towerTotalMap (fun i => s2b_normalizationOver (B i) (η i)) eW.hom w (Fin.last r)) (Point.map eFinal.hom x) →
            z = Point.map eFinal.hom x := by
  let marks := fun t => Point.map p₀ (eY (y t))
  obtain ⟨xgood, hxgood⟩ := s2e_c1_exists_initial_base_point_off_branches S Y Z B₀ a
    ha1 hamul hinj p₀ (rsq_Quot S.χ.ker C) (Fin (g32p_exponents S).length)
    eY.toEquiv hpointAction marks hbranch h γ hγsurj hγinv hγ
  let Vraw : B₀.left.Opens :=
    ⟨⋂ t : Fin (g32p_exponents S).length,
      ((s2c_branchIdeal Z B₀ h γ (marks t)).support : Set B₀.left)ᶜ,
      isOpen_iInter_of_finite fun t =>
        (s2c_branchIdeal Z B₀ h γ (marks t)).support.isClosed.isOpen_compl⟩
  let V := e₀.hom.left ⁻¹ᵁ Vraw
  have hV : (V : Set (B 0).left).Nonempty := by
    obtain ⟨x, hx⟩ := e₀.hom.left.surjective xgood.underlying
    refine ⟨x, ?_⟩
    change e₀.hom.left x ∈ Vraw
    rw [hx]
    exact Set.mem_iInter.mpr hxgood
  let X := fun i => (B i).left
  let bs := fun i : Fin r => (b i).left
  let tB := s2e_towerTotalMap B (𝟙 (B 0)) b
  let tX := s2e_towerTotalMap X (𝟙 (X 0)) bs
  have htB (i) : (tB i).left = tX i := by
    exact towerTotalMap_functor (Over.forget (Spec ↧ℂ)) B (𝟙 (B 0)) b i
  have hiso : ∀ i, IsIso (tX i ∣_ V) := by
    apply base_tower_isIso_off_initial_branches r X bs (Fin (2 * r)) D
      (fun i => ⟨2 * i.val, by omega⟩) (fun i => ⟨2 * i.val + 1, by omega⟩) htransform
    · intro i
      exact s2e_blowup_universal_property_on_schemes (b i)
        (D i.castSucc ⟨2 * i.val, by omega⟩ ⊔ D i.castSucc ⟨2 * i.val + 1, by omega⟩)
        (hblowup i)
    · intro t x hx hmem
      rw [hD₀ t, Scheme.IdealSheafData.support_comap] at hmem
      exact Set.mem_iInter.mp hx (σ t) hmem
  have hηt (i) : η i ≫ (tB i).left = η 0 := by
    rw [htB]
    simpa only [Category.comp_id] using towerTotalMap_source X (𝟙 (X 0)) bs η hη i
  let N := fun i => s2b_normalizationOver (B i) (η i)
  let tN := s2e_towerTotalMap N (𝟙 (N 0)) w
  have htN (i) : (tN i).left = s2e_towerTotalMap (fun j => (N j).left)
      (𝟙 (N 0).left) (fun j => (w j).left) i :=
    towerTotalMap_functor (Over.forget (Spec ↧ℂ)) N (𝟙 (N 0)) w i
  have hηN (i) : (η i).toNormalization ≫ (tN i).left = (η 0).toNormalization := by
    rw [htN]
    simpa only [Category.comp_id] using towerTotalMap_source (fun j => (N j).left)
      (𝟙 (N 0).left) (fun j => (w j).left) (fun j => (η j).toNormalization) hw i
  haveI (i : Fin (r + 1)) : IsDominant (η i) :=
    s2v_n2b_dominant S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder i
  let T := N (Fin.last r)
  let A : T.left.Opens := ((η (Fin.last r)).fromNormalization ≫ (tB (Fin.last r)).left) ⁻¹ᵁ V
  have hgenV : genericPoint (B 0).left ∈ V :=
    ((genericPoint_spec (B 0).left).mem_open_set_iff V.isOpen).mpr
      (by simpa only [Set.univ_inter] using hV)
  have hA : (A : Set T.left).Nonempty := by
    let q := genericPoint (Spec (CommRingCat.of W₀.left.functionField))
    refine ⟨(η (Fin.last r)).toNormalization q, ?_⟩
    change ((η (Fin.last r)).toNormalization ≫
      ((η (Fin.last r)).fromNormalization ≫ (tB (Fin.last r)).left)) q ∈ V
    rw [← Category.assoc, Scheme.Hom.toNormalization_fromNormalization, hηt]
    change (η 0) (genericPoint _) ∈ V
    rw [s2_dominant_genericPoint (η 0)]
    exact hgenV
  letI : IsIso ((tB (Fin.last r)).left ∣_ V) := by rw [htB]; exact hiso _
  have hopen : IsOpenImmersion (A.ι ≫ (tN (Fin.last r)).left) :=
    normalization_transition_openImmersion_on_preimage (B (Fin.last r)) (B 0)
      (η (Fin.last r)) (η 0) (tB (Fin.last r)) (hηt _) (tN (Fin.last r)) (hηN _)
      V hV
  have htotal : s2e_towerTotalMap N eW.hom w (Fin.last r) = tN (Fin.last r) ≫ eW.hom := by
    simpa only [Category.id_comp] using towerTotalMap_postcomp N (𝟙 (N 0)) w eW.hom (Fin.last r)
  refine ⟨A, hA, ?_, ?_⟩
  · rw [htotal]
    change IsOpenImmersion ((A.ι ≫ (tN (Fin.last r)).left) ≫ eW.hom.left)
    letI := hopen
    infer_instance
  · intro xn hxn
    have huniq : ∀ z, Point.map (tN (Fin.last r)) z = Point.map (tN (Fin.last r)) xn → z = xn :=
      normalization_transition_singleton_fibre (B (Fin.last r)) (B 0)
        (η (Fin.last r)) (η 0) (tB (Fin.last r)) (hηt _) (tN (Fin.last r)) (hηN _)
        V hV xn hxn
    intro z hz
    have hz' : Point.map (tN (Fin.last r)) (Point.map eFinal.inv z) =
        Point.map (tN (Fin.last r)) xn := by
      apply (cancel_mono eW.hom).mp
      change (z ≫ eFinal.inv ≫ tN (Fin.last r)) ≫ eW.hom = (xn ≫ tN (Fin.last r)) ≫ eW.hom
      change z ≫ (eFinal.inv ≫ s2e_towerTotalMap N eW.hom w (Fin.last r)) =
        (xn ≫ eFinal.hom) ≫ (eFinal.inv ≫ s2e_towerTotalMap N eW.hom w (Fin.last r)) at hz
      rw [htotal] at hz
      simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hz
    have hzN := huniq (Point.map eFinal.inv z) hz'
    apply (cancel_mono eFinal.inv).mp
    change z ≫ eFinal.inv = (xn ≫ eFinal.hom) ≫ eFinal.inv
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    exact hzN

#print axioms retained_total_open_singleton_domain
end HodgeLean.Foundations.QuotientDuality
