import HodgeLean.Foundations.Program.SchoenCycleC1NormalizationDegreeHelpers
import HodgeLean.Foundations.Program.SchoenCycleC1InitialCardHelpers
import HodgeLean.Foundations.Program.SchoenCycleC1BranchComplementHelpers
import HodgeLean.Foundations.Program.SchoenTowerN2b

/-! # A measured fibre of the actual final retained cover -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.RealDefs
open scoped BigOperators Manifold ContDiff OnePoint
namespace HodgeLean.Foundations.Program

/-- Every nonempty final base neighbourhood contains a complex fibre with
exactly the retained covering degree many points. -/
theorem s2e_c1_actual_cover_has_measured_fibre
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
    (U : (B (Fin.last r)).left.Opens) (hU : (U : Set (B (Fin.last r)).left).Nonempty) :
    let β := eFinal.hom ≫ s2b_normalizationMap (B (Fin.last r)) (η (Fin.last r))
    ∃ x : ComplexPoint (B (Fin.last r)), x.underlying ∈ U ∧
      Nat.card ((Point.map β) ⁻¹' {x}) = S.m := by
  let marks : Fin (g32p_exponents S).length → ComplexPoint Z := fun t => Point.map p₀ (eY (y t))
  obtain ⟨xgood, hxgood⟩ := s2e_c1_exists_initial_base_point_off_branches S Y Z B₀ a ha1 hamul hinj p₀
    (rsq_Quot S.χ.ker C) (Fin (g32p_exponents S).length) eY.toEquiv hpointAction marks hbranch
    h γ hγsurj hγinv hγ
  let Vraw : B₀.left.Opens :=
    ⟨⋂ t : Fin (g32p_exponents S).length, ((s2c_branchIdeal Z B₀ h γ (marks t)).support : Set B₀.left)ᶜ,
      isOpen_iInter_of_finite fun t => (s2c_branchIdeal Z B₀ h γ (marks t)).support.isClosed.isOpen_compl⟩
  have hxV : xgood.underlying ∈ Vraw := Set.mem_iInter.mpr hxgood
  have hdense : Dense (Vraw : Set B₀.left) := Vraw.isOpen.dense ⟨xgood.underlying, hxV⟩
  let Vzero := e₀.hom.left ⁻¹ᵁ Vraw
  have hVzero : Dense (Vzero : Set (B 0).left) :=
    hdense.preimage e₀.hom.left.isOpenEmbedding.isOpenMap
  have hd₀order : End.of d₀ ^ S.m = 1 := by
    have hc := s2e_c1_equivariant_generator_power eW.hom (d 0) d₀ hdinit S.m
    rw [horder 0] at hc
    apply End.ext
    apply (cancel_epi eW.hom).mp
    exact (hc.symm.trans (Category.id_comp eW.hom)).trans (Category.comp_id eW.hom).symm
  have hcardzero (x : ComplexPoint (B 0)) (hx : x.underlying ∈ Vzero) :
      Nat.card ((Point.map (s2b_normalizationMap (B 0) (η 0))) ⁻¹' {x}) = S.m := by
    have hc := s2e_c1_fibre_card_of_iso_square (s2b_normalizationMap (B 0) (η 0)) β₀ eW e₀ heW x
    rw [hc]
    apply s2e_c1_initial_fibre_card_off_marks S Y Z W₀ B₀ a e ha1 hamul p₀ hp₀ hpsurj hporbit
      (rsq_Quot S.χ.ker C) (Fin (g32p_exponents S).length) eY.toEquiv hpointAction marks hbranch
      h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hd₀order hgenerator
    intro t
    have hx' : e₀.hom.left x.underlying ∈ Vraw := hx
    have ht := Set.mem_iInter.mp hx' t
    change e₀.hom.left x.underlying ∉ (s2c_branchIdeal Z B₀ h γ (marks t)).support at ht
    simpa only [Point.underlying_map] using ht
  haveI (i : Fin (r + 1)) : IsDominant (η i) :=
    s2v_n2b_dominant S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder i
  let X := fun i : Fin (r + 1) => (B i).left
  let bs := fun i : Fin r => (b i).left
  let total := s2e_towerTotalMap B (𝟙 (B 0)) b
  have hleft : ∀ i, (total i).left = s2e_towerTotalMap X (𝟙 (B 0).left) bs i := by
    intro i
    induction i using Fin.induction with
    | zero => rfl
    | succ j ih =>
      change (s2e_towerTotalMap B (𝟙 (B 0)) b j.succ).left = s2e_towerTotalMap X (𝟙 (B 0).left) bs j.succ
      rw [s2e_towerTotalMap_succ, s2e_towerTotalMap_succ]
      change (b j).left ≫ (total j.castSucc).left = (b j).left ≫ s2e_towerTotalMap X (𝟙 (B 0).left) bs j.castSucc
      rw [ih]
  have hηtotal : ∀ i, η i ≫ (total i).left = η 0 := by
    intro i
    induction i using Fin.induction with
    | zero => exact Category.comp_id _
    | succ j ih =>
      change η j.succ ≫ (s2e_towerTotalMap B (𝟙 (B 0)) b j.succ).left = η 0
      rw [s2e_towerTotalMap_succ]
      change η j.succ ≫ ((b j).left ≫ (total j.castSucc).left) = η 0
      rw [← Category.assoc, hη j, ih]
  have hsteps (i : Fin r) : ∃ P : (B i.succ).left.PartialIso (B i.castSucc).left,
      P.iso.hom ≫ P.target.ι = P.source.ι ≫ (b i).left := by
    obtain ⟨E, hE, _⟩ := s2v_n1a_blowup_complement_iso S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder i
    obtain ⟨_, hDense, _, hDense'⟩ := s2v_n1b_centre_complements S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder i
    let I := D i.castSucc ⟨2 * i.val, by omega⟩ ⊔ D i.castSucc ⟨2 * i.val + 1, by omega⟩
    let O : (B i.castSucc).left.Opens := ⟨(I.support : Set _)ᶜ, I.support.isClosed.isOpen_compl⟩
    refine ⟨⟨(b i).left ⁻¹ᵁ O, hDense', O, hDense, E⟩, ?_⟩
    change E.hom ≫ O.ι = ((b i).left ⁻¹ᵁ O).ι ≫ (b i).left
    rw [hE, morphismRestrict_ι]
  choose P hP using hsteps
  let Pzero := Scheme.PartialIso.ofIso (Iso.refl (B 0).left)
  have hPzero : Pzero.IsOver (𝟙 (B 0).left) (𝟙 (B 0).left) := by
    simp only [Pzero, Scheme.PartialIso.IsOver, Scheme.PartialIso.ofIso, Iso.trans_hom,
      Iso.refl_hom, Iso.symm_hom, Category.comp_id, Category.id_comp, Category.assoc,
      Iso.hom_inv_id_assoc]
  obtain ⟨Q, hQ⟩ := s2e_c1_partial_iso_tower r X (B 0).left (𝟙 (B 0).left) bs Pzero hPzero P hP (Fin.last r)
  have hQ' : Q.iso.hom ≫ Q.target.ι = Q.source.ι ≫ (total (Fin.last r)).left := by
    rw [hleft]
    simpa only [Scheme.PartialIso.IsOver, Category.comp_id] using hQ
  obtain ⟨x, hx, hcx⟩ := s2e_c1_normalization_has_measured_fibre S.m (B (Fin.last r)) (B 0)
    (η (Fin.last r)) (η 0) (total (Fin.last r)) (hηtotal (Fin.last r)) Q hQ' U hU Vzero hVzero hcardzero
  refine ⟨x, hx, ?_⟩
  let β := eFinal.hom ≫ s2b_normalizationMap (B (Fin.last r)) (η (Fin.last r))
  have hsquare : eFinal.hom ≫ s2b_normalizationMap (B (Fin.last r)) (η (Fin.last r)) =
      β ≫ (Iso.refl (B (Fin.last r))).hom := by rw [Iso.refl_hom, Category.comp_id]
  have hc := s2e_c1_fibre_card_of_iso_square β (s2b_normalizationMap (B (Fin.last r)) (η (Fin.last r)))
    eFinal (Iso.refl _) hsquare x
  have hc' : Nat.card ((Point.map β) ⁻¹' {x}) =
      Nat.card ((Point.map (s2b_normalizationMap (B (Fin.last r)) (η (Fin.last r)))) ⁻¹' {x}) := by
    simpa only [Iso.refl_hom, Point.map_id, id_eq] using hc
  exact hc'.trans hcx

end HodgeLean.Foundations.Program
