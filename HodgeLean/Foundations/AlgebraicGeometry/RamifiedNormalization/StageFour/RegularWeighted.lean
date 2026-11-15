import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageThree.Basic
import HodgeLean.Foundations.Program.SchoenTowerL1aEtaleRestriction

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedVariables false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Adapters HodgeLean.Foundations.Program
open scoped BigOperators Manifold ContDiff OnePoint
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

theorem regular_weighted_factorization
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
      x.left (IsLocalRing.closedPoint ℂ) ∉ (D i.castSucc t).support)
    (U₀ : (B i.castSucc).left.Opens)
    (hxU₀ : x.left (IsLocalRing.closedPoint ℂ) ∈ U₀) :
    ∃ (U : (B i.castSucc).left.affineOpens)
      (hηU : ⊤ ≤ (η i.castSucc) ⁻¹ᵁ U.1)
      (u v : Γ((B i.castSucc).left, U))
      (δ : Γ((B i.castSucc).left, U)ˣ)
      (c : ∀ j : Fin (i.val + 1), B i.castSucc ⟶ B ⟨j.val, by omega⟩)
      (g : Fin (2 * r) → Γ((B i.castSucc).left, U))
      (eE : Fin i.val → Γ((B i.castSucc).left, U)),
      x.left (IsLocalRing.closedPoint ℂ) ∈ U.1 ∧
      c (Fin.last i.val) = 𝟙 (B i.castSucc) ∧
      (∀ j : Fin i.val, c j.succ ≫ b ⟨j.val, by omega⟩ = c j.castSucc) ∧
      (D i.castSucc ⟨2 * i.val, by omega⟩).ideal U = Ideal.span {u} ∧
      (D i.castSucc ⟨2 * i.val + 1, by omega⟩).ideal U = Ideal.span {v} ∧
      (∀ j, ((s2c_branchIdeal Z B₀ h γ (Point.map p₀ (eY (y (σ j))))).comap
        (c 0 ≫ e₀.hom).left).ideal U = Ideal.span {g j}) ∧
      (∀ j : Fin i.val,
        ((D ⟨j.val, by omega⟩ ⟨2 * j.val, by omega⟩ ⊔
          D ⟨j.val, by omega⟩ ⟨2 * j.val + 1, by omega⟩).comap
          (c j.castSucc).left).ideal U = Ideal.span {eE j}) ∧
      let α := (g32p_exponents S)[σ ⟨2 * i.val, by omega⟩]
      let ρ := ((η i.castSucc).appLE U.1 ⊤ hηU ≫
        (Scheme.ΓSpecIso W₀.left.functionField).hom).hom
      IsRegular v ∧ IsRegular (Ideal.Quotient.mk (Ideal.span {v}) u) ∧
      IsRegular u ∧ IsRegular (Ideal.Quotient.mk (Ideal.span {u}) v) ∧
      U.1 ≤ U₀ ∧ ρ (∏ j, eE j) ≠ 0 ∧
      (∏ j, (g j) ^ (g32p_exponents S)[σ j]) =
        (δ : Γ((B i.castSucc).left, U)) * u ^ α * v ^ (S.m - α) *
          (∏ j, eE j) ^ S.m := by
  classical
  obtain ⟨V, hn, z, hxV, hz, hz₁, hz₂⟩ :=
    s2v_l1b_tower_branch_generators S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder i x hx₁ hx₂ havoid
  have hstep := s2v_l1b_retained_weighted_transform_step S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder
  let I := fun j : Fin r => D j.castSucc ⟨2 * j.val, by omega⟩ ⊔
    D j.castSucc ⟨2 * j.val + 1, by omega⟩
  letI : ∀ j, IsDominant (η j) := s2v_l1b_original_tower_generic_dominant
    p₀ hpsurj (h + 1) q₀ γ hγsurj β₀ hβ₀ B e₀ b I hcartier hblowup η hη₀ hη
  let a₁ : Fin (2 * r) := ⟨2 * i.val, by omega⟩
  let a₂ : Fin (2 * r) := ⟨2 * i.val + 1, by omega⟩
  obtain ⟨W, hxW, hWV, hW⟩ := s2v_l1b_affine_avoid_finite_supports
    (B i.castSucc).left
    (fun t : {t : Fin (2 * r) // t ≠ a₁ ∧ t ≠ a₂} => D i.castSucc t.val)
    x.underlying (fun t => havoid t.val
      (fun he => t.property.1 (Fin.ext he))
      (fun he => t.property.2 (Fin.ext he)))
    (V.1 ⊓ U₀) ⟨hxV, hxU₀⟩
  let B' := fun j : Fin (i.val + 1) => B ⟨j.val, by omega⟩
  let b' := fun j : Fin i.val => b ⟨j.val, by omega⟩
  let I' := fun j : Fin i.val => I ⟨j.val, by omega⟩
  let η' := fun j : Fin (i.val + 1) => η ⟨j.val, by omega⟩
  obtain ⟨c, E, hηE, eE, hc, hb, hxE, hEW, hE, hEn⟩ :=
    s2v_l1b_proper_tower_exceptional_equations B' b' I'
      (fun j => hcartier ⟨j.val, by omega⟩) η'
      (fun j => hη ⟨j.val, by omega⟩) x.underlying W.1 hxW
  obtain ⟨U, hxU, hUE, g, hg⟩ :=
    s2v_l1b_original_branches_simultaneous_equations Z B₀ (B i.castSucc)
      hdimZ h γ hγsurj hγinv hγ
      (fun t => Point.map p₀ (eY (y (σ t)))) (c 0 ≫ e₀.hom) x E.1 hxE
  let res := ((B i.castSucc).left.presheaf.map (homOfLE hUE).op).hom
  let eU := fun j => res (eE j)
  have hUV : U.1 ≤ V.1 := hUE.trans (hEW.trans (fun _ ht => (hWV ht).1))
  let resV := ((B i.castSucc).left.presheaf.map (homOfLE hUV).op).hom
  let u := resV (z ⟨0, by omega⟩)
  let v := resV (z ⟨1, by omega⟩)
  have hu : (D i.castSucc a₁).ideal U = Ideal.span {u} :=
    s2v_l1b_principal_restrict _ _ U V hUV _ hz₁
  have hv : (D i.castSucc a₂).ideal U = Ideal.span {v} :=
    s2v_l1b_principal_restrict _ _ U V hUV _ hz₂
  have hEU : ∀ j, ((I' j).comap (c j.castSucc).left).ideal U = Ideal.span {eU j} :=
    fun j => s2v_l1b_principal_restrict _ _ U E hUE _ (hE j)
  have hrest : ∀ t, t ≠ a₁ → t ≠ a₂ → (D i.castSucc t).ideal U = ⊤ := by
    intro t ht₁ ht₂
    rw [← (D i.castSucc t).map_ideal (hUE.trans hEW), hW ⟨t, ht₁, ht₂⟩,
      Ideal.map_top]
  letI : Nonempty U.1 := ⟨⟨x.underlying, hxU⟩⟩
  have hg' : ∀ t, ((D 0 t).comap (c 0).left).ideal U = Ideal.span {g t} := by
    intro t
    rw [hD₀ t, ← Scheme.IdealSheafData.comap_comp]
    exact hg t
  obtain ⟨δ, hδ⟩ := s2v_l1b_tower_section_factorization i.val S.m
    (fun j => (B' j).left) (fun j => (b' j).left) (fun j => (c j).left)
    (congrArg Over.Hom.left hc) (fun j => congrArg Over.Hom.left (hb j))
    (fun j t => D ⟨j.val, by omega⟩ t) I'
    (fun t => (g32p_exponents S)[σ t])
    (fun j => hstep ⟨j.val, by omega⟩) U g eU a₁ a₂
    (by intro he; have := congrArg Fin.val he; dsimp [a₁, a₂] at this; omega)
    (hpair i) u v hg' hEU hu hv hrest
  have hηU : ⊤ ≤ (η i.castSucc) ⁻¹ᵁ U.1 := by
    letI : Subsingleton (Spec W₀.left.functionField) := by
      change Subsingleton (PrimeSpectrum W₀.left.functionField)
      infer_instance
    intro q _
    change η i.castSucc q ∈ U.1
    rw [Subsingleton.elim q (genericPoint (Spec W₀.left.functionField)),
      s2_dominant_genericPoint (η i.castSucc)]
    exact ((genericPoint_spec (B i.castSucc).left).mem_open_set_iff U.1.isOpen).mpr
      (by simpa using (show Nonempty U.1 from inferInstance))
  have hEnz : (∏ j, eE j) ≠ 0 := by
    intro he
    apply hEn
    rw [he, map_zero]
  have hres : Function.Injective res :=
    map_injective_of_isIntegral (B i.castSucc).left (homOfLE hUE)
  have heUne : (∏ j, eU j) ≠ 0 := by
    rw [show (∏ j, eU j) = res (∏ j, eE j) from (map_prod res _ _).symm]
    exact fun he => hEnz (hres (he.trans (map_zero res).symm))
  have hij : (⟨0, by omega⟩ : Fin (h + 1)) ≠ ⟨1, by omega⟩ := by
    intro he
    have heval : (0 : ℕ) = 1 := congrArg Fin.val he
    omega
  obtain ⟨hvreg, hureg⟩ := s2v_l1b_etale_coordinate_pair
    ((B i.castSucc).hom.appLE ⊤ V.1 le_top).hom z hz _ _ hij
  obtain ⟨hureg', hvreg'⟩ := s2v_l1b_etale_coordinate_pair
    ((B i.castSucc).hom.appLE ⊤ V.1 le_top).hom z hz _ _ hij.symm
  letI := resV.toAlgebra
  letI : Algebra.Etale Γ((B i.castSucc).left, V) Γ((B i.castSucc).left, U) :=
    s2v_l1a_affine_section_restriction_etale V U hUV
  obtain ⟨hvregU, huregU⟩ := s2v_l1b_regular_pair_flat (A := Γ((B i.castSucc).left, U))
    (z ⟨0, by omega⟩) (z ⟨1, by omega⟩) hvreg hureg
  obtain ⟨huregU', hvregU'⟩ := s2v_l1b_regular_pair_flat (A := Γ((B i.castSucc).left, U))
    (z ⟨1, by omega⟩) (z ⟨0, by omega⟩) hureg' hvreg'
  refine ⟨U, hηU, u, v, δ, c, g, eU, hxU, hc, hb, hu, hv, hg, hEU,
    hvregU, huregU, huregU', hvregU', ?_, ?_, hδ⟩
  · exact hUE.trans (hEW.trans (fun _ ht => (hWV ht).2))
  · intro he
    exact heUne (s2v_l1b_dominant_section_map_injective _ (η i.castSucc)
      U.1 hηU (he.trans (map_zero _).symm))

end AlgebraicGeometry.RamifiedNormalization.StageFour
