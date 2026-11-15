import HodgeLean.Foundations.Program.SchoenCycleC1InitialAvoidanceProofs
import HodgeLean.Foundations.Program.SchoenCycleC1SingleCoordinateBranches
import HodgeLean.Foundations.Program.SchoenCycleC1UnitCentreSupports

/-! # The retained neighbourhood for a one-coordinate symmetric quotient -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.Adapters HodgeLean.RealDefs
open scoped BigOperators Manifold ContDiff OnePoint
namespace HodgeLean.Foundations.Program

/-- With one symmetric coordinate every paired centre has empty support;
the actual final strict avoidance gives the required retained neighbourhood. -/
theorem s2e_c1_chain_cover_etale_near_slice_of_single_coordinate
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
    (hzero : h = 0)
    (k : ℕ)
    (ℓ : Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)) ⟶ B (Fin.last r))
    [IsClosedImmersion ℓ.left]
    (havoid : ∀ t, Disjoint (Set.range ℓ.left) (D (Fin.last r) t).support) :
    let β := eFinal.hom ≫ s2b_normalizationMap (B (Fin.last r)) (η (Fin.last r))
    ∃ U : (B (Fin.last r)).left.Opens,
      Set.range ℓ.left ⊆ U ∧ IsFinite (β.left ∣_ U) ∧ Etale (β.left ∣_ U) := by
  subst h
  let X := fun i : Fin (r + 1) => (B i).left
  let bs := fun i : Fin r => (b i).left
  let I := fun i : Fin r => D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
    D i.castSucc ⟨2 * i.val + 1, by omega⟩
  have hsubset := s2e_c1_strict_support_tower_subset r X bs (Fin (2 * r)) D I htransform
  have hcentres : ∀ i, (I i).support = ⊥ := by
    intro i
    let p : Fin (2 * r) := ⟨2 * i.val, by omega⟩
    let q : Fin (2 * r) := ⟨2 * i.val + 1, by omega⟩
    have hpq : p ≠ q := by intro heq; have hv := congrArg Fin.val heq; dsimp [p, q] at hv; omega
    have hmarks : Point.map p₀ (eY (y (σ p))) ≠ Point.map p₀ (eY (y (σ q))) := by
      intro heq
      exact hpq (σ.injective (hy heq))
    have hdis := s2e_c1_single_coordinate_branch_supports_disjoint Z B₀ γ hγsurj hγinv hγ
      (Point.map p₀ (eY (y (σ p)))) (Point.map p₀ (eY (y (σ q)))) hmarks
    have hinitial : Disjoint ((D 0 p).support : Set (B 0).left)
        ((D 0 q).support : Set (B 0).left) := by
      rw [hD₀ p, hD₀ q, Scheme.IdealSheafData.support_comap,
        Scheme.IdealSheafData.support_comap]
      exact Set.disjoint_left.mpr (fun x hp hq => Set.disjoint_left.mp hdis hp hq)
    apply Closeds.ext
    change ((D i.castSucc p ⊔ D i.castSucc q).support : Set (B i.castSucc).left) = ∅
    rw [Scheme.IdealSheafData.support_sup]
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact Set.disjoint_left.mp hinitial (hsubset i.castSucc p hx.1) (hsubset i.castSucc q hx.2)
  have heq := s2e_c1_strict_support_tower_eq_of_empty_centres r X bs (Fin (2 * r)) D I
    htransform hcentres
  apply s2e_c1_chain_cover_etale_near_slice_of_initial_avoidance S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair 0 hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder W eFinal k ℓ havoid
  intro t
  let j := σ.symm t
  have hsupport := heq (Fin.last r) j
  rw [hD₀ j, Scheme.IdealSheafData.support_comap] at hsupport
  have hj : σ j = t := σ.apply_symm_apply t
  rw [hj] at hsupport
  apply Set.disjoint_left.mpr
  rintro _ ⟨p, rfl⟩ hmem
  have hmem' : ℓ.left p ∈ (D (Fin.last r) j).support := by
    change ℓ.left p ∈ ((D (Fin.last r) j).support : Set (B (Fin.last r)).left)
    rw [hsupport]
    exact hmem
  exact Set.disjoint_left.mp (havoid j) ⟨p, rfl⟩ hmem'

end HodgeLean.Foundations.Program
