import HodgeLean.Foundations.Program.SchoenCycleC1MeasuredFibreProofs
import HodgeLean.Foundations.Program.SchoenCycleC1NeighbourhoodOrbitHelpers
import HodgeLean.Foundations.Program.SchoenCycleC1TowerFaithfulHelpers
import HodgeLean.Foundations.Program.SchoenCycleC1InitialFaithfulHelpers
import HodgeLean.Foundations.Program.SchoenCycleC1OrbitAssemblyHelpers
import HodgeLean.Foundations.Program.SchoenCycleC1EtalePullbackHelpers
import HodgeLean.Foundations.Program.SchoenTowerN2b
import HodgeLean.Foundations.Program.SchoenCycleCartierAvoidance
import HodgeLean.Foundations.Program.SchoenCycleS1c
import HodgeLean.Foundations.Program.SchoenCycleS2
import HodgeLean.Foundations.Program.SchoenCycleS2b
import HodgeLean.Foundations.Program.SchoenCycleStageDefs
import HodgeLean.Foundations.Program.SchoenTowerFibreDefs
import HodgeLean.Foundations.Program.SchoenTowerSheafDefs

import HodgeLean.Foundations.Program.SchoenCycleC11
import HodgeLean.Foundations.Program.SchoenCycleOrbitHelpers
import HodgeLean.Foundations.Program.SchoenCycleS3

import HodgeLean.Foundations.Program.SchoenCycleC1NoMarksEtale
import HodgeLean.Foundations.Program.SchoenCycleC1DeckHelpers

/-! # The retained slice neighbourhood when there are no paired centres -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Adapters HodgeLean.RealDefs
open scoped BigOperators Manifold ContDiff OnePoint
namespace HodgeLean.Foundations.Program

/-- With no retained paired centres the actual initial cover is unmarked;
the specified normalization isomorphisms give the required slice neighbourhood. -/
theorem s2e_c1_chain_cover_etale_near_slice_of_no_pairs
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
    (hr : r = 0)
    (k : ℕ)
    (ℓ : Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)) ⟶ B (Fin.last r))
    [IsClosedImmersion ℓ.left]
    (havoid : ∀ t, Disjoint (Set.range ℓ.left) (D (Fin.last r) t).support) :
    let β := eFinal.hom ≫ s2b_normalizationMap (B (Fin.last r)) (η (Fin.last r))
    ∃ U : (B (Fin.last r)).left.Opens,
      Set.range ℓ.left ⊆ U ∧ IsFinite (β.left ∣_ U) ∧ Etale (β.left ∣_ U) := by
  subst r
  have hlen : (g32p_exponents S).length = 0 := by
    simpa only [Fintype.card_fin, Nat.mul_zero] using (Fintype.card_congr σ).symm
  letI : IsEmpty (Fin (g32p_exponents S).length) := by rw [hlen]; infer_instance
  have hconj : eW.inv ≫ d 0 ≫ eW.hom = d₀ := by
    rw [hdinit, eW.inv_hom_id_assoc]
  have hdorder : End.of d₀ ^ S.m = 1 := by
    have hpow := s2e_c1_transport_generator_order eW.symm (d 0) S.m (horder 0)
    change End.of (eW.inv ≫ d 0 ≫ eW.hom) ^ S.m = 1 at hpow
    rw [hconj] at hpow
    exact hpow
  haveI : Etale β₀.left := s2e_c1_initial_etale_of_no_marks S Y Z W₀ B₀
    a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit (rsq_Quot S.χ.ker C)
    (Fin (g32p_exponents S).length) eY.toEquiv hpointAction
    (fun t => Point.map p₀ (eY (y t))) hbranch h hh q₀ hqsurj hqinv hq
    γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hdorder hgenerator
  have heq : s2b_normalizationMap (B 0) (η 0) = eW.hom ≫ β₀ ≫ e₀.inv := by
    calc
      s2b_normalizationMap (B 0) (η 0) =
          (s2b_normalizationMap (B 0) (η 0) ≫ e₀.hom) ≫ e₀.inv := by
            simp only [Category.assoc, e₀.hom_inv_id, Category.comp_id]
      _ = (eW.hom ≫ β₀) ≫ e₀.inv := by rw [heW]
      _ = eW.hom ≫ β₀ ≫ e₀.inv := Category.assoc _ _ _
  haveI : Etale (s2b_normalizationMap (B 0) (η 0)).left := by
    rw [heq]
    change Etale (eW.hom.left ≫ β₀.left ≫ e₀.inv.left)
    infer_instance
  haveI : IsFinite (s2b_normalizationMap (B 0) (η 0)).left := by
    rw [heq]
    change IsFinite (eW.hom.left ≫ β₀.left ≫ e₀.inv.left)
    infer_instance
  have hlast : Fin.last 0 = (0 : Fin 1) := by decide
  haveI : Etale (s2b_normalizationMap (B (Fin.last 0)) (η (Fin.last 0))).left := by
    exact hlast.symm ▸ (inferInstance : Etale (s2b_normalizationMap (B 0) (η 0)).left)
  haveI : IsFinite (s2b_normalizationMap (B (Fin.last 0)) (η (Fin.last 0))).left := by
    exact hlast.symm ▸ (inferInstance : IsFinite (s2b_normalizationMap (B 0) (η 0)).left)
  haveI : Etale (eFinal.hom ≫
      s2b_normalizationMap (B (Fin.last 0)) (η (Fin.last 0))).left := by
    change Etale (eFinal.hom.left ≫ _)
    infer_instance
  haveI : IsFinite (eFinal.hom ≫
      s2b_normalizationMap (B (Fin.last 0)) (η (Fin.last 0))).left := by
    change IsFinite (eFinal.hom.left ≫ _)
    infer_instance
  dsimp only
  refine ⟨⊤, (fun _ _ => trivial), ?_, ?_⟩ <;> infer_instance

end HodgeLean.Foundations.Program
