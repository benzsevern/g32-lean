import HodgeLean.Foundations.QuotientDuality.RetainedBaseComplexBranchCoordinates
import HodgeLean.Foundations.QuotientDuality.RetainedComplexCoordinateRestriction
import HodgeLean.Foundations.QuotientDuality.RetainedArbitraryWeights
import HodgeLean.Foundations.QuotientDuality.RetainedBaseBranchCoordinates
import HodgeLean.Foundations.QuotientDuality.RetainedWeightedStrictIdentity
import HodgeLean.Foundations.Program.SchoenCycleC1ActualFinalWeightedChart
import HodgeLean.Foundations.QuotientDuality.LocalComplexNormalization
import HodgeLean.Foundations.QuotientDuality.LocalDenseChartCalibration
import HodgeLean.Foundations.QuotientDuality.RetainedZeroTowerOrientation
import HodgeLean.Foundations.QuotientDuality.RetainedModificationLocalWitness
import HodgeLean.Foundations.QuotientDuality.ModificationPushforwardOrientation
import HodgeLean.Foundations.QuotientDuality.LocalRetainedConnectedness
import HodgeLean.Foundations.QuotientDuality.LocalAlgebraicOrientation
import HodgeLean.Foundations.QuotientDuality.LocalTrace
import HodgeLean.Foundations.QuotientDuality.LocalCupCompatibility
import HodgeLean.Foundations.AlgebraicGeometry.ComplexTopology.Basis
import HodgeLean.Foundations.Topology.RationalSheafComparison
import HodgeLean.Foundations.Program.SchoenTowerGeometryDefs
import HodgeLean.Foundations.Program.SchoenCycleTowerHelpers
import HodgeLean.Foundations.Analytic.Analytification
import HodgeLean.Adapters.RationalSheafComparisonDefs
import HodgeLean.Foundations.Singular.Cup
import HodgeLean.Foundations.QuotientDuality.ComparisonCupDefs

/-! # Retained quotient orientations and normalized traces

The tower, deck maps and modification are the retained algebraic constructions.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular HodgeLean.Adapters HodgeLean.RealDefs
open HodgeLean.Foundations.Program
open HodgeLean.Foundations.Analytic
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


theorem retained_final_complex_weighted_chart
    (α : Fin (2 * r) → ℕ) (q : Fin r → ℕ)
    (hα : ∀ i : Fin r, α ⟨2 * i.val, by omega⟩ +
      α ⟨2 * i.val + 1, by omega⟩ = q i * S.m)
    (x : ComplexPoint (B (Fin.last r)))
    (U₀ : (B (Fin.last r)).left.Opens) (hx₀ : x.underlying ∈ U₀) :
    ∃ (c : ∀ j, B (Fin.last r) ⟶ B j)
      (U : (B (Fin.last r)).left.affineOpens)
      (z : Fin (h + 1) → Γ((B (Fin.last r)).left, U))
      (A : Set (Fin (2 * r))) (ι : A ↪ Fin (h + 1))
      (g : Fin (2 * r) → Γ((B (Fin.last r)).left, U))
      (eE : Fin r → Γ((B (Fin.last r)).left, U))
      (s : Fin (2 * r) → Γ((B (Fin.last r)).left, U)),
      c (Fin.last r) = 𝟙 _ ∧
      (∀ j : Fin r, c j.succ ≫ b j = c j.castSucc) ∧
      x.underlying ∈ U.1 ∧ U.1 ≤ U₀ ∧
      (MvPolynomial.eval₂Hom (complexAffineCoefficient (B (Fin.last r)) U) z).Etale ∧
      (∀ t : A, s t = z (ι t)) ∧ (∀ t, t ∉ A → s t = 1) ∧
      (∀ t, ((D 0 t).comap (c 0).left).ideal U = Ideal.span {g t}) ∧
      (∀ j : Fin r,
        ((D j.castSucc ⟨2 * j.val, by omega⟩ ⊔
          D j.castSucc ⟨2 * j.val + 1, by omega⟩).comap
          (c j.castSucc).left).ideal U = Ideal.span {eE j}) ∧
      (∀ t, (D (Fin.last r) t).ideal U = Ideal.span {s t}) ∧
      (∏ t, (Ideal.span {g t}) ^ α t) =
        (∏ t, (Ideal.span {s t}) ^ α t) *
        (Ideal.span {∏ j, eE j ^ q j}) ^ S.m := by
  classical
  let I := fun j : Fin r => D j.castSucc ⟨2 * j.val, by omega⟩ ⊔
    D j.castSucc ⟨2 * j.val + 1, by omega⟩
  letI : ∀ j, IsDominant (η j) := s2v_l1b_original_tower_generic_dominant
    p₀ hpsurj (h + 1) q₀ γ hγsurj β₀ hβ₀ B e₀ b I hcartier hblowup η hη₀ hη
  obtain ⟨Uc, z, A, ι, hxUc, hEt, hD, hunit⟩ :=
    retained_base_complex_branch_coordinates S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder W eFinal (Fin.last r) x
  let s₀ : Fin (2 * r) → Γ((B (Fin.last r)).left, Uc) :=
    fun t => if ht : t ∈ A then z (ι ⟨t, ht⟩) else 1
  have hs₀ (t) : (D (Fin.last r) t).ideal Uc = Ideal.span {s₀ t} := by
    by_cases ht : t ∈ A
    · simpa only [s₀, dif_pos ht] using hD ⟨t, ht⟩
    · rw [hunit t ht]
      simp only [s₀, dif_neg ht, Ideal.span_singleton_one]
  let V : (B (Fin.last r)).left.Opens := Uc.1 ⊓ U₀
  have hxV : x.underlying ∈ V := ⟨hxUc, hx₀⟩
  have hVU₀ : V ≤ U₀ := inf_le_right
  have hVUc : V ≤ Uc.1 := inf_le_left
  obtain ⟨c, E, hηE, eE, hc, hb, hxE, hEV, hE, hEn⟩ :=
    s2v_l1b_proper_tower_exceptional_equations B b I hcartier η hη x.underlying V hxV
  obtain ⟨U, hxU, hUE, g, hg⟩ :=
    s2v_l1b_original_branches_simultaneous_equations Z B₀ (B (Fin.last r))
      hdimZ h γ hγsurj hγinv hγ
      (fun t => Point.map p₀ (eY (y (σ t)))) (c 0 ≫ e₀.hom) x E.1 hxE
  let res := ((B (Fin.last r)).left.presheaf.map (homOfLE hUE).op).hom
  let eU := fun j => res (eE j)
  have hg' (t) : ((D 0 t).comap (c 0).left).ideal U = Ideal.span {g t} := by
    rw [hD₀, ← Scheme.IdealSheafData.comap_comp]
    exact hg t
  have hE' (j) : ((I j).comap (c j.castSucc).left).ideal U = Ideal.span {eU j} := by
    rw [← ((I j).comap (c j.castSucc).left).map_ideal hUE, hE j,
      Ideal.map_span, Set.image_singleton]
    rfl
  have hUUc : U.1 ≤ Uc.1 := hUE.trans (hEV.trans hVUc)
  let resS := ((B (Fin.last r)).left.presheaf.map (homOfLE hUUc).op).hom
  let s := fun t => resS (s₀ t)
  have hfinal (t) : (D (Fin.last r) t).ideal U = Ideal.span {s t} := by
    rw [← (D (Fin.last r) t).map_ideal hUUc, hs₀ t,
      Ideal.map_span, Set.image_singleton]
    rfl
  let zU : Fin (h + 1) → Γ((B (Fin.last r)).left, U) := fun j => resS (z j)
  have hEtU : (MvPolynomial.eval₂Hom
      (complexAffineCoefficient (B (Fin.last r)) U) zU).Etale :=
    complex_affine_coordinate_restriction (B (Fin.last r)) Uc U hUUc z hEt
  have hsCoord (t) : s t = if ht : t ∈ A then zU (ι ⟨t, ht⟩) else 1 := by
    dsimp [s, s₀, zU]
    split_ifs with ht
    · rfl
    · exact map_one resS
  have hsPresent (t : A) : s t = zU (ι t) := by
    rw [hsCoord, dif_pos t.property]
  have hsAbsent (t) (ht : t ∉ A) : s t = 1 := by
    rw [hsCoord, dif_neg ht]
  have hstep := retained_arbitrary_branch_weight_transform S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder W eFinal α
  have hstep' (j : Fin r) :
      (∏ t, ((D j.castSucc t).comap (b j).left) ^ α t) =
        (∏ t, D j.succ t ^ α t) * (((I j) ^ q j).comap (b j).left) ^ S.m := by
    simpa only [s2v_l1b_comap_pow, hα j, pow_mul] using hstep j
  have hEpow (j : Fin r) : (((I j) ^ q j).comap (c j.castSucc).left).ideal U =
      Ideal.span {eU j ^ q j} := by
    rw [s2v_l1b_comap_pow, Scheme.IdealSheafData.ideal_pow, Pi.pow_apply,
      hE' j, Ideal.span_singleton_pow]
  refine ⟨c, U, zU, A, ι, g, eU, s, hc, hb, hxU, hUE.trans (hEV.trans hVU₀),
    hEtU, hsPresent, hsAbsent, hg', hE', hfinal, ?_⟩
  exact weighted_total_transform_with_strict_branches r S.m (fun j => (B j).left)
    (fun j => (b j).left) (fun j => (c j).left)
    (congrArg Over.Hom.left hc) (fun j => congrArg Over.Hom.left (hb j))
    D (fun j => (I j) ^ q j) α hstep' U g (fun j => eU j ^ q j) hg' hEpow s hfinal

#print axioms retained_final_complex_weighted_chart
end HodgeLean.Foundations.QuotientDuality
