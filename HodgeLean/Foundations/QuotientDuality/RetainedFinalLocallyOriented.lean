import HodgeLean.Foundations.QuotientDuality.RetainedFieldSourceChartOrientation
import HodgeLean.Foundations.QuotientDuality.RetainedFieldSourceChartRange
import HodgeLean.Foundations.QuotientDuality.LocalOpenImmersionImage
import HodgeLean.Foundations.QuotientDuality.LocalHomeomorphOrientation
import HodgeLean.Foundations.QuotientDuality.RetainedFinalMonomialChart
import HodgeLean.Foundations.QuotientDuality.RetainedStrictKummerFieldChart
import HodgeLean.Foundations.QuotientDuality.MonomialPairedResidueWeights
import HodgeLean.Foundations.QuotientDuality.MonomialCoordinateWeights
import HodgeLean.Foundations.QuotientDuality.RetainedFinalComplexWeightedChart
import HodgeLean.Foundations.Program.SchoenCycleC1ActualFinalWeightedEtaleOpen
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
set_option maxHeartbeats 400000
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


theorem retained_final_locally_oriented (x : ComplexPoint W) :
    ∃ U : W.left.affineOpens, x.underlying ∈ U.1 ∧
      Nonempty (LocalRationalOrientation
        (TopCat.of (ComplexPoint (openScheme W U.1))) (2 * (h + 1))) := by
  let T := s2b_normalizationOver (B (Fin.last r)) (η (Fin.last r))
  let xB := Point.map (s2b_normalizationMap (B (Fin.last r)) (η (Fin.last r)))
    (Point.map eFinal.inv x)
  obtain ⟨U, hxU, hηU, z, α, ε, v, hUtop, hEt, hv, hgen⟩ :=
    retained_final_monomial_chart S Y Z W₀ B₀ hdimY hdimZ a e ha1 hamul hinj p₀ hp₀ hpsurj hporbit C eY hpointAction r σ y rot hrot hy hbranch hexp hpair h hh q₀ hqsurj hqinv hq γ hγsurj hγinv hγ β₀ hβ₀ d₀ hd₀ hgenerator B e₀ b D hD₀ htransform hcartier hblowup η hη₀ hη eW heW hgeneric w hw d hd hdinit hdw horder W eFinal xB ⊤ (by trivial)
  letI : Nonempty U.1 := ⟨⟨xB.underlying, hxU⟩⟩
  let R := Γ((B (Fin.last r)).left, U)
  letI : Algebra R W₀.left.functionField :=
    ((η (Fin.last r)).app U.1 ≫
      (s2v_fieldSourceSectionsIso (η (Fin.last r)) U.1 hηU).hom).hom.toAlgebra
  let N := integralClosure R W₀.left.functionField
  letI : Algebra ℂ N := ((algebraMap R N).comp
    (complexAffineCoefficient (B (Fin.last r)) U)).toAlgebra
  let I := fun j : Fin r => D j.castSucc ⟨2 * j.val, by omega⟩ ⊔
    D j.castSucc ⟨2 * j.val + 1, by omega⟩
  letI : ∀ i, IsDominant (η i) := s2v_l1b_original_tower_generic_dominant
    p₀ hpsurj (h + 1) q₀ γ hγsurj β₀ hβ₀ B e₀ b I hcartier hblowup η hη₀ hη
  letI : LocallyOfFiniteType ((η (Fin.last r)).fromNormalization ≫ (B (Fin.last r)).hom) := by
    change LocallyOfFiniteType T.hom
    rw [← Over.w eFinal.hom]
    infer_instance
  have hm : 0 < S.m := by have := S.three_le; omega
  obtain ⟨oN⟩ := field_source_monomial_chart_orientation (B (Fin.last r))
    (η (Fin.last r)) U hηU (h + 1) S.m hm z hEt α ε v hv hgen
  let j₀ : Over.mk (affineSpecStructureMap N) ⟶ T :=
    fieldSourceNormalizationChartMap (B (Fin.last r)) (η (Fin.last r)) U hηU
  letI : IsOpenImmersion j₀.left :=
    fieldSourceNormalizationChartMap_isOpenImmersion (B (Fin.last r)) (η (Fin.last r)) U hηU
  let j := j₀ ≫ eFinal.hom
  letI : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion (j₀.left ≫ eFinal.hom.left))
  let V := j.left.opensRange
  letI : IsAffine (Over.mk (affineSpecStructureMap N)).left :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of N)))
  let E := openImmersionImageIso j
  letI : IsAffine V.toScheme := IsAffine.of_isIso E.inv.left
  obtain ⟨oV⟩ := homeomorph_transport_coherent_orientation
    (TopCat.of (ComplexPoint (Over.mk (affineSpecStructureMap N))))
    (TopCat.of (ComplexPoint (openScheme W V))) (Point.isoMapHomeomorph E) (2 * (h + 1)) oN
  have hxrange : (Point.map eFinal.inv x).underlying ∈ Set.range j₀.left := by
    have H := fieldSourceNormalizationChartMap_range (B (Fin.last r)) (η (Fin.last r)) U hηU
    change Set.range j₀.left = _ at H
    rw [H]
    change (η (Fin.last r)).fromNormalization (eFinal.inv.left x.underlying) ∈ U.1
    exact hxU
  obtain ⟨p, hp⟩ := hxrange
  have hxV : x.underlying ∈ V := by
    change x.underlying ∈ Set.range j.left
    refine ⟨p, ?_⟩
    change eFinal.hom.left (j₀.left p) = x.underlying
    rw [hp]
    have H := congrArg (fun f : W ⟶ W => (Point.map f x).underlying) eFinal.inv_hom_id
    simp only [Point.map_comp_apply, Point.underlying_map] at H
    change eFinal.hom.left (eFinal.inv.left x.underlying) = x.underlying at H
    exact H
  exact ⟨⟨V, (inferInstance : IsAffine V.toScheme)⟩, hxV, ⟨oV⟩⟩

#print axioms retained_final_locally_oriented
end HodgeLean.Foundations.QuotientDuality
