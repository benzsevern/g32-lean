import HodgeLean.Adapters.F1575Powers
import HodgeLean.Foundations.WeilPowerDescent

/-! # Forward generation for exterior Hodge classes of all powers

The Hodge-group equality remains an explicit premise. The Weil generators
come from the original member and retain degree six for every power.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 1600000
open CategoryTheory AlgebraicGeometry ComplexPoint
open scoped TensorProduct
namespace HodgeLean.Adapters
open RealDefs Foundations Foundations.WeilPower InvariantsExterior

variable {X : Over (Spec ↧ℂ)} [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
  {μ : CupProduct X} [GrpObj X]
  {hF : FiniteBetti X} {hB : BettiDeRhamIso X} {hD : HodgeDecomposition X}
  {hT : TorusCohomology μ}
  {A : letI := hT.finite
    HodgeBlocks.WeilAction (abelianVarietyCohomologyOf hF hB hD hT).weight1 3}
  {η : HQ X 2}

private theorem power_topLines (hM : IsMemberOfM hF hB hD hT A η) (n : ℕ)
    (hn : letI := hT.finite
      Module.finrank ℂ ↥(A.Vs ⊓ (abelianVarietyCohomologyOf hF hB hD hT).weight1.H (1, 0)) +
        Module.finrank ℂ ↥(A.Vs ⊓ (abelianVarietyCohomologyOf hF hB hD hT).weight1.H (1, 0)) = n) :
    letI := hT.finite
    exteriorSpanC (hn ▸ A.weilClasses (h10_sup_h01_eq_top hF hB hD hT) hM.isWeilType) =
      LinearMap.range (exteriorPower.map n A.Vs.subtype) ⊔
        LinearMap.range (exteriorPower.map n A.Vsbar.subtype) := by
  let := hT.finite
  subst n
  exact weilClasses_baseChange_eq_topLines A
    (h10_sup_h01_eq_top hF hB hD hT) hM.isWeilType (by norm_num)

private theorem power_weil_pullback (hM : IsMemberOfM hF hB hD hT A η) (m n : ℕ)
    (hn : letI := hT.finite
      Module.finrank ℂ ↥(A.Vs ⊓ (abelianVarietyCohomologyOf hF hB hD hT).weight1.H (1, 0)) +
        Module.finrank ℂ ↥(A.Vs ⊓ (abelianVarietyCohomologyOf hF hB hD hT).weight1.H (1, 0)) = n) :
    letI := hT.finite
    ∀ r s w, w ∈ (hn ▸ A.weilClasses (h10_sup_h01_eq_top hF hB hD hT) hM.isWeilType) →
      exteriorPower.map n (weilPowerPullback A.J r s) w ∈
        f1575PowerHodgeTwoPulledWeilSpan hM m n := by
  let := hT.finite
  subst n
  exact f1575Power_weil_pullback_mem hM m

private theorem power_map_mem_range {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (f : V →ₗ[ℂ] W) (P : Submodule ℂ W)
    (hf : ∀ x, f x ∈ P) (k : ℕ) (v : ⋀[ℂ]^k V) :
    exteriorPower.map k f v ∈ LinearMap.range (exteriorPower.map k P.subtype) := by
  refine ⟨exteriorPower.map k (f.codRestrict P hf) v, ?_⟩
  rw [← LinearMap.comp_apply, ← exteriorPower.map_comp]
  rfl

/-- Every complex vector determinant on a power is in the complex span of
pullbacks of the original rational Weil classes. -/
theorem f1575Power_detW_mem (hM : IsMemberOfM hF hB hD hT A η)
    (m : ℕ) (a : Fin m → ℂ) :
    letI := hT.finite
    let e := polarizedSplitting (polarizationForm hT hM.nondegenerate)
      (nondegenerate_polarizationForm hT hM.nondegenerate) A.J A.J_sq
      (polarizationForm_skew hT hM.nondegenerate hM.rosati)
    let n := Module.finrank ℂ (Module.End.eigenspace (A.J.baseChange ℂ) root)
    (exteriorEquiv n (powerModel m e)).symm (detW a) ∈
      exteriorSpanC (f1575PowerHodgeTwoPulledWeilSpan hM m n) := by
  let := hT.finite
  let W := Module.End.eigenspace (A.J.baseChange ℂ) root
  let e := polarizedSplitting (polarizationForm hT hM.nondegenerate)
    (nondegenerate_polarizationForm hT hM.nondegenerate) A.J A.J_sq
    (polarizationForm_skew hT hM.nondegenerate hM.rosati)
  let n := Module.finrank ℂ W
  have hn : Module.finrank ℂ ↥(A.Vs ⊓
      (abelianVarietyCohomologyOf hF hB hD hT).weight1.H (1, 0)) +
      Module.finrank ℂ ↥(A.Vs ⊓
      (abelianVarietyCohomologyOf hF hB hD hT).weight1.H (1, 0)) = n := by
    simpa only [two_mul] using (f1575Member_middleDegree hM).symm
  let T : Submodule ℚ (⋀[ℚ]^n (HQ X 1)) :=
    hn ▸ A.weilClasses (h10_sup_h01_eq_top hF hB hD hT) hM.isWeilType
  let P := f1575PowerHodgeTwoPulledWeilSpan hM m n
  let Q := (exteriorSpanC P).comap (exteriorEquiv n (powerModel m e)).symm.toLinearMap
  change detW a ∈ Q
  apply (show Submodule.span ℂ (Set.range (fun r : Fin m → ℚ =>
    detW (K := ℂ) (W := W) (U' := Fin m → ℂ) (fun i => (r i : ℂ)))) ≤ Q from ?_)
    (detW_mem_span_rat a)
  apply Submodule.span_le.mpr
  rintro _ ⟨r, rfl⟩
  apply detWOf_rat_mem_exteriorSpanC A.J e (polarizedSplitting_J _ _ _ _ _) T P
    (power_weil_pullback hM m n hn) _ _ r
  rw [show exteriorSpanC T = _ from power_topLines hM n hn]
  apply Submodule.mem_sup_left
  apply power_map_mem_range
  intro w
  change e.symm (w, 0) ∈ A.Vs
  simp only [e, polarizedSplitting_symm_apply, map_zero, Submodule.coe_zero, add_zero]
  rw [← f1575Member_vs (A := A)]
  exact w.property

/-- Every complex dual determinant on a power is in the complex span of
pullbacks of the original rational Weil classes. -/
theorem f1575Power_detWDual_mem (hM : IsMemberOfM hF hB hD hT A η)
    (m : ℕ) (a : Fin m → ℂ) :
    letI := hT.finite
    let e := polarizedSplitting (polarizationForm hT hM.nondegenerate)
      (nondegenerate_polarizationForm hT hM.nondegenerate) A.J A.J_sq
      (polarizationForm_skew hT hM.nondegenerate hM.rosati)
    let n := Module.finrank ℂ (Module.End.eigenspace (A.J.baseChange ℂ) root)
    (exteriorEquiv n (powerModel m e)).symm (detWDual a) ∈
      exteriorSpanC (f1575PowerHodgeTwoPulledWeilSpan hM m n) := by
  let := hT.finite
  let W := Module.End.eigenspace (A.J.baseChange ℂ) root
  let e := polarizedSplitting (polarizationForm hT hM.nondegenerate)
    (nondegenerate_polarizationForm hT hM.nondegenerate) A.J A.J_sq
    (polarizationForm_skew hT hM.nondegenerate hM.rosati)
  let n := Module.finrank ℂ W
  have hn : Module.finrank ℂ ↥(A.Vs ⊓
      (abelianVarietyCohomologyOf hF hB hD hT).weight1.H (1, 0)) +
      Module.finrank ℂ ↥(A.Vs ⊓
      (abelianVarietyCohomologyOf hF hB hD hT).weight1.H (1, 0)) = n := by
    simpa only [two_mul] using (f1575Member_middleDegree hM).symm
  let T : Submodule ℚ (⋀[ℚ]^n (HQ X 1)) :=
    hn ▸ A.weilClasses (h10_sup_h01_eq_top hF hB hD hT) hM.isWeilType
  let P := f1575PowerHodgeTwoPulledWeilSpan hM m n
  let Q := (exteriorSpanC P).comap (exteriorEquiv n (powerModel m e)).symm.toLinearMap
  change detWDual a ∈ Q
  apply (show Submodule.span ℂ (Set.range (fun r : Fin m → ℚ =>
    detWDual (K := ℂ) (W := W) (U := Fin m → ℂ) (fun i => (r i : ℂ)))) ≤ Q from ?_)
    (detWDual_mem_span_rat a)
  apply Submodule.span_le.mpr
  rintro _ ⟨r, rfl⟩
  apply detWDualOf_rat_mem_exteriorSpanC A.J e (polarizedSplitting_J _ _ _ _ _) T P
    (power_weil_pullback hM m n hn) _ _ r
  rw [show exteriorSpanC T = _ from power_topLines hM n hn]
  apply Submodule.mem_sup_right
  apply power_map_mem_range
  intro w
  change e.symm (0, w) ∈ A.Vsbar
  simp only [e, polarizedSplitting_symm_apply, Submodule.coe_zero, zero_add]
  simp [HodgeBlocks.WeilAction.Vsbar, HodgeBlocks.WeilAction.omegaC, root]

/-- Under the Hodge-group input, all contraction generators lie in the
complexified rational degree-two Hodge space, hence in the proposed generating span. -/
theorem f1575Power_theta_mem (hM : IsMemberOfM hF hB hD hT A η)
    (hSU : F1575MemberHodgeGroupIsSU hF hB hD hT A hM)
    (m : ℕ) (u u' : Fin m → ℂ) :
    letI := hT.finite
    let e := polarizedSplitting (polarizationForm hT hM.nondegenerate)
      (nondegenerate_polarizationForm hT hM.nondegenerate) A.J A.J_sq
      (polarizationForm_skew hT hM.nondegenerate hM.rosati)
    (exteriorEquiv 2 (powerModel m e)).symm (theta u u') ∈
      exteriorSpanC (f1575PowerHodgeTwoPulledWeilSpan hM m 2) := by
  let := hT.finite
  let S := abelianVarietyCohomologyOf hF hB hD hT
  let e := polarizedSplitting (polarizationForm hT hM.nondegenerate)
    (nondegenerate_polarizationForm hT hM.nondegenerate) A.J A.J_sq
    (polarizationForm_skew hT hM.nondegenerate hM.rosati)
  have hθ : (exteriorEquiv 2 (powerModel m e)).symm (theta u u') ∈
      exteriorHodgeClasses S.weight1.H S.weight1.isInternal m 2 := by
    rw [exteriorHodgeClasses_eq_generated S.weight1.H S.weight1.isInternal
      (polarizationForm hT hM.nondegenerate)
      (nondegenerate_polarizationForm hT hM.nondegenerate) A.J A.J_sq
      (polarizationForm_skew hT hM.nondegenerate hM.rosati) m 2 hSU]
    exact ⟨theta u u', Submodule.subset_span (GeneratorProduct.theta u u'), rfl⟩
  exact exteriorSpanC_mono (isDivisorPulledWeilClosed_span A.J
    (rationalExteriorHodge S.weight1.H S.weight1.isInternal m 2)
    (A.weilClasses (h10_sup_h01_eq_top hF hB hD hT) hM.isWeilType)).divisor_le hθ

/-- Forward generation for every exterior degree of every power, as an
implication from `hSU`. The rational generators are degree-two Hodge classes
and pullbacks of the original member's degree-six Weil classes.
Source: F-1575 / TR54 §3; van Geemen, *An introduction to the Hodge conjecture
for abelian varieties*, §§5–6, with the Hodge-group equality explicit. -/
theorem f1575Power_hodgeClasses_le_hodgeTwoPulledWeilSpan
    (hM : IsMemberOfM hF hB hD hT A η)
    (hSU : F1575MemberHodgeGroupIsSU hF hB hD hT A hM) (m k : ℕ) :
    letI := hT.finite
    let S := abelianVarietyCohomologyOf hF hB hD hT
    exteriorHodgeClasses S.weight1.H S.weight1.isInternal m k ≤
      ((f1575PowerHodgeTwoPulledWeilSpan hM m k).baseChange ℂ).map
        (exteriorBaseChange k).toLinearMap := by
  let := hT.finite
  let S := abelianVarietyCohomologyOf hF hB hD hT
  let e := polarizedSplitting (polarizationForm hT hM.nondegenerate)
    (nondegenerate_polarizationForm hT hM.nondegenerate) A.J A.J_sq
    (polarizationForm_skew hT hM.nondegenerate hM.rosati)
  let P := f1575PowerHodgeTwoPulledWeilSpan hM m
  have hP := isDivisorPulledWeilClosed_span A.J
    (rationalExteriorHodge S.weight1.H S.weight1.isInternal m 2)
    (A.weilClasses (h10_sup_h01_eq_top hF hB hD hT) hM.isWeilType)
  change exteriorHodgeClasses S.weight1.H S.weight1.isInternal m k ≤ exteriorSpanC (P k)
  rw [exteriorHodgeClasses_eq_generated S.weight1.H S.weight1.isInternal
    (polarizationForm hT hM.nondegenerate)
    (nondegenerate_polarizationForm hT hM.nondegenerate) A.J A.J_sq
    (polarizationForm_skew hT hM.nondegenerate hM.rosati) m k hSU]
  change (generatedDegree k).map (exteriorEquiv k (powerModel m e)).symm.toLinearMap ≤
    exteriorSpanC (P k)
  rw [Submodule.map_le_iff_le_comap]
  apply Submodule.span_le.mpr
  intro v hv
  change (exteriorEquiv k (powerModel m e)).symm v ∈ exteriorSpanC (P k)
  induction hv with
  | unit =>
    have hu := exteriorComplexify_mem hP.unit_mem
    rw [f1575_exteriorEquiv_symm, exteriorPower.map_apply_ιMulti]
    rw [exteriorComplexify_ιMulti] at hu
    convert hu using 1
    · rfl
    · congr 1
      funext i
      exact Fin.elim0 i
  | theta u u' => exact f1575Power_theta_mem hM hSU m u u'
  | detW a => exact f1575Power_detW_mem hM m a
  | detWDual a => exact f1575Power_detWDual_mem hM m a
  | @wedge i j v w hv hw ihv ihw =>
    simp only [f1575_exteriorEquiv_symm] at ihv ihw ⊢
    rw [f1575_exterior_map_wedge]
    exact exteriorSpanC_wedge (P i) (P j) (P (i + j))
      (fun v hv w hw => hP.wedge_mem i j v w hv hw) ihv ihw

#print axioms f1575Power_detW_mem
#print axioms f1575Power_detWDual_mem
#print axioms f1575Power_theta_mem
#print axioms f1575Power_hodgeClasses_le_hodgeTwoPulledWeilSpan

end HodgeLean.Adapters
