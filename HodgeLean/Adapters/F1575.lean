import HodgeLean.RealDefs.F1569
import HodgeLean.Foundations.WeilPowerClasses
import HodgeLean.Adapters.F1575Exterior
import HodgeLean.Adapters.F1575Products
import HodgeLean.Adapters.F1575Theta

/-!
# F-1575 assembly for one member of M

The Hodge-group input is an explicit Lie-algebra equality. Geometric
compatibility uses O5, `CupFiltered`, together with C1, C2, C4 and C7.
-/

noncomputable section
set_option maxHeartbeats 1600000
attribute [local instance 100] LieRing.ofAssociativeRing
open CategoryTheory AlgebraicGeometry ComplexPoint TopologicalSpace
open scoped TensorProduct

namespace HodgeLean.Adapters

open RealDefs Foundations Foundations.WeilPower

variable {X : Over (Spec ↧ℂ)} [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
  {μ : CupProduct X} [GrpObj X]

/-- The explicit Hodge-group input for a member of `M`, using the package's
weight-one decomposition and the dual form of its polarization.

Source: specialization of `Foundations.WeilPower.complexSU` and
`Foundations.hodgeLieAlgebra` to `RealDefs.IsMemberOfM`.

Here `V = HQ X 1`, `H = S.weight1.H`, `hH = S.weight1.isInternal`,
`E = polarizationForm hT hM.nondegenerate`, `J = A.J`, `hJ = A.J_sq`;
nondegeneracy and skewness are proved by the F-1569 layer. This definition is
only the Lie-algebra equality; in particular it does not hide O5, the
cup/Hodge comparison, or the generation conclusion. It is not tagged. -/
def F1575MemberHodgeGroupIsSU (hF : FiniteBetti X) (hB : BettiDeRhamIso X)
    (hD : HodgeDecomposition X) (hT : TorusCohomology μ)
    (A : letI := hT.finite
      HodgeBlocks.WeilAction (abelianVarietyCohomologyOf hF hB hD hT).weight1 3)
    {η : HQ X 2} (hM : IsMemberOfM hF hB hD hT A η) : Prop :=
  letI := hT.finite
  let S := abelianVarietyCohomologyOf hF hB hD hT
  complexSpan (hodgeLieAlgebra S.weight1.H S.weight1.isInternal).toSubmodule =
    (complexSU (polarizationForm hT hM.nondegenerate)
      (nondegenerate_polarizationForm hT hM.nondegenerate) A.J A.J_sq
      (polarizationForm_skew hT hM.nondegenerate hM.rosati)).toSubmodule

example (hF : FiniteBetti X) (hB : BettiDeRhamIso X) (hD : HodgeDecomposition X)
    (hT : TorusCohomology μ)
    (A : letI := hT.finite
      HodgeBlocks.WeilAction (abelianVarietyCohomologyOf hF hB hD hT).weight1 3)
    {η : HQ X 2} (hM : IsMemberOfM hF hB hD hT A η) : Prop :=
  F1575MemberHodgeGroupIsSU hF hB hD hT A hM

private theorem f1575_map_mem_range {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (f : V →ₗ[ℂ] W) (P : Submodule ℂ W)
    (hf : ∀ x, f x ∈ P) (k : ℕ) (v : ⋀[ℂ]^k V) :
    exteriorPower.map k f v ∈ LinearMap.range (exteriorPower.map k P.subtype) := by
  refine ⟨exteriorPower.map k (f.codRestrict P hf) v, ?_⟩
  rw [← LinearMap.comp_apply, ← exteriorPower.map_comp]
  rfl

section Member

variable {hF : FiniteBetti X} {hB : BettiDeRhamIso X} {hD : HodgeDecomposition X}
  {hT : TorusCohomology μ}
  {A : letI := hT.finite
    HodgeBlocks.WeilAction (abelianVarietyCohomologyOf hF hB hD hT).weight1 3}
  {η : HQ X 2}

/-- The one-copy invariant-theory model for this member's polarized Weil action.

Source: constructed here for F-1575 step 3 from the polarized splitting in
van Geemen, *An introduction to the Hodge conjecture for abelian varieties*, §5–6. -/
def f1575MemberModel (hM : IsMemberOfM hF hB hD hT A η) :
    letI := hT.finite
    (ℂ ⊗[ℚ] (HQ X 1 ⊗[ℚ] (Fin 1 → ℚ))) ≃ₗ[ℂ]
      InvariantsExterior.Space ℂ (Module.End.eigenspace (A.J.baseChange ℂ) root)
        (Fin 1 → ℂ) (Fin 1 → ℂ) :=
  letI := hT.finite
  powerModel 1 (polarizedSplitting (polarizationForm hT hM.nondegenerate)
    (nondegenerate_polarizationForm hT hM.nondegenerate) A.J A.J_sq
    (polarizationForm_skew hT hM.nondegenerate hM.rosati))

example (hM : IsMemberOfM hF hB hD hT A η) :
    letI := hT.finite
    (ℂ ⊗[ℚ] (HQ X 1 ⊗[ℚ] (Fin 1 → ℚ))) ≃ₗ[ℂ]
      InvariantsExterior.Space ℂ (Module.End.eigenspace (A.J.baseChange ℂ) root)
        (Fin 1 → ℂ) (Fin 1 → ℂ) :=
  f1575MemberModel hM

/-- Carry an invariant-theory generator, in its actual degree, to geometric cohomology.

Source: constructed here for F-1575 step 3 by composing the member model with
the C7 single-copy cohomology comparison. -/
def f1575GeneratorCohomology (hM : IsMemberOfM hF hB hD hT A η) (k : ℕ) :
    letI := hT.finite
    (⋀[ℂ]^k (InvariantsExterior.Space ℂ (Module.End.eigenspace (A.J.baseChange ℂ) root)
      (Fin 1 → ℂ) (Fin 1 → ℂ))) ≃ₗ[ℂ] (ℂ ⊗[ℚ] HQ X k) :=
  letI := hT.finite
  (exteriorEquiv k (f1575MemberModel hM)).symm.trans (f1575SingleCopyCohomology hT k)

example (hM : IsMemberOfM hF hB hD hT A η) (k : ℕ) :
    letI := hT.finite
    (⋀[ℂ]^k (InvariantsExterior.Space ℂ (Module.End.eigenspace (A.J.baseChange ℂ) root)
      (Fin 1 → ℂ) (Fin 1 → ℂ))) ≃ₗ[ℂ] (ℂ ⊗[ℚ] HQ X k) :=
  f1575GeneratorCohomology hM k

/-- The single-copy polarized model, with its multiplicity factor removed.

Source: constructed here for F-1575 step 3 from `f1575MemberModel` and the
canonical one-copy complex equivalence. -/
def f1575MemberToH1 (hM : IsMemberOfM hF hB hD hT A η) :
    letI := hT.finite
    InvariantsExterior.Space ℂ (Module.End.eigenspace (A.J.baseChange ℂ) root)
      (Fin 1 → ℂ) (Fin 1 → ℂ) ≃ₗ[ℂ] (ℂ ⊗[ℚ] HQ X 1) :=
  letI := hT.finite
  (f1575MemberModel hM).symm.trans f1575SingleCopyComplex

example (hM : IsMemberOfM hF hB hD hT A η) :
    letI := hT.finite
    InvariantsExterior.Space ℂ (Module.End.eigenspace (A.J.baseChange ℂ) root)
      (Fin 1 → ℂ) (Fin 1 → ℂ) ≃ₗ[ℂ] (ℂ ⊗[ℚ] HQ X 1) :=
  f1575MemberToH1 hM

theorem f1575GeneratorCohomology_eq (hM : IsMemberOfM hF hB hD hT A η) (k : ℕ)
    (v : letI := hT.finite
      ⋀[ℂ]^k (InvariantsExterior.Space ℂ (Module.End.eigenspace (A.J.baseChange ℂ) root)
        (Fin 1 → ℂ) (Fin 1 → ℂ))) :
    letI := hT.finite
    f1575GeneratorCohomology hM k v = f1575ExteriorCohomology hT k
      (exteriorPower.map k (f1575MemberToH1 hM).toLinearMap v) := by
  let := hT.finite
  simp only [f1575GeneratorCohomology, LinearEquiv.trans_apply, f1575_exteriorEquiv_symm,
    f1575SingleCopyCohomology, f1575SingleCopyExterior]
  change f1575ExteriorCohomology hT k
    (exteriorPower.map k (f1575SingleCopyComplex (V := HQ X 1)).toLinearMap
      (exteriorPower.map k (f1575MemberModel hM).symm.toLinearMap v)) = _
  rw [← LinearMap.comp_apply, ← exteriorPower.map_comp]
  rfl

theorem f1575Member_vs :
    letI := hT.finite
    Module.End.eigenspace (A.J.baseChange ℂ) root = A.Vs := by
  let := hT.finite
  simp [HodgeBlocks.WeilAction.Vs, HodgeBlocks.WeilAction.omegaC, root]

/-- The normalized one-copy contraction is exactly the polarization class:
the rational multiple is `1`. This identity does not require the Hodge-group input. -/
theorem f1575_theta_eq_polarization (hM : IsMemberOfM hF hB hD hT A η) :
    letI := hT.finite
    f1575GeneratorCohomology hM 2
      (InvariantsExterior.theta (1 : Fin 1 → ℂ) (1 : Fin 1 → ℂ)) =
      (1 : ℂ) ⊗ₜ[ℚ] η := by
  let := hT.finite
  rw [f1575GeneratorCohomology_eq]
  have hh : exteriorPower.map 2 (f1575MemberToH1 hM).toLinearMap
      (InvariantsExterior.theta (1 : Fin 1 → ℂ) (1 : Fin 1 → ℂ)) =
      HodgeBlocks.complexifyWedge 2 (polarizationVec hT η) := by
    let e := polarizedSplitting (polarizationForm hT hM.nondegenerate)
      (nondegenerate_polarizationForm hT hM.nondegenerate) A.J A.J_sq
      (polarizationForm_skew hT hM.nondegenerate hM.rosati)
    let b := Module.finBasis ℂ (Module.End.eigenspace (A.J.baseChange ℂ) root)
    change exteriorPower.map 2 ((powerModel 1 e).symm.trans f1575SingleCopyComplex).toLinearMap _ = _
    rw [f1575_singleCopy_theta e b]
    apply f1575_split_sum_eq_complexify hM.nondegenerate e
    exact polarizedSplitting_form _ _ _ _ _ (isAlt_polarizationForm hT hM.nondegenerate)
  rw [hh, f1575ExteriorCohomology_complexify, cupWedgeMap_polarizationVec]

theorem f1575Member_rank (hM : IsMemberOfM hF hB hD hT A η) :
    letI := hT.finite
    Module.finrank ℂ (Module.End.eigenspace (A.J.baseChange ℂ) root) = 6 := by
  let := hT.finite
  rw [f1575Member_vs, A.finrank_Vs_eq_twice_inf_H10
    (h10_sup_h01_eq_top hF hB hD hT) hM.isWeilType, hM.finrank_eq_three]

theorem f1575Member_middleDegree (hM : IsMemberOfM hF hB hD hT A η) :
    letI := hT.finite
    Module.finrank ℂ (Module.End.eigenspace (A.J.baseChange ℂ) root) =
      2 * Module.finrank ℂ ↥(A.Vs ⊓ (abelianVarietyCohomologyOf hF hB hD hT).weight1.H (1, 0)) := by
  let := hT.finite
  rw [f1575Member_vs, A.finrank_Vs_eq_twice_inf_H10
    (h10_sup_h01_eq_top hF hB hD hT) hM.isWeilType, two_mul]

theorem f1575MemberToH1_vector_mem (hM : IsMemberOfM hF hB hD hT A η)
    (u : Fin 1 → ℂ) (x : letI := hT.finite; Module.End.eigenspace (A.J.baseChange ℂ) root) :
    letI := hT.finite
    f1575MemberToH1 hM (InvariantsExterior.vectorIn u x) ∈ A.Vs := by
  let := hT.finite
  unfold f1575MemberToH1 f1575MemberModel
  rw [LinearEquiv.trans_apply, f1575_singleCopyModel_symm_vector,
    polarizedSplitting_symm_apply, map_zero, Submodule.coe_zero, add_zero]
  apply A.Vs.smul_mem
  rw [← f1575Member_vs]
  exact x.property

theorem f1575MemberToH1_dual_mem (hM : IsMemberOfM hF hB hD hT A η)
    (u : Fin 1 → ℂ)
    (x : letI := hT.finite; Module.Dual ℂ (Module.End.eigenspace (A.J.baseChange ℂ) root)) :
    letI := hT.finite
    f1575MemberToH1 hM (InvariantsExterior.dualIn u x) ∈ A.Vsbar := by
  let := hT.finite
  unfold f1575MemberToH1 f1575MemberModel
  rw [LinearEquiv.trans_apply, f1575_singleCopyModel_symm_dual,
    polarizedSplitting_symm_apply, Submodule.coe_zero, zero_add]
  apply A.Vsbar.smul_mem
  simpa [HodgeBlocks.WeilAction.Vsbar, HodgeBlocks.WeilAction.omegaC, root] using
    ((weilDuality (polarizationForm hT hM.nondegenerate)
      (nondegenerate_polarizationForm hT hM.nondegenerate) A.J A.J_sq
      (polarizationForm_skew hT hM.nondegenerate hM.rosati)).symm x).property

/-- Any vector in the two top eigenlines maps into the complexified rational Weil classes. -/
theorem f1575_topLines_mem_weil (hM : IsMemberOfM hF hB hD hT A η) {n : ℕ}
    (h : letI := hT.finite; n = Module.finrank ℂ
      ↥(A.Vs ⊓ (abelianVarietyCohomologyOf hF hB hD hT).weight1.H (1, 0)) +
        Module.finrank ℂ ↥(A.Vs ⊓ (abelianVarietyCohomologyOf hF hB hD hT).weight1.H (1, 0)))
    (v : ⋀[ℂ]^n (ℂ ⊗[ℚ] HQ X 1))
    (hv : letI := hT.finite
      v ∈ LinearMap.range (exteriorPower.map n A.Vs.subtype) ⊔
        LinearMap.range (exteriorPower.map n A.Vsbar.subtype)) :
    letI := hT.finite
    (HQ.castEquiv X (h.trans (two_mul _).symm)).toLinearMap.baseChange ℂ
      (f1575ExteriorCohomology hT n v) ∈
      (weilClassOf hF hB hD hT A hM.isWeilType).baseChange ℂ := by
  let := hT.finite
  subst n
  rw [weilClassOf, f1575_baseChange_map]
  refine ⟨(HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv _).symm v, ?_, ?_⟩
  · have hs := weilClasses_baseChange_eq_topLines A
      (h10_sup_h01_eq_top hF hB hD hT) hM.isWeilType (by norm_num)
    rw [← hs, Submodule.mem_map_equiv] at hv
    exact hv
  · rw [LinearMap.baseChange_comp, LinearMap.comp_apply, f1575ExteriorCohomology_eq_baseChange]

theorem f1575_detW_range (hM : IsMemberOfM hF hB hD hT A η) (u : Fin 1 → ℂ) :
    letI := hT.finite
    let n := Module.finrank ℂ (Module.End.eigenspace (A.J.baseChange ℂ) root)
    exteriorPower.map n (f1575MemberToH1 hM).toLinearMap (InvariantsExterior.detW u) ∈
      LinearMap.range (exteriorPower.map n A.Vs.subtype) := by
  let := hT.finite
  dsimp only
  rw [InvariantsExterior.detW, InvariantsExterior.detWOf,
    ← LinearMap.comp_apply, ← exteriorPower.map_comp]
  exact f1575_map_mem_range _ A.Vs (f1575MemberToH1_vector_mem hM u) _ _

theorem f1575_detWDual_range (hM : IsMemberOfM hF hB hD hT A η) (u : Fin 1 → ℂ) :
    letI := hT.finite
    let n := Module.finrank ℂ (Module.End.eigenspace (A.J.baseChange ℂ) root)
    exteriorPower.map n (f1575MemberToH1 hM).toLinearMap (InvariantsExterior.detWDual u) ∈
      LinearMap.range (exteriorPower.map n A.Vsbar.subtype) := by
  let := hT.finite
  dsimp only
  rw [InvariantsExterior.detWDual, InvariantsExterior.detWDualOf,
    ← LinearMap.comp_apply, ← exteriorPower.map_comp]
  exact f1575_map_mem_range _ A.Vsbar (f1575MemberToH1_dual_mem hM u) _ _

/-- The positive determinant generator lies in the complex span of the rational Weil classes. -/
theorem f1575_detW_mem_weil (hM : IsMemberOfM hF hB hD hT A η) (u : Fin 1 → ℂ) :
    letI := hT.finite
    let n := Module.finrank ℂ (Module.End.eigenspace (A.J.baseChange ℂ) root)
    (HQ.castEquiv X (f1575Member_middleDegree hM)).toLinearMap.baseChange ℂ
      (f1575GeneratorCohomology hM n (InvariantsExterior.detW u)) ∈
      (weilClassOf hF hB hD hT A hM.isWeilType).baseChange ℂ := by
  let := hT.finite
  dsimp only
  rw [f1575GeneratorCohomology_eq]
  exact f1575_topLines_mem_weil hM ((f1575Member_middleDegree hM).trans (two_mul _)) _
    (Submodule.mem_sup_left (f1575_detW_range hM u))

/-- The dual determinant generator lies in the same complexified rational Weil space. -/
theorem f1575_detWDual_mem_weil (hM : IsMemberOfM hF hB hD hT A η) (u : Fin 1 → ℂ) :
    letI := hT.finite
    let n := Module.finrank ℂ (Module.End.eigenspace (A.J.baseChange ℂ) root)
    (HQ.castEquiv X (f1575Member_middleDegree hM)).toLinearMap.baseChange ℂ
      (f1575GeneratorCohomology hM n (InvariantsExterior.detWDual u)) ∈
      (weilClassOf hF hB hD hT A hM.isWeilType).baseChange ℂ := by
  let := hT.finite
  dsimp only
  rw [f1575GeneratorCohomology_eq]
  exact f1575_topLines_mem_weil hM ((f1575Member_middleDegree hM).trans (two_mul _)) _
    (Submodule.mem_sup_right (f1575_detWDual_range hM u))

/-- Abstract generation transported to geometric Hodge classes for one member, under O5. -/
theorem f1575_generated_map_eq_hdg (hM : IsMemberOfM hF hB hD hT A η)
    (hC : CupFiltered X μ) (hSU : F1575MemberHodgeGroupIsSU hF hB hD hT A hM) (p : ℕ) :
    letI := hT.finite
    (InvariantsExterior.generatedDegree (K := ℂ)
      (W := Module.End.eigenspace (A.J.baseChange ℂ) root)
      (U := Fin 1 → ℂ) (U' := Fin 1 → ℂ) (2 * p)).map
        (f1575GeneratorCohomology hM (2 * p)).toLinearMap = (Hdg^p(X; ℚ)).baseChange ℂ := by
  let := hT.finite
  have hg := exteriorHodgeClasses_eq_generated
    (abelianVarietyCohomologyOf hF hB hD hT).weight1.H
    (abelianVarietyCohomologyOf hF hB hD hT).weight1.isInternal
    (polarizationForm hT hM.nondegenerate)
    (nondegenerate_polarizationForm hT hM.nondegenerate) A.J A.J_sq
    (polarizationForm_skew hT hM.nondegenerate hM.rosati) 1 (2 * p) hSU
  rw [← f1575_exteriorHodgeClasses_map_eq hF hB hD hT hC p, hg]
  exact Submodule.map_comp _ _ _

/-- The transported quadratic contraction lies in the complexified divisor Hodge classes. -/
theorem f1575_theta_mem_divisor (hM : IsMemberOfM hF hB hD hT A η)
    (hC : CupFiltered X μ) (hSU : F1575MemberHodgeGroupIsSU hF hB hD hT A hM)
    (u u' : Fin 1 → ℂ) :
    letI := hT.finite
    f1575GeneratorCohomology hM 2 (InvariantsExterior.theta u u') ∈
      (Hdg^1(X; ℚ)).baseChange ℂ := by
  let := hT.finite
  rw [← f1575_generated_map_eq_hdg hM hC hSU 1]
  exact ⟨_, Submodule.subset_span (InvariantsExterior.GeneratorProduct.theta u u'), rfl⟩

/-- At multiplicity one the prescribed `theta 1 1` lands in the divisor part of the span. -/
example (hM : IsMemberOfM hF hB hD hT A η) (hC : CupFiltered X μ)
    (hSU : F1575MemberHodgeGroupIsSU hF hB hD hT A hM) :
    letI := hT.finite
    f1575GeneratorCohomology hM 2
      (InvariantsExterior.theta (1 : Fin 1 → ℂ) (1 : Fin 1 → ℂ)) ∈
      (divisorWeilSpan hF hB hD hT A hM.isWeilType 1).baseChange ℂ := by
  let := hT.finite
  exact Submodule.baseChange_mono ℂ (hdg_one_le_divisorWeilSpan hF hB hD hT A hM.isWeilType)
    (f1575_theta_mem_divisor hM hC hSU 1 1)

theorem f1575GeneratorCohomology_wedge (hM : IsMemberOfM hF hB hD hT A η) (i j : ℕ)
    (v : letI := hT.finite
      ⋀[ℂ]^i (InvariantsExterior.Space ℂ (Module.End.eigenspace (A.J.baseChange ℂ) root)
        (Fin 1 → ℂ) (Fin 1 → ℂ)))
    (w : letI := hT.finite
      ⋀[ℂ]^j (InvariantsExterior.Space ℂ (Module.End.eigenspace (A.J.baseChange ℂ) root)
        (Fin 1 → ℂ) (Fin 1 → ℂ))) :
    letI := hT.finite
    f1575GeneratorCohomology hM (i + j) (exteriorPower.wedge ℂ _ i j v w) =
      μ.cupC rfl (f1575GeneratorCohomology hM i v) (f1575GeneratorCohomology hM j w) := by
  let := hT.finite
  simp only [f1575GeneratorCohomology_eq, f1575_exterior_map_wedge,
    f1575ExteriorCohomology_wedge]

theorem f1575GeneratorCohomology_unit (hM : IsMemberOfM hF hB hD hT A η) :
    letI := hT.finite
    f1575GeneratorCohomology hM 0 (exteriorPower.ιMulti ℂ 0 Fin.elim0) =
      (1 : ℂ) ⊗ₜ[ℚ] unitClass X := by
  let := hT.finite
  rw [f1575GeneratorCohomology_eq, exteriorPower.map_apply_ιMulti]
  have he : (f1575MemberToH1 hM).toLinearMap ∘ Fin.elim0 =
      (fun i : Fin 0 => (1 : ℂ) ⊗ₜ[ℚ] (Fin.elim0 i : HQ X 1)) := by
    funext i
    exact Fin.elim0 i
  rw [he, ← HodgeBlocks.complexifyWedge_ιMulti, f1575ExteriorCohomology_complexify,
    CupProduct.cupWedgeMap_zero]
  rfl

/-- Every prescribed wedge product lies in the complexified divisor-Weil family. -/
theorem f1575GeneratorProduct_mem (hM : IsMemberOfM hF hB hD hT A η)
    (hC : CupFiltered X μ) (hSU : F1575MemberHodgeGroupIsSU hF hB hD hT A hM)
    {k : ℕ} {v : letI := hT.finite
      ⋀[ℂ]^k (InvariantsExterior.Space ℂ (Module.End.eigenspace (A.J.baseChange ℂ) root)
        (Fin 1 → ℂ) (Fin 1 → ℂ))}
    (hv : letI := hT.finite; InvariantsExterior.GeneratorProduct k v) :
    letI := hT.finite
    f1575GeneratorCohomology hM k v ∈
      f1575EvenCohomologySpan (divisorWeilSpan hF hB hD hT A hM.isWeilType) k := by
  let := hT.finite
  induction hv with
  | unit =>
    rw [f1575GeneratorCohomology_unit]
    change (1 : ℂ) ⊗ₜ[ℚ] unitClass X ∈
      f1575EvenCohomologySpan (divisorWeilSpan hF hB hD hT A hM.isWeilType) (2 * 0)
    rw [f1575EvenCohomologySpan_even]
    exact Submodule.tmul_mem_baseChange_of_mem 1
      (unitClass_mem_divisorWeilSpan hF hB hD hT A hM.isWeilType)
  | theta u u' =>
    change _ ∈ f1575EvenCohomologySpan
      (divisorWeilSpan hF hB hD hT A hM.isWeilType) (2 * 1)
    rw [f1575EvenCohomologySpan_even]
    exact Submodule.baseChange_mono ℂ (hdg_one_le_divisorWeilSpan hF hB hD hT A hM.isWeilType)
      (f1575_theta_mem_divisor hM hC hSU u u')
  | detW u =>
    refine Or.inr ⟨_, f1575Member_middleDegree hM, ?_⟩
    exact Submodule.baseChange_mono ℂ (weilClassOf_le_divisorWeilSpan hF hB hD hT A hM.isWeilType)
      (f1575_detW_mem_weil hM u)
  | detWDual u =>
    refine Or.inr ⟨_, f1575Member_middleDegree hM, ?_⟩
    exact Submodule.baseChange_mono ℂ (weilClassOf_le_divisorWeilSpan hF hB hD hT A hM.isWeilType)
      (f1575_detWDual_mem_weil hM u)
  | @wedge i j v w _ _ ihv ihw =>
    rw [f1575GeneratorCohomology_wedge]
    exact f1575EvenCohomologySpan_cup (divisorWeilSpan hF hB hD hT A hM.isWeilType)
      (fun h a b ha hb => cup_mem_divisorWeilSpan hF hB hD hT A hM.isWeilType h a b ha hb)
      rfl ihv ihw

set_option backward.isDefEq.respectTransparency false in
/-- F-1575 case `m = 1`: the generation hypothesis for this member is the
implication from `hSU`, given `hM`, `hC` (O5), `hW`, and C1/C2/C4/C7 through
`hF`, `hB`, `hD`, and `hT`. The source multiplicity
is fixed to `Fin 1`; this is not generation by the middle-degree Weil classes
of a higher power with diagonal action.

The geometric comparison is `f1575_exteriorHodgeClasses_map_eq`. The quadratic
generators lie in the divisor part, both determinant generators lie in the
complexification of the exact rational `weilClassOf`, and cup closure handles
all products. Faithfully flat scalar extension then gives the rational claim.
No algebraicity premise is needed for this generation theorem. -/
theorem hodgeRingGeneratedByDivisorsAndWeil_of_hSU
    (hM : IsMemberOfM hF hB hD hT A η) (hC : CupFiltered X μ)
    (hSU : F1575MemberHodgeGroupIsSU hF hB hD hT A hM)
    (hW : letI := hT.finite; A.IsWeilType := hM.isWeilType) :
    HodgeRingGeneratedByDivisorsAndWeil hF hB hD hT A hW := by
  let := hT.finite
  constructor
  intro p
  apply (Submodule.baseChange_le_iff (A := ℂ)).mp
  rw [← f1575_generated_map_eq_hdg hM hC hSU p, Submodule.map_le_iff_le_comap,
    InvariantsExterior.generatedDegree, Submodule.span_le]
  intro v hv
  have hh := f1575GeneratorProduct_mem hM hC hSU hv
  rwa [f1575EvenCohomologySpan_even] at hh

end Member

/-- F-1575 case `m = 1`: the implication from `hSU` (the Hodge-group input,
`SU_H` for the member), given `F1569StatementFor cup`, C9, Lefschetz (1,1),
`hM`, the package C1/C2/C4/C7, and O5.

| premise | role |
| --- | --- |
| `hF1569 : F1569StatementFor cup` | algebraicity of the rational Weil classes; assumed |
| `hSU : F1575MemberHodgeGroupIsSU … hM` | the explicit Hodge-group Lie-algebra equality |
| `hF`, `hB`, `hD`, `hT` | C1, C2, C4, C7 |
| `hC : CupFiltered X (cup X)` | O5, compatibility of cup product with Hodge filtration |
| `hC9 : CycleClassMultiplicative (cup X)` | C9, cup closure of algebraic classes |
| `h11 : LefschetzOneOneHyp` | Lefschetz (1,1), algebraicity of divisor Hodge classes |
| `hM : IsMemberOfM … A η` | the polarized Weil-type sixfold in `M` |

The conclusion concerns this member only, not its powers with diagonal action.
Relation to the goal: HC no distance; AV milestone no distance. -/
@[hodge_milestone] theorem hdg_le_span_of_f1569Statement_of_hSU
    (cup : ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
      [IsProjective X.hom], CupProduct X) (hF1569 : F1569StatementFor cup)
    (hF : FiniteBetti X) (hB : BettiDeRhamIso X) (hD : HodgeDecomposition X)
    (hT : TorusCohomology (cup X))
    (A : letI := hT.finite
      HodgeBlocks.WeilAction (abelianVarietyCohomologyOf hF hB hD hT).weight1 3)
    {η : HQ X 2} (hM : IsMemberOfM hF hB hD hT A η)
    (hC : CupFiltered X (cup X)) (hSU : F1575MemberHodgeGroupIsSU hF hB hD hT A hM)
    (hC9 : CycleClassMultiplicative (cup X)) (h11 : LefschetzOneOneHyp) :
    ∀ p : ℕ, Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p :=
  hdg_le_span_of_f1569Statement cup hF1569 hF hB hD hT A hM
    (hodgeRingGeneratedByDivisorsAndWeil_of_hSU hM hC hSU) hC9 h11

end HodgeLean.Adapters
