import HodgeLean.Adapters.PolarizedHodgeAbelianDefs
import HodgeLean.Foundations.EQWCore
import HodgeLean.Adapters.AutomorphyChernHQ
import HodgeLean.Adapters.HodgeLieAlgebra
import HodgeLean.Adapters.F1575Exterior

/-! # Proof obligations for the polarized weight-one specification -/

noncomputable section

namespace HodgeLean.Adapters

export HodgeLean.Foundations.WeilPower (root complexSU)
attribute [instance 100] LieRing.ofAssociativeRing

open HodgeLean.Foundations HodgeLean.RealDefs HodgeBlocks
open HodgeLean.Foundations.Symplectic HodgeLean.Foundations.WeilHermitian
  HodgeLean.Foundations.HermitianForm
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Module
open scoped TensorProduct

private def pol1RealIn {V : Type*} [AddCommGroup V] [Module ℚ V] :
    ℝ ⊗[ℚ] V →ₗ[ℝ] ℂ ⊗[ℚ] V :=
  TensorProduct.AlgebraTensorModule.map Complex.ofRealLI.toLinearMap LinearMap.id

private def pol1RealRe {V : Type*} [AddCommGroup V] [Module ℚ V] :
    ℂ ⊗[ℚ] V →ₗ[ℝ] ℝ ⊗[ℚ] V :=
  TensorProduct.AlgebraTensorModule.map Complex.reLm LinearMap.id

private theorem pol1RealIn_re {V : Type*} [AddCommGroup V] [Module ℚ V]
    (x : ℂ ⊗[ℚ] V) :
    pol1RealIn (pol1RealRe x) = (2 : ℝ)⁻¹ • (x + complexConj V x) := by
  induction x using TensorProduct.inductionOn with
  | tmul z v =>
    change (z.re : ℂ) ⊗ₜ[ℚ] v = (2 : ℝ)⁻¹ • (z ⊗ₜ[ℚ] v + (starRingEnd ℂ z) ⊗ₜ[ℚ] v)
    rw [← TensorProduct.add_tmul, TensorProduct.smul_tmul']
    congr 1
    apply Complex.ext <;> simp <;> ring
  | add x y hx hy => simp only [map_add, hx, hy]; module

/-- The real vector whose `(0,1)` component is the given Hodge vector. -/
private def pol1HodgeRealMap {V : Type*} [AddCommGroup V] [Module ℚ V]
    [Module.Finite ℚ V] (M : QHodgeStructure 1 V) :
    M.H (0, 1) →ₗ[ℝ] ℝ ⊗[ℚ] V :=
  (2 : ℝ) • (pol1RealRe.comp ((M.H (0, 1)).subtype.restrictScalars ℝ))

private theorem pol1HodgeRealMap_in {V : Type*} [AddCommGroup V] [Module ℚ V]
    [Module.Finite ℚ V] (M : QHodgeStructure 1 V) (x : M.H (0, 1)) :
    pol1RealIn (pol1HodgeRealMap M x) = (x : ℂ ⊗[ℚ] V) + complexConj V x := by
  simp only [pol1HodgeRealMap, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.restrictScalars_apply, Submodule.subtype_apply, map_smul, pol1RealIn_re,
    smul_smul]
  norm_num

private theorem pol1HodgeRealMap_injective {V : Type*} [AddCommGroup V] [Module ℚ V]
    [Module.Finite ℚ V] (M : QHodgeStructure 1 V) :
    Function.Injective (pol1HodgeRealMap M) := by
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro x hx
  change pol1HodgeRealMap M x = 0 at hx
  change x = 0
  have h := congrArg pol1RealIn hx
  rw [pol1HodgeRealMap_in, map_zero] at h
  have hx10 : (x : ℂ ⊗[ℚ] V) ∈ M.H (1, 0) := by
    rw [eq_neg_of_add_eq_zero_left h]
    exact (M.H (1, 0)).neg_mem (complexConj_mem_H M 0 1 x x.2)
  have hd : Disjoint (M.H (1, 0)) (M.H (0, 1)) :=
    M.isInternal.submodule_iSupIndep.pairwiseDisjoint (by norm_num)
  apply Subtype.ext
  exact hd.le_bot ⟨hx10, x.2⟩

private def pol1HodgeRealEquiv {V : Type*} [AddCommGroup V] [Module ℚ V]
    [Module.Finite ℚ V] (M : QHodgeStructure 1 V)
    (hdim : finrank ℝ (M.H (0, 1)) = finrank ℝ (ℝ ⊗[ℚ] V)) :
    M.H (0, 1) ≃ₗ[ℝ] ℝ ⊗[ℚ] V := by
  letI : FiniteDimensional ℂ (M.H (0, 1)) := inferInstance
  letI : FiniteDimensional ℝ (M.H (0, 1)) := FiniteDimensional.complexToReal _
  exact (pol1HodgeRealMap M).linearEquivOfInjective (pol1HodgeRealMap_injective M) hdim

private theorem pol1RealRe_baseChange {V : Type*} [AddCommGroup V] [Module ℚ V]
    (T : Module.End ℚ V) (x : ℂ ⊗[ℚ] V) :
    pol1RealRe (T.baseChange ℂ x) = T.baseChange ℝ (pol1RealRe x) := by
  induction x using TensorProduct.inductionOn with
  | tmul z v => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem pol1HodgeRealMap_baseChange {V : Type*} [AddCommGroup V] [Module ℚ V]
    [Module.Finite ℚ V] (M : QHodgeStructure 1 V) (T : Module.End ℚ V)
    (hT : ∀ x ∈ M.H (0, 1), T.baseChange ℂ x ∈ M.H (0, 1))
    (x : M.H (0, 1)) :
    pol1HodgeRealMap M ⟨T.baseChange ℂ x, hT x x.2⟩ =
      T.baseChange ℝ (pol1HodgeRealMap M x) := by
  simp only [pol1HodgeRealMap, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.restrictScalars_apply, Submodule.subtype_apply, map_smul,
    pol1RealRe_baseChange]

private theorem pol1Cancel_real {V : Type*} [AddCommGroup V] [Module ℚ V]
    (x : ℝ ⊗[ℚ] V) :
    TensorProduct.AlgebraTensorModule.cancelBaseChange ℚ ℝ ℂ ℂ V (1 ⊗ₜ[ℝ] x) =
      pol1RealIn x := by
  induction x using TensorProduct.inductionOn with
  | tmul r v => simp [pol1RealIn, Complex.real_smul]
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]

private theorem pol1Complexify_in {V : Type*} [AddCommGroup V] [Module ℚ V]
    (I : Module.End ℝ (ℝ ⊗[ℚ] V)) (x : ℝ ⊗[ℚ] V) :
    complexifyRealEnd I (pol1RealIn x) = pol1RealIn (I x) := by
  rw [← pol1Cancel_real x]
  simp only [complexifyRealEnd, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, LinearMap.baseChange_tmul]
  exact pol1Cancel_real _

/-- Transport a real kernel to the complex eigenspace in the `(0,1)` piece. -/
private theorem pol1Kernel_finrank {V : Type*} [AddCommGroup V] [Module ℚ V]
    [Module.Finite ℚ V] (M : QHodgeStructure 1 V)
    (hdim : finrank ℝ (M.H (0, 1)) = finrank ℝ (ℝ ⊗[ℚ] V))
    (T : Module.End ℚ V)
    (hT : ∀ x ∈ M.H (0, 1), T.baseChange ℂ x ∈ M.H (0, 1))
    (I : Module.End ℝ (ℝ ⊗[ℚ] V))
    (hI : ∀ x : M.H (0, 1), I (pol1HodgeRealEquiv M hdim x) =
      pol1HodgeRealEquiv M hdim (Complex.I • x)) (s : ℝ) (z : ℂ) (hz : z = (s : ℂ) * Complex.I) :
    finrank ℝ (LinearMap.ker (T.baseChange ℝ - s • I)) =
      2 * finrank ℂ ↥(Module.End.eigenspace (T.baseChange ℂ)
        z ⊓ M.H (0, 1)) := by
  let e := pol1HodgeRealEquiv M hdim
  have hTe (x : M.H (0, 1)) :
      T.baseChange ℝ (e x) = e ⟨T.baseChange ℂ x, hT x x.2⟩ :=
    (pol1HodgeRealMap_baseChange M T hT x).symm
  have hmem (x : M.H (0, 1)) :
      e x ∈ LinearMap.ker (T.baseChange ℝ - s • I) ↔
      (x : ℂ ⊗[ℚ] V) ∈ Module.End.eigenspace (T.baseChange ℂ)
        z := by
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, sub_eq_zero,
      hTe, hI, ← map_smul e, e.injective.eq_iff, Module.End.mem_eigenspace_iff]
    rw [Subtype.ext_iff]
    change T.baseChange ℂ x = s • (Complex.I • (x : ℂ ⊗[ℚ] V)) ↔ _
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul, hz]
    rfl
  let P := Module.End.eigenspace (T.baseChange ℂ) z ⊓ M.H (0, 1)
  let f : P →ₗ[ℝ] LinearMap.ker (T.baseChange ℝ - s • I) :=
    { toFun := fun x => ⟨e ⟨x, x.2.2⟩, (hmem ⟨x, x.2.2⟩).mpr x.2.1⟩
      map_add' := by
        intro x y
        exact Subtype.ext (e.map_add ⟨x, x.2.2⟩ ⟨y, y.2.2⟩)
      map_smul' := by
        intro r x
        exact Subtype.ext (e.map_smul r ⟨x, x.2.2⟩) }
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      have hxy : e ⟨x, x.2.2⟩ = e ⟨y, y.2.2⟩ :=
        congrArg (fun z : LinearMap.ker (T.baseChange ℝ - s • I) => (z : ℝ ⊗[ℚ] V)) h
      apply Subtype.ext
      exact congrArg (fun z : M.H (0, 1) => (z : ℂ ⊗[ℚ] V)) (e.injective hxy)
    · intro y
      obtain ⟨x, hx⟩ := e.surjective y
      refine ⟨⟨x, (hmem x).mp ?_, x.2⟩, ?_⟩
      · rw [hx]; exact y.2
      · exact Subtype.ext hx
  have hr := (LinearEquiv.ofBijective f hf).finrank_eq
  rw [← hr]
  exact finrank_real_of_complex P

private theorem pol1Complexify_eq_negGrading {V : Type*} [AddCommGroup V] [Module ℚ V]
    [Module.Finite ℚ V] (M : QHodgeStructure 1 V)
    (hdim : finrank ℝ (M.H (0, 1)) = finrank ℝ (ℝ ⊗[ℚ] V))
    (I : Module.End ℝ (ℝ ⊗[ℚ] V))
    (hI : ∀ x : M.H (0, 1), I (pol1HodgeRealEquiv M hdim x) =
      pol1HodgeRealEquiv M hdim (Complex.I • x)) :
    complexifyRealEnd I = -gradingOperator M.H M.isInternal := by
  have he (x : M.H (0, 1)) :
      pol1RealIn (pol1HodgeRealEquiv M hdim x) =
        (x : ℂ ⊗[ℚ] V) + complexConj V x := pol1HodgeRealMap_in M x
  have h (x : ℝ ⊗[ℚ] V) :
      complexifyRealEnd I (pol1RealIn x) =
        (-gradingOperator M.H M.isInternal) (pol1RealIn x) := by
    obtain ⟨y, rfl⟩ := (pol1HodgeRealEquiv M hdim).surjective x
    rw [pol1Complexify_in, hI, he, he]
    rw [LinearMap.neg_apply, map_add,
      gradingOperator_apply_of_mem M.H M.isInternal y.2,
      gradingOperator_apply_of_mem M.H M.isInternal (complexConj_mem_H M 0 1 y y.2)]
    simp [complexConj_smul, add_comm]
  ext v
  exact h (1 ⊗ₜ[ℚ] v)

theorem spec_exists_weightOneComplexStructure_dictionary_aux
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (hF : FiniteBetti X) (hB : BettiDeRhamIso X) :
    let hT := torusCohomology_cupProductOf X
    letI := hT.finite
    let hD := spec_hodgeDecomposition_of_cupLeft_alone X hT
      (spec_cupLeft_cupProductOf X)
    ∃ I : ℝ ⊗[ℚ] HQ X 1 →ₗ[ℝ] ℝ ⊗[ℚ] HQ X 1,
      (∀ x, I (I x) = -x) ∧
      complexifyRealEnd I =
        -gradingOperator (abelianVarietyCohomologyOf hF hB hD hT).weight1.H
          (abelianVarietyCohomologyOf hF hB hD hT).weight1.isInternal ∧
      ∀ {d : ℚ} (_hd : 0 < d) (A : letI := hT.finite
        WeilAction (abelianVarietyCohomologyOf hF hB hD hT).weight1 d),
        SignatureDictionary hF hB hD hT A I := by
  let hT := torusCohomology_cupProductOf X
  letI := hT.finite
  let hD := spec_hodgeDecomposition_of_cupLeft_alone X hT (spec_cupLeft_cupProductOf X)
  let M := (abelianVarietyCohomologyOf hF hB hD hT).weight1
  have hdim : finrank ℝ (M.H (0, 1)) = finrank ℝ (ℝ ⊗[ℚ] HQ X 1) := by
    calc
      finrank ℝ (M.H (0, 1)) = 2 * finrank ℂ (M.H (0, 1)) :=
        finrank_real_of_complex (M.H (0, 1))
      _ = 2 * dim X.left := congrArg (2 * ·)
        (spec_finrank_cohomologyHodgePiece_one X hD).2
      _ = finrank ℚ (HQ X 1) := hT.finrank_eq.symm
      _ = finrank ℝ (ℝ ⊗[ℚ] HQ X 1) := Module.finrank_baseChange.symm
  let e := pol1HodgeRealEquiv M hdim
  let I : Module.End ℝ (ℝ ⊗[ℚ] HQ X 1) :=
    e.toLinearMap ∘ₗ
      (Complex.I • (LinearMap.id : Module.End ℂ (M.H (0, 1)))).restrictScalars ℝ ∘ₗ
      e.symm.toLinearMap
  have hIe (x : M.H (0, 1)) : I (e x) = e (Complex.I • x) := by
    simp only [I, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      LinearMap.restrictScalars_apply, LinearMap.smul_apply, LinearMap.id_apply]
  refine ⟨I, ?_, pol1Complexify_eq_negGrading M hdim I hIe, ?_⟩
  · intro x
    obtain ⟨y, rfl⟩ := e.surjective x
    rw [hIe, hIe, smul_smul, Complex.I_mul_I, neg_one_smul, map_neg]
  · intro d hd A
    have hA : ∀ x ∈ M.H (0, 1), A.J.baseChange ℂ x ∈ M.H (0, 1) :=
      fun x hx => A.preserves (0, 1) (Submodule.mem_map_of_mem hx)
    constructor
    · exact pol1Kernel_finrank M hdim A.J hA I hIe (Real.sqrt (d : ℝ))
        (WeilAction.omegaC d) (mul_comm _ _)
    · have hk : A.J.baseChange ℝ + Real.sqrt (d : ℝ) • I =
          A.J.baseChange ℝ - (-Real.sqrt (d : ℝ)) • I := by
        rw [neg_smul, sub_neg_eq_add]
      exact (congrArg (fun K : Module.End ℝ (ℝ ⊗[ℚ] HQ X 1) =>
          finrank ℝ (LinearMap.ker K)) hk).trans
        (pol1Kernel_finrank M hdim A.J hA I hIe (-Real.sqrt (d : ℝ))
          (-WeilAction.omegaC d) (by
            simp only [WeilAction.omegaC, Complex.ofReal_neg, neg_mul]
            rw [mul_comm]))

/-- Degree-one Betti cohomology of an abelian variety is finite-dimensional.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, Lemma 1.3.1, through
`torusCohomology_cupProductOf`. -/
noncomputable instance polarizedFiniteHQOne
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] : Module.Finite ℚ (HQ X 1) :=
  (torusCohomology_cupProductOf X).finite

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] : Module.Finite ℚ (HQ X 1) := inferInstance

private theorem realEnd_commutes_of_complexify_commutes
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (I : Module.End ℝ (ℝ ⊗[ℚ] V)) (T : Module.End ℚ V)
    (h : complexifyRealEnd I * T.baseChange ℂ =
      T.baseChange ℂ * complexifyRealEnd I) :
    I * T.baseChange ℝ = T.baseChange ℝ * I := by
  apply LinearMap.baseChangeHom_injective (R := ℝ) (S := ℂ)
    (M := ℝ ⊗[ℚ] V) (N := ℝ ⊗[ℚ] V)
  change (I * T.baseChange ℝ).baseChange ℂ =
    (T.baseChange ℝ * I).baseChange ℂ
  rw [LinearMap.baseChange_mul, LinearMap.baseChange_mul,
    LinearMap.baseChange_baseChange]
  let e := TensorProduct.AlgebraTensorModule.cancelBaseChange ℚ ℝ ℂ ℂ V
  change I.baseChange ℂ * (e.symm.toLinearMap ∘ₗ T.baseChange ℂ ∘ₗ e.toLinearMap) =
    (e.symm.toLinearMap ∘ₗ T.baseChange ℂ ∘ₗ e.toLinearMap) * I.baseChange ℂ
  apply LinearMap.ext
  intro x
  have hx := LinearMap.congr_fun h (e x)
  simpa only [e, Module.End.mul_apply, complexifyRealEnd, LinearMap.coe_comp,
    LinearEquiv.coe_coe, Function.comp_apply, LinearEquiv.symm_apply_apply,
    LinearEquiv.apply_symm_apply] using congrArg e.symm hx

private theorem negGradingOperator_commutes
    {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    (M : QHodgeStructure 1 V) (T : M.Hom M) :
    (-gradingOperator M.H M.isInternal).comp (T.toLinearMap.baseChange ℂ) =
      (T.toLinearMap.baseChange ℂ).comp (-gradingOperator M.H M.isInternal) := by
  apply linearMap_ext_of_isInternal M.isInternal
  intro pq z hz
  obtain ⟨p, q⟩ := pq
  have hTz : T.toLinearMap.baseChange ℂ z ∈ M.H (p, q) :=
    T.maps_pieces (p, q) (Submodule.mem_map_of_mem hz)
  simp only [LinearMap.comp_apply, LinearMap.neg_apply,
    gradingOperator_apply_of_mem M.H M.isInternal hz,
    gradingOperator_apply_of_mem M.H M.isInternal hTz]
  rw [map_neg, map_smul]

/-- An operator with eigenvalues `-i` and `i` preserves a bilinear form exactly
when its two complementary eigenspaces are isotropic. -/
theorem pol1_invariant_iff_isotropic
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (E : LinearMap.BilinForm ℂ W) (J : Module.End ℂ W)
    (U V : Submodule ℂ W) (hUV : U ⊔ V = ⊤)
    (hU : ∀ x ∈ U, J x = -Complex.I • x)
    (hV : ∀ x ∈ V, J x = Complex.I • x) :
    (∀ x y, E (J x) (J y) = E x y) ↔
      (∀ x ∈ U, ∀ y ∈ U, E x y = 0) ∧
      (∀ x ∈ V, ∀ y ∈ V, E x y = 0) := by
  constructor
  · intro h
    constructor
    · intro x hx y hy
      have he := h x y
      rw [hU x hx, hU y hy] at he
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at he
      have hi : (-Complex.I) * (-Complex.I) = (-1 : ℂ) := by simp
      rw [← mul_assoc, hi, neg_one_mul] at he
      linear_combination -he / 2
    · intro x hx y hy
      have he := h x y
      rw [hV x hx, hV y hy] at he
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at he
      rw [← mul_assoc, Complex.I_mul_I, neg_one_mul] at he
      linear_combination -he / 2
  · rintro ⟨hUU, hVV⟩ x y
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp
      (show x ∈ U ⊔ V by rw [hUV]; trivial)
    obtain ⟨u', hu', v', hv', rfl⟩ := Submodule.mem_sup.mp
      (show y ∈ U ⊔ V by rw [hUV]; trivial)
    simp only [map_add, hU u hu, hU u' hu', hV v hv, hV v' hv',
      map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hUU u hu u' hu', hVV v hv v' hv']
    simp [← mul_assoc]

/-- Extending a rational bilinear form through the reals agrees with direct
complex scalar extension under the canonical tensor comparison. -/
theorem pol1_bilin_cancelBaseChange
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (E : LinearMap.BilinForm ℚ V) :
    (E.baseChange ℂ).compl₁₂
      (TensorProduct.AlgebraTensorModule.cancelBaseChange ℚ ℝ ℂ ℂ V).toLinearMap
      (TensorProduct.AlgebraTensorModule.cancelBaseChange ℚ ℝ ℂ ℂ V).toLinearMap =
      (E.baseChange ℝ).baseChange ℂ := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  change E.baseChange ℂ
    (TensorProduct.AlgebraTensorModule.cancelBaseChange ℚ ℝ ℂ ℂ V x)
    (TensorProduct.AlgebraTensorModule.cancelBaseChange ℚ ℝ ℂ ℂ V y) =
      (E.baseChange ℝ).baseChange ℂ x y
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    induction y using TensorProduct.inductionOn with
    | tmul b y =>
      induction x using TensorProduct.inductionOn with
      | tmul r x =>
        induction y using TensorProduct.inductionOn with
        | tmul s y =>
          simp only [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
            LinearMap.BilinForm.baseChange_tmul, Algebra.smul_def]
          change (E x y : ℂ) * ((r * a) * (s * b)) =
            (((E x y : ℝ) * (r * s) : ℝ) : ℂ) * (a * b)
          push_cast
          ring
        | add y z hy hz => simp only [TensorProduct.tmul_add, map_add,
            LinearMap.add_apply, hy, hz]
      | add x z hx hz => simp only [TensorProduct.tmul_add, map_add,
          LinearMap.add_apply, hx, hz]
    | add y z hy hz => simp only [map_add, LinearMap.add_apply, hy, hz]
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]

/-- Preservation of a real bilinear form can be tested after complexification. -/
theorem pol1_real_bilin_invariant_iff
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    (E : LinearMap.BilinForm ℝ W) (J : Module.End ℝ W) :
    (∀ x y, E (J x) (J y) = E x y) ↔
      (∀ x y, E.baseChange ℂ (J.baseChange ℂ x) (J.baseChange ℂ y) =
        E.baseChange ℂ x y) := by
  constructor
  · intro h x y
    induction x using TensorProduct.inductionOn with
    | tmul a x =>
      induction y using TensorProduct.inductionOn with
      | tmul b y =>
        simp only [LinearMap.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul, h]
      | add y z hy hz => simp only [map_add, hy, hz]
    | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]
  · intro h x y
    have he := h (1 ⊗ₜ[ℝ] x) (1 ⊗ₜ[ℝ] y)
    simp only [LinearMap.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul,
      Algebra.smul_def, mul_one] at he
    change (E (J x) (J y) : ℂ) = (E x y : ℂ) at he
    exact Complex.ofReal_injective he

/-- The first bilinear relation is unchanged by the canonical comparison of
iterated and direct complexifications. -/
theorem pol1_complexify_invariant_iff
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (E : LinearMap.BilinForm ℚ V) (I : Module.End ℝ (ℝ ⊗[ℚ] V)) :
    (∀ x y, E.baseChange ℝ (I x) (I y) = E.baseChange ℝ x y) ↔
      (∀ x y, E.baseChange ℂ (complexifyRealEnd I x) (complexifyRealEnd I y) =
        E.baseChange ℂ x y) := by
  rw [pol1_real_bilin_invariant_iff]
  let e := TensorProduct.AlgebraTensorModule.cancelBaseChange ℚ ℝ ℂ ℂ V
  have he (x y : ℂ ⊗[ℝ] (ℝ ⊗[ℚ] V)) :
      E.baseChange ℂ (e x) (e y) = (E.baseChange ℝ).baseChange ℂ x y :=
    LinearMap.congr_fun₂ (pol1_bilin_cancelBaseChange E) x y
  have hI (x : ℂ ⊗[ℝ] (ℝ ⊗[ℚ] V)) :
      complexifyRealEnd I (e x) = e (I.baseChange ℂ x) := by
    simp only [complexifyRealEnd, LinearMap.comp_apply, LinearEquiv.coe_coe,
      e, LinearEquiv.symm_apply_apply]
  constructor
  · intro h x y
    obtain ⟨x, rfl⟩ := e.surjective x
    obtain ⟨y, rfl⟩ := e.surjective y
    rw [hI, hI, he, he]
    exact h x y
  · intro h x y
    have hh := h (e x) (e y)
    rwa [hI, hI, he, he] at hh

/-- For weight one, the real first bilinear relation is equivalent to isotropy
of the two Hodge summands. -/
theorem pol1_real_invariant_iff_hodge_isotropic
    {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    (M : QHodgeStructure 1 V) (E : LinearMap.BilinForm ℚ V)
    (hsup : M.H (1, 0) ⊔ M.H (0, 1) = ⊤)
    (I : Module.End ℝ (ℝ ⊗[ℚ] V))
    (hIC : complexifyRealEnd I = -gradingOperator M.H M.isInternal) :
    (∀ x y, E.baseChange ℝ (I x) (I y) = E.baseChange ℝ x y) ↔
      (∀ x ∈ M.H (1, 0), ∀ y ∈ M.H (1, 0), E.baseChange ℂ x y = 0) ∧
      (∀ x ∈ M.H (0, 1), ∀ y ∈ M.H (0, 1), E.baseChange ℂ x y = 0) := by
  rw [pol1_complexify_invariant_iff]
  apply pol1_invariant_iff_isotropic _ _ _ _ hsup
  · intro x hx
    rw [hIC, LinearMap.neg_apply, gradingOperator_apply_of_mem M.H M.isInternal hx]
    simp
  · intro x hx
    rw [hIC, LinearMap.neg_apply, gradingOperator_apply_of_mem M.H M.isInternal hx]
    simp

/-- Contraction intertwines the exterior derivation with the action on a map
from the dual space. -/
theorem pol1_contract_exteriorDer
    {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
    (f : Module.End K V) (ω : ⋀[K]^2 V) :
    contract (InvariantsExterior.exteriorDer 2 f ω) =
      f ∘ₗ contract ω + contract ω ∘ₗ f.dualMap := by
  have h : contract ∘ₗ InvariantsExterior.exteriorDer 2 f =
      (LinearMap.llcomp K (Dual K V) V V f +
        (LinearMap.llcomp K (Dual K V) (Dual K V) V).flip f.dualMap) ∘ₗ contract := by
    ext v φ
    simp [InvariantsExterior.exteriorDer_ιMulti, Fin.sum_univ_two,
      LinearMap.dualMap_apply]
    module
  exact LinearMap.congr_fun h ω

/-- A nondegenerate bivector is killed by an exterior derivation exactly when
the corresponding endomorphism is skew for its dual form. -/
theorem pol1_exteriorDer_eq_zero_iff_dualForm_skew
    {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
    [Module.Finite K V] {ω : ⋀[K]^2 V} (hω : Symplectic.IsNondegenerate ω)
    (f : Module.End K V) :
    InvariantsExterior.exteriorDer 2 f ω = 0 ↔
      ∀ x y, dualForm hω (f x) y = -dualForm hω x (f y) := by
  rw [← isRosatiSkew_iff_dualForm hω f, ← contract_injective.eq_iff,
    map_zero, pol1_contract_exteriorDer, IsRosatiSkew]
  exact add_eq_zero_iff_eq_neg'.trans (by rfl)

/-- Rational bilinear forms commute with rational conjugation after scalar
extension to the complex numbers. -/
theorem pol1_bilin_conj
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (E : LinearMap.BilinForm ℚ V) (x y : ℂ ⊗[ℚ] V) :
    E.baseChange ℂ (sigmaQ V x) (sigmaQ V y) =
      starRingEnd ℂ (E.baseChange ℂ x y) := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    induction y using TensorProduct.inductionOn with
    | tmul b y =>
      change E.baseChange ℂ (starRingEnd ℂ a ⊗ₜ[ℚ] x)
        (starRingEnd ℂ b ⊗ₜ[ℚ] y) = _
      simp only [LinearMap.BilinForm.baseChange_tmul, Algebra.smul_def,
        map_mul]
      congr 1
      exact (map_ratCast (starRingEnd ℂ) (E x y)).symm
    | add y z hy hz => simp only [map_add, hy, hz]
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]

/-- For a rational alternating form, the weight-one Hermitian expression is real. -/
theorem pol1_hermitian_real
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (E : LinearMap.BilinForm ℚ V) (hE : E.IsAlt) (x : ℂ ⊗[ℚ] V) :
    (Complex.I * E.baseChange ℂ x (sigmaQ V x)).im = 0 := by
  have hc := pol1_bilin_conj E x (sigmaQ V x)
  rw [sigmaQ_involutive] at hc
  rw [WeilPower.alternating_baseChange_skew E hE] at hc
  have hr := congrArg Complex.re hc
  simp only [Complex.neg_re, Complex.conj_re] at hr
  have hz : (E.baseChange ℂ x (sigmaQ V x)).re = 0 := by linarith
  simpa only [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul,
    one_mul, zero_add] using hz

/-- Once the first relation holds, a weight-one polarization is determined by
strict positivity on `H^{1,0}`; conjugation supplies the other Hodge summand. -/
theorem pol1_polarisation_iff_h10_positive
    {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    (M : QHodgeStructure 1 V) (E : LinearMap.BilinForm ℚ V)
    (hE : E.IsAlt) (hne : E.Nondegenerate)
    (hsupp : ∀ pq : ℤ × ℤ, pq ≠ (1, 0) → pq ≠ (0, 1) → M.H pq = ⊥)
    (h10 : ∀ x ∈ M.H (1, 0), ∀ y ∈ M.H (1, 0), E.baseChange ℂ x y = 0)
    (h01 : ∀ x ∈ M.H (0, 1), ∀ y ∈ M.H (0, 1), E.baseChange ℂ x y = 0) :
    (∃ P : Polarisation M, P.form = E) ↔
      ∀ x ∈ M.H (1, 0), x ≠ 0 →
        0 < (Complex.I * E.baseChange ℂ x (sigmaQ V x)).re := by
  constructor
  · rintro ⟨P, rfl⟩ x hx hx0
    simpa only [Iexp, sub_zero, zpow_one] using P.positive 1 0 (by norm_num) x hx hx0
  · intro hpos
    have hcases (p q : ℤ) (x : ℂ ⊗[ℚ] V) (hx : x ∈ M.H (p, q)) :
        (p, q) = (1, 0) ∨ (p, q) = (0, 1) ∨ x = 0 := by
      by_cases h : (p, q) = (1, 0)
      · exact Or.inl h
      by_cases h' : (p, q) = (0, 1)
      · exact Or.inr (Or.inl h')
      exact Or.inr (Or.inr (by simpa only [hsupp _ h h', Submodule.mem_bot] using hx))
    refine ⟨{
      form := E
      nondegenerate := hne
      symm := ?_
      orthogonal := ?_
      hermitian_real := ?_
      positive := ?_
    }, rfl⟩
    · intro x y
      simpa using (hE.neg_eq y x).symm
    · intro p q p' q' hneq x hx y hy
      rcases hcases p q x hx with h | h | rfl
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        rcases hcases p' q' y hy with h' | h' | rfl
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h'
          exact h10 x hx y hy
        · exact (hneq h').elim
        · simp
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        rcases hcases p' q' y hy with h' | h' | rfl
        · exact (hneq h').elim
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h'
          exact h01 x hx y hy
        · simp
      · simp
    · intro p q _ x hx
      rcases hcases p q x hx with h | h | rfl
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        simpa [Iexp] using pol1_hermitian_real E hE x
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        have hr := pol1_hermitian_real E hE x
        simpa [Iexp] using congrArg Neg.neg hr
      · simp
    · intro p q _ x hx hx0
      rcases hcases p q x hx with h | h | h
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        simpa [Iexp] using hpos x hx hx0
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        have hc : sigmaQ V x ∈ M.H (1, 0) := by
          rw [← M.conj_symm 0 1]
          exact ⟨x, hx, rfl⟩
        have hc0 : sigmaQ V x ≠ 0 := by
          intro hz
          apply hx0
          simpa using congrArg (sigmaQ V) hz
        have hp := hpos _ hc hc0
        rw [sigmaQ_involutive, WeilPower.alternating_baseChange_skew E hE] at hp
        simpa [Iexp] using hp
      · exact (hx0 h).elim

/-- The geometric degree-two Hodge condition is the `(1,1)` condition on the
polarization bivector in the exterior Hodge structure. -/
theorem pol1_hodge_iff_polarizationVec_type
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (hF : FiniteBetti X) (hB : BettiDeRhamIso X)
    (η : HQ X 2) :
    let hT := torusCohomology_cupProductOf X
    letI := hT.finite
    let hD := spec_hodgeDecomposition_of_cupLeft_alone X hT
      (spec_cupLeft_cupProductOf X)
    ((η : H^(2 * 1)(X; ℚ)) ∈ Hdg^1(X; ℚ)) ↔
      (1 : ℂ) ⊗ₜ[ℚ] polarizationVec hT η ∈
        ((abelianVarietyCohomologyOf hF hB hD hT).weight1.exteriorPower
          (V := HQ X 1) 2).H (1, 1) := by
  let hT := torusCohomology_cupProductOf X
  letI := hT.finite
  let hD := spec_hodgeDecomposition_of_cupLeft_alone X hT
    (spec_cupLeft_cupProductOf X)
  have h := isHodgeClass_exteriorPower_iff hF hB hD hT
    (spec_cupFiltered_of_cupLeft_alone X hT (spec_cupLeft_cupProductOf X))
    1 (polarizationVec hT η)
  change (1 : ℂ) ⊗ₜ[ℚ] polarizationVec hT η ∈
    ((abelianVarietyCohomologyOf hF hB hD hT).weight1.exteriorPower
      (V := HQ X 1) 2).H (1, 1) ↔
    (cupProductOf X).cupWedgeMap 2 (polarizationVec hT η) ∈ Hdg^1(X; ℚ) at h
  rw [cupWedgeMap_polarizationVec] at h
  exact h.symm

private theorem pol1_singleCopy_commutes
    {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    (G : Module.End ℂ (ℂ ⊗[ℚ] V)) :
    G.comp (f1575SingleCopyComplex (V := V)).toLinearMap =
      (f1575SingleCopyComplex (V := V)).toLinearMap.comp (WeilPower.powerAction 1 G) := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul a v =>
    induction v using TensorProduct.inductionOn with
    | tmul x u => simp [f1575SingleCopyComplex, WeilPower.powerAction, WeilPower.powerBaseChange]
    | add x y hx hy => simpa only [TensorProduct.tmul_add, map_add] using congrArg₂ (· + ·) hx hy
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

/-- Type `(1,1)` of a bivector is equivalent to vanishing of the derivation
induced by the weight-one grading operator. -/
theorem pol1_exterior_type_iff_grading_zero
    {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    (M : QHodgeStructure 1 V) (ω : ⋀[ℚ]^2 V) :
    (1 : ℂ) ⊗ₜ[ℚ] ω ∈ (M.exteriorPower (V := V) 2).H (1, 1) ↔
      InvariantsExterior.exteriorDer 2 (gradingOperator M.H M.isInternal)
        (WeilAction.exteriorPowerBaseChangeEquiv 2 ((1 : ℂ) ⊗ₜ[ℚ] ω)) = 0 := by
  let e := f1575SingleCopyExterior (V := V) 2
  let w := e.symm ((1 : ℂ) ⊗ₜ[ℚ] ω)
  let j := f1575SingleCopyComplex (V := V)
  have hmap : (⨆ q : ℤ, WeilPower.exteriorHodge M.H 1 2 (q, q)).map e.toLinearMap =
      M.exteriorPowerH (V := V) 2 (1, 1) := by
    dsimp only [e]
    rw [Submodule.map_iSup]
    simp_rw [f1575SingleCopyExterior_map_hodge]
    exact f1575_diagonal_eq M 1
  have hw : w ∈ ⨆ q : ℤ, WeilPower.exteriorHodge M.H 1 2 (q, q) ↔
      (1 : ℂ) ⊗ₜ[ℚ] ω ∈ M.exteriorPowerH (V := V) 2 (1, 1) := by
    rw [← hmap, Submodule.mem_map_equiv]
  rw [← WeilPower.ker_exterior_hodge_grading M.H M.isInternal, LinearMap.mem_ker] at hw
  have he : exteriorPower.map 2 j.toLinearMap w =
      WeilAction.exteriorPowerBaseChangeEquiv 2 ((1 : ℂ) ⊗ₜ[ℚ] ω) := by
    change (WeilPower.exteriorEquiv 2 j)
      ((WeilPower.exteriorEquiv 2 j).symm
        (WeilAction.exteriorPowerBaseChangeEquiv 2 ((1 : ℂ) ⊗ₜ[ℚ] ω))) = _
    exact LinearEquiv.apply_symm_apply _ _
  change (1 : ℂ) ⊗ₜ[ℚ] ω ∈ M.exteriorPowerH (V := V) 2 (1, 1) ↔ _
  rw [← he, InvariantsExterior.exteriorDer_map _ _ _ _ (pol1_singleCopy_commutes _)]
  change _ ↔ (WeilPower.exteriorEquiv 2 j)
    (InvariantsExterior.exteriorDer 2 (WeilPower.powerAction 1
      (gradingOperator M.H M.isInternal)) w) = 0
  rw [LinearEquiv.map_eq_zero_iff]
  exact hw.symm

theorem pol1_contract_complexify
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (ω : ⋀[ℚ]^2 V) (φ : Dual ℚ V) :
    contract (complexifyWedge 2 ω) (Module.Dual.baseChange ℂ φ) =
      (1 : ℂ) ⊗ₜ[ℚ] contract ω φ := by
  have h : ((LinearMap.applyₗ (Module.Dual.baseChange ℂ φ) :
      (Dual ℂ (ℂ ⊗[ℚ] V) →ₗ[ℂ] ℂ ⊗[ℚ] V) →ₗ[ℂ] ℂ ⊗[ℚ] V).restrictScalars ℚ).comp
      ((contract : ⋀[ℂ]^2 (ℂ ⊗[ℚ] V) →ₗ[ℂ] _).restrictScalars ℚ) ∘ₗ
        complexifyWedge 2 =
      (TensorProduct.mk ℚ ℂ V 1) ∘ₗ (LinearMap.applyₗ φ ∘ₗ contract) := by
    ext v
    simp [TensorProduct.tmul_sub, TensorProduct.tmul_smul, Rat.cast_smul_eq_qsmul]
  exact LinearMap.congr_fun h ω

theorem pol1_dual_baseChange_tmul
    {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    (a : ℂ) (φ : Dual ℚ V) :
    (TensorProduct.isBaseChange ℚ V ℂ).toDualBaseChange (a ⊗ₜ[ℚ] φ) =
      a • Module.Dual.baseChange ℂ φ := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul c x =>
    have ht := IsBaseChange.toDualBaseChange_tmul
      (TensorProduct.isBaseChange ℚ V ℂ) a φ x
    change ((TensorProduct.isBaseChange ℚ V ℂ).toDualBaseChange (a ⊗ₜ[ℚ] φ))
      ((1 : ℂ) ⊗ₜ[ℚ] x) = a * (algebraMap ℚ ℂ) (φ x) at ht
    rw [show c ⊗ₜ[ℚ] x = c • ((1 : ℂ) ⊗ₜ[ℚ] x) by simp [TensorProduct.smul_tmul'],
      map_smul, ht]
    simp [Algebra.smul_def]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem pol1_complexify_nondegenerate
    {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    {ω : ⋀[ℚ]^2 V} (hω : Symplectic.IsNondegenerate ω) :
    Symplectic.IsNondegenerate (complexifyWedge 2 ω) := by
  let d := (TensorProduct.isBaseChange ℚ V ℂ).toDualBaseChange
  have hc : (contract (complexifyWedge 2 ω)).comp d.toLinearMap =
      (contract ω).baseChange ℂ := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a φ =>
      change contract (complexifyWedge 2 ω)
        ((TensorProduct.isBaseChange ℚ V ℂ).toDualBaseChange (a ⊗ₜ[ℚ] φ)) = _
      rw [pol1_dual_baseChange_tmul, map_smul, pol1_contract_complexify,
        LinearMap.baseChange_tmul]
      simp [TensorProduct.smul_tmul']
    | add x y hx hy => simp only [map_add, hx, hy]
  have hb : Function.Bijective (fun z => contract (complexifyWedge 2 ω) (d z)) := by
    change Function.Bijective ((contract (complexifyWedge 2 ω)).comp d.toLinearMap)
    rw [hc]
    exact ((contractEquiv hω).baseChange ℚ ℂ _ _).bijective
  constructor
  · intro x y hxy
    obtain ⟨x, rfl⟩ := d.surjective x
    obtain ⟨y, rfl⟩ := d.surjective y
    exact congrArg d (hb.1 hxy)
  · intro y
    obtain ⟨z, hz⟩ := hb.2 y
    exact ⟨d z, hz⟩

theorem pol1_dualForm_complexify
    {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    {ω : ⋀[ℚ]^2 V} (hω : Symplectic.IsNondegenerate ω) :
    (dualForm hω).baseChange ℂ = dualForm (pol1_complexify_nondegenerate hω) := by
  apply LinearMap.ext_basis ((Module.finBasis ℚ V).baseChange ℂ)
    ((Module.finBasis ℚ V).baseChange ℂ)
  intro i j
  simp only [Module.Basis.baseChange_apply]
  obtain ⟨φ, hφ⟩ := hω.2 (Module.finBasis ℚ V j)
  rw [← hφ, LinearMap.BilinForm.baseChange_tmul, dualForm_apply,
    contractEquiv_symm_contract]
  rw [← pol1_contract_complexify, dualForm_apply, contractEquiv_symm_contract,
    Module.Dual.baseChange_apply_tmul]
  simp

/-- For an operator squaring to minus the identity, invariance and
infinitesimal skewness of a bilinear form are equivalent. -/
theorem pol1_invariant_iff_skew
    {K W : Type*} [Field K] [AddCommGroup W] [Module K W]
    (E : LinearMap.BilinForm K W) (J : Module.End K W)
    (hJ : ∀ x, J (J x) = -x) :
    (∀ x y, E (J x) (J y) = E x y) ↔
      (∀ x y, E (J x) y = -E x (J y)) := by
  constructor
  · intro h x y
    have hh := h x (J y)
    rw [hJ, map_neg] at hh
    exact neg_eq_iff_eq_neg.mp hh
  · intro h x y
    rw [h, hJ, map_neg, neg_neg]

theorem spec_firstRiemannRelation_aux
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (hF : FiniteBetti X) (hB : BettiDeRhamIso X)
    {η : HQ X 2} (hω : Symplectic.IsNondegenerate
      (polarizationVec (torusCohomology_cupProductOf X) η))
    (I : ℝ ⊗[ℚ] HQ X 1 →ₗ[ℝ] ℝ ⊗[ℚ] HQ X 1)
    (hIC : let hT := torusCohomology_cupProductOf X
      letI := hT.finite
      let hD := spec_hodgeDecomposition_of_cupLeft_alone X hT (spec_cupLeft_cupProductOf X)
      complexifyRealEnd I = -gradingOperator
        (abelianVarietyCohomologyOf hF hB hD hT).weight1.H
        (abelianVarietyCohomologyOf hF hB hD hT).weight1.isInternal) :
    let hT := torusCohomology_cupProductOf X
    letI := hT.finite
    let hD := spec_hodgeDecomposition_of_cupLeft_alone X hT (spec_cupLeft_cupProductOf X)
    let S := abelianVarietyCohomologyOf hF hB hD hT
    ((η : H^(2 * 1)(X; ℚ)) ∈ Hdg^1(X; ℚ)) ↔
      (((∀ x ∈ S.weight1.H (1, 0), ∀ y ∈ S.weight1.H (1, 0),
          (polarizationForm hT hω).baseChange ℂ x y = 0) ∧
        (∀ x ∈ S.weight1.H (0, 1), ∀ y ∈ S.weight1.H (0, 1),
          (polarizationForm hT hω).baseChange ℂ x y = 0)) ∧
       (∀ x y, (polarizationForm hT hω).baseChange ℝ (I x) (I y) =
          (polarizationForm hT hω).baseChange ℝ x y)) := by
  let hT := torusCohomology_cupProductOf X
  letI := hT.finite
  let hD := spec_hodgeDecomposition_of_cupLeft_alone X hT
    (spec_cupLeft_cupProductOf X)
  let M := (abelianVarietyCohomologyOf hF hB hD hT).weight1
  let E := polarizationForm hT hω
  let C := gradingOperator M.H M.isInternal
  have hC2 (x : ℂ ⊗[ℚ] HQ X 1) : C (C x) = -x := by
    have hsupp : ∀ pq : ℤ × ℤ, pq ≠ (1, 0) → pq ≠ (0, 1) → M.H pq = ⊥ := by
      intro pq h10 h01
      exact cohomologyHodgePiece_one_eq_bot X pq h10 h01
    have hh := spec_eqw_gradingOperator_mul_self (H := M.H) (hH := M.isInternal) hsupp
    exact LinearMap.congr_fun hh x
  have hclass : ((η : H^(2 * 1)(X; ℚ)) ∈ Hdg^1(X; ℚ)) ↔
      ∀ x y, E.baseChange ℂ (C x) y = -E.baseChange ℂ x (C y) := by
    refine (pol1_hodge_iff_polarizationVec_type X hF hB η).trans ?_
    rw [pol1_exterior_type_iff_grading_zero,
      WeilAction.exteriorPowerBaseChangeEquiv_tmul,
      pol1_exteriorDer_eq_zero_iff_dualForm_skew (pol1_complexify_nondegenerate hω),
      ← pol1_dualForm_complexify hω]
    rfl
  have hinv : ((η : H^(2 * 1)(X; ℚ)) ∈ Hdg^1(X; ℚ)) ↔
      ∀ x y, E.baseChange ℝ (I x) (I y) = E.baseChange ℝ x y := by
    rw [hclass, pol1_complexify_invariant_iff,
      ← pol1_invariant_iff_skew (E.baseChange ℂ) C hC2]
    constructor <;> intro h x y <;> have hh := h x y
    · simpa only [hIC, LinearMap.neg_apply, map_neg, neg_neg] using hh
    · simpa only [hIC, LinearMap.neg_apply, map_neg, neg_neg] using hh
  have hiso := pol1_real_invariant_iff_hodge_isotropic M E
    (h10_sup_h01_eq_top hF hB hD hT) I hIC
  constructor
  · intro h
    have hi := hinv.mp h
    exact ⟨hiso.mp hi, hi⟩
  · intro h
    exact hinv.mpr h.2

private def pol1_tensorRe {W : Type*} [AddCommGroup W] [Module ℝ W] :
    ℂ ⊗[ℝ] W →ₗ[ℝ] W :=
  (TensorProduct.lid ℝ W).toLinearMap.comp (TensorProduct.map Complex.reLm LinearMap.id)

private theorem pol1_tensorRe_tmul {W : Type*} [AddCommGroup W] [Module ℝ W]
    (a : ℂ) (x : W) : pol1_tensorRe (a ⊗ₜ[ℝ] x) = a.re • x := by
  simp [pol1_tensorRe]

private theorem pol1_tensor_split {W : Type*} [AddCommGroup W] [Module ℝ W]
    (z : ℂ ⊗[ℝ] W) : ∃ x y : W, z = 1 ⊗ₜ[ℝ] x + Complex.I ⊗ₜ[ℝ] y := by
  induction z using TensorProduct.inductionOn with
  | tmul a x =>
    refine ⟨a.re • x, a.im • x, ?_⟩
    rw [← TensorProduct.smul_tmul a.re (1 : ℂ) x,
      ← TensorProduct.smul_tmul a.im Complex.I x, ← TensorProduct.add_tmul]
    congr 1
    simp [Algebra.smul_def]
  | add z w hz hw =>
    obtain ⟨x,y,rfl⟩ := hz
    obtain ⟨x',y',rfl⟩ := hw
    refine ⟨x+x', y+y', ?_⟩
    simp only [TensorProduct.tmul_add]
    abel

private theorem pol1_eigenvector_real_form {W : Type*} [AddCommGroup W] [Module ℝ W]
    (J : Module.End ℝ W) (z : ℂ ⊗[ℝ] W)
    (hz : J.baseChange ℂ z = -Complex.I • z) :
    ∃ x : W, z = 1 ⊗ₜ[ℝ] x + Complex.I ⊗ₜ[ℝ] J x := by
  obtain ⟨x,y,rfl⟩ := pol1_tensor_split z
  have hh := congrArg pol1_tensorRe hz
  simp only [map_add, LinearMap.baseChange_tmul, smul_add, TensorProduct.smul_tmul',
    pol1_tensorRe_tmul] at hh
  have hy : J x = y := by simpa using hh
  exact ⟨x, by rw [hy]⟩

private theorem pol1_real_form_eigenvector {W : Type*} [AddCommGroup W] [Module ℝ W]
    (J : Module.End ℝ W) (hJ : ∀ x, J (J x) = -x) (x : W) :
    J.baseChange ℂ (1 ⊗ₜ[ℝ] x + Complex.I ⊗ₜ[ℝ] J x) =
      -Complex.I • (1 ⊗ₜ[ℝ] x + Complex.I ⊗ₜ[ℝ] J x) := by
  simp [LinearMap.baseChange_tmul, hJ, smul_add, TensorProduct.smul_tmul',
    TensorProduct.neg_tmul, TensorProduct.tmul_neg, add_comm]

private theorem pol1_real_form_value {W : Type*} [AddCommGroup W] [Module ℝ W]
    (E : LinearMap.BilinForm ℝ W) (hE : E.IsAlt) (J : Module.End ℝ W) (x : W) :
    Complex.I * E.baseChange ℂ
      (1 ⊗ₜ[ℝ] x + Complex.I ⊗ₜ[ℝ] J x)
      ((TensorProduct.map Complex.conjAe.toLinearMap LinearMap.id)
        (1 ⊗ₜ[ℝ] x + Complex.I ⊗ₜ[ℝ] J x)) =
      (2 * E x (J x) : ℝ) := by
  simp only [map_add, TensorProduct.map_tmul, LinearMap.id_apply,
    LinearMap.add_apply, LinearMap.BilinForm.baseChange_tmul]
  have hswap : E (J x) x = -E x (J x) := (hE.neg_eq x (J x)).symm
  simp [hE x, hE (J x), hswap, Algebra.smul_def]
  ring_nf
  simp

private theorem pol1_positive_eigen_iff_real
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    (E : LinearMap.BilinForm ℝ W) (hE : E.IsAlt)
    (J : Module.End ℝ W) (hJ : ∀ x, J (J x) = -x) :
    (∀ z : ℂ ⊗[ℝ] W, J.baseChange ℂ z = -Complex.I • z → z ≠ 0 →
      0 < (Complex.I * E.baseChange ℂ z
        ((TensorProduct.map Complex.conjAe.toLinearMap LinearMap.id) z)).re) ↔
      ∀ x, x ≠ 0 → 0 < E x (J x) := by
  constructor
  · intro hp x hx
    have hz : (1 : ℂ) ⊗ₜ[ℝ] x + Complex.I ⊗ₜ[ℝ] J x ≠ 0 := by
      intro hz
      apply hx
      have hh := congrArg pol1_tensorRe hz
      simpa only [map_add, map_zero, pol1_tensorRe_tmul, Complex.one_re,
        Complex.I_re, one_smul, zero_smul, add_zero] using hh
    have hh := hp _ (pol1_real_form_eigenvector J hJ x) hz
    rw [pol1_real_form_value E hE J x, Complex.ofReal_re] at hh
    linarith
  · intro hp z hz hz0
    obtain ⟨x, rfl⟩ := pol1_eigenvector_real_form J z hz
    have hx : x ≠ 0 := by
      intro hx
      apply hz0
      simp only [hx, map_zero, TensorProduct.tmul_zero, add_zero]
    rw [pol1_real_form_value E hE J x, Complex.ofReal_re]
    exact mul_pos (by norm_num) (hp x hx)

private theorem pol1_sigma_cancel
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (z : ℂ ⊗[ℝ] (ℝ ⊗[ℚ] V)) :
    sigmaQ V (TensorProduct.AlgebraTensorModule.cancelBaseChange ℚ ℝ ℂ ℂ V z) =
      TensorProduct.AlgebraTensorModule.cancelBaseChange ℚ ℝ ℂ ℂ V
        ((TensorProduct.map Complex.conjAe.toLinearMap LinearMap.id) z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a x =>
    induction x using TensorProduct.inductionOn with
    | tmul r x =>
      change sigmaQR V _ = _
      simp [Algebra.smul_def]
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  | add z w hz hw => simp only [map_add, hz, hw]

private theorem pol1_mem_neg_eigen
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (J : Module.End ℂ W) (U V : Submodule ℂ W) (hUV : U ⊔ V = ⊤)
    (hU : ∀ x ∈ U, J x = -Complex.I • x)
    (hV : ∀ x ∈ V, J x = Complex.I • x) (z : W) :
    z ∈ U ↔ J z = -Complex.I • z := by
  constructor
  · exact hU z
  · intro hz
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp
      (show z ∈ U ⊔ V by rw [hUV]; trivial)
    have hv0 : (2 * Complex.I) • v = 0 := by
      calc
        _ = J (u + v) + Complex.I • (u + v) := by
          rw [map_add, hU u hu, hV v hv]
          module
        _ = 0 := by rw [hz]; module
    have hvzero : v = 0 := (smul_eq_zero.mp hv0).resolve_left
      (mul_ne_zero (by norm_num) Complex.I_ne_zero)
    simpa only [hvzero, add_zero] using hu

private theorem pol1_complexify_apply_cancel
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (I : Module.End ℝ (ℝ ⊗[ℚ] V)) (z : ℂ ⊗[ℝ] (ℝ ⊗[ℚ] V)) :
    complexifyRealEnd I (TensorProduct.AlgebraTensorModule.cancelBaseChange ℚ ℝ ℂ ℂ V z) =
      TensorProduct.AlgebraTensorModule.cancelBaseChange ℚ ℝ ℂ ℂ V (I.baseChange ℂ z) := by
  simp only [complexifyRealEnd, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]

private theorem pol1_weightOne_real_square
    {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    (M : QHodgeStructure 1 V)
    (hsupp : ∀ pq : ℤ × ℤ, pq ≠ (1, 0) → pq ≠ (0, 1) → M.H pq = ⊥)
    (I : Module.End ℝ (ℝ ⊗[ℚ] V))
    (hIC : complexifyRealEnd I = -gradingOperator M.H M.isInternal) :
    ∀ x, I (I x) = -x := by
  have hC := spec_eqw_gradingOperator_mul_self (H := M.H) (hH := M.isInternal) hsupp
  have hsq (z : ℂ ⊗[ℚ] V) : complexifyRealEnd I (complexifyRealEnd I z) = -z := by
    rw [hIC]
    simp only [LinearMap.neg_apply, map_neg, neg_neg]
    exact LinearMap.congr_fun hC z
  let e := TensorProduct.AlgebraTensorModule.cancelBaseChange ℚ ℝ ℂ ℂ V
  intro x
  have hh := hsq (e ((1 : ℂ) ⊗ₜ[ℝ] x))
  rw [pol1_complexify_apply_cancel, pol1_complexify_apply_cancel,
    LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, ← map_neg e] at hh
  have ht := congrArg pol1_tensorRe (e.injective hh)
  simpa only [map_neg, pol1_tensorRe_tmul, Complex.one_re, one_smul] using ht

private theorem pol1_real_baseChange_alt
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (E : LinearMap.BilinForm ℚ V) (hE : E.IsAlt) : (E.baseChange ℝ).IsAlt := by
  have hs (x y : ℝ ⊗[ℚ] V) : E.baseChange ℝ x y = -E.baseChange ℝ y x := by
    induction x using TensorProduct.inductionOn with
    | tmul a x =>
      induction y using TensorProduct.inductionOn with
      | tmul b y =>
        simp only [LinearMap.BilinForm.baseChange_tmul]
        rw [← hE.neg_eq x y, neg_smul, neg_neg, mul_comm]
      | add y z hy hz => simp only [map_add, LinearMap.add_apply, hy, hz, neg_add_rev]; abel
    | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz, neg_add_rev]; abel
  intro x
  have hh := hs x x
  linarith

/-- For the geometric sign `I = -C`, Hermitian positivity on `H^{1,0}` is
exactly strict positivity of the real form `E(x,Ix)`. -/
theorem pol1_hodge_positive_iff_real
    {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    (M : QHodgeStructure 1 V) (E : LinearMap.BilinForm ℚ V) (hE : E.IsAlt)
    (hsupp : ∀ pq : ℤ × ℤ, pq ≠ (1, 0) → pq ≠ (0, 1) → M.H pq = ⊥)
    (hsup : M.H (1, 0) ⊔ M.H (0, 1) = ⊤)
    (I : Module.End ℝ (ℝ ⊗[ℚ] V))
    (hIC : complexifyRealEnd I = -gradingOperator M.H M.isInternal) :
    (∀ x ∈ M.H (1, 0), x ≠ 0 →
      0 < (Complex.I * E.baseChange ℂ x (sigmaQ V x)).re) ↔
      ∀ x, x ≠ 0 → 0 < E.baseChange ℝ x (I x) := by
  let e := TensorProduct.AlgebraTensorModule.cancelBaseChange ℚ ℝ ℂ ℂ V
  have he (x y : ℂ ⊗[ℝ] (ℝ ⊗[ℚ] V)) :
      E.baseChange ℂ (e x) (e y) = (E.baseChange ℝ).baseChange ℂ x y :=
    LinearMap.congr_fun₂ (pol1_bilin_cancelBaseChange E) x y
  have hu (x : ℂ ⊗[ℚ] V) (hx : x ∈ M.H (1, 0)) :
      complexifyRealEnd I x = -Complex.I • x := by
    rw [hIC, LinearMap.neg_apply, gradingOperator_apply_of_mem M.H M.isInternal hx]
    simp
  have hv (x : ℂ ⊗[ℚ] V) (hx : x ∈ M.H (0, 1)) :
      complexifyRealEnd I x = Complex.I • x := by
    rw [hIC, LinearMap.neg_apply, gradingOperator_apply_of_mem M.H M.isInternal hx]
    simp
  have hm (z : ℂ ⊗[ℝ] (ℝ ⊗[ℚ] V)) :
      e z ∈ M.H (1, 0) ↔ I.baseChange ℂ z = -Complex.I • z := by
    rw [pol1_mem_neg_eigen _ _ _ hsup hu hv, pol1_complexify_apply_cancel,
      ← map_smul e, e.injective.eq_iff]
  rw [← pol1_positive_eigen_iff_real (E.baseChange ℝ) (pol1_real_baseChange_alt E hE)
    I (pol1_weightOne_real_square M hsupp I hIC)]
  constructor
  · intro hp z hz hz0
    have hh := hp (e z) ((hm z).mpr hz) (by
      intro hz
      apply hz0
      apply e.injective
      simpa only [map_zero] using hz)
    rwa [pol1_sigma_cancel, he] at hh
  · intro hp x hx hx0
    obtain ⟨z, rfl⟩ := e.surjective x
    have hh := hp z ((hm z).mp hx) (by
      intro hz
      apply hx0
      rw [hz, map_zero])
    rwa [pol1_sigma_cancel, he]

theorem spec_polarizationPositive_iff_aux
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (hF : FiniteBetti X) (hB : BettiDeRhamIso X)
    {η : HQ X 2} (hω : Symplectic.IsNondegenerate
      (polarizationVec (torusCohomology_cupProductOf X) η))
    (I : ℝ ⊗[ℚ] HQ X 1 →ₗ[ℝ] ℝ ⊗[ℚ] HQ X 1)
    (hIC : let hT := torusCohomology_cupProductOf X
      letI := hT.finite
      let hD := spec_hodgeDecomposition_of_cupLeft_alone X hT (spec_cupLeft_cupProductOf X)
      complexifyRealEnd I = -gradingOperator
        (abelianVarietyCohomologyOf hF hB hD hT).weight1.H
        (abelianVarietyCohomologyOf hF hB hD hT).weight1.isInternal) :
    let hT := torusCohomology_cupProductOf X
    let hD := spec_hodgeDecomposition_of_cupLeft_alone X hT (spec_cupLeft_cupProductOf X)
    PolarizationPositive hF hB hD hT hω ↔
      ((η : H^(2 * 1)(X; ℚ)) ∈ Hdg^1(X; ℚ) ∧
        ∀ x, x ≠ 0 → 0 < (polarizationForm hT hω).baseChange ℝ x (I x)) := by
  let hT := torusCohomology_cupProductOf X
  letI := hT.finite
  let hD := spec_hodgeDecomposition_of_cupLeft_alone X hT
    (spec_cupLeft_cupProductOf X)
  let M := (abelianVarietyCohomologyOf hF hB hD hT).weight1
  let E := polarizationForm hT hω
  have hsupp : ∀ pq : ℤ × ℤ, pq ≠ (1, 0) → pq ≠ (0, 1) → M.H pq = ⊥ := by
    intro pq h10 h01
    exact cohomologyHodgePiece_one_eq_bot X pq h10 h01
  have hsup := h10_sup_h01_eq_top hF hB hD hT
  have hAlt := isAlt_polarizationForm hT hω
  have hfirst := spec_firstRiemannRelation_aux X hF hB hω I hIC
  have hlinear := pol1_real_invariant_iff_hodge_isotropic M E hsup I hIC
  have hpositive := pol1_hodge_positive_iff_real M E hAlt hsupp hsup I hIC
  constructor
  · rintro ⟨P, hP⟩
    change P.form = E at hP
    have hiso :
        (∀ x ∈ M.H (1, 0), ∀ y ∈ M.H (1, 0), E.baseChange ℂ x y = 0) ∧
        (∀ x ∈ M.H (0, 1), ∀ y ∈ M.H (0, 1), E.baseChange ℂ x y = 0) := by
      constructor
      · intro x hx y hy
        rw [← hP]
        exact P.orthogonal_of_ne_swap (by norm_num) hx hy
      · intro x hx y hy
        rw [← hP]
        exact P.orthogonal_of_ne_swap (by norm_num) hx hy
    refine ⟨hfirst.mpr ⟨hiso, hlinear.mpr hiso⟩, hpositive.mp ?_⟩
    intro x hx hx0
    have hp := P.positive 1 0 (by norm_num) x hx hx0
    simpa only [Iexp, sub_zero, zpow_one, hP] using hp
  · rintro ⟨hclass, hp⟩
    have hiso := (hfirst.mp hclass).1
    apply (pol1_polarisation_iff_h10_positive M E hAlt
      (nondegenerate_polarizationForm hT hω) hsupp hiso.1 hiso.2).mpr
    exact hpositive.mpr hp

theorem spec_isWeilType_iff_hermSignature_eq_aux
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (hF : FiniteBetti X) (hB : BettiDeRhamIso X)
    {d : ℚ} (hd : 0 < d) [Fact (∀ r : ℚ, r ^ 2 ≠ -d + 0 * r)]
    (hdim : dim X.left = 6)
    (A : let hT := torusCohomology_cupProductOf X
      letI := hT.finite
      let hD := spec_hodgeDecomposition_of_cupLeft_alone X hT (spec_cupLeft_cupProductOf X)
      WeilAction (abelianVarietyCohomologyOf hF hB hD hT).weight1 d)
    {η : HQ X 2} (hω : Symplectic.IsNondegenerate
      (polarizationVec (torusCohomology_cupProductOf X) η))
    (hR : let hT := torusCohomology_cupProductOf X
      letI := hT.finite
      IsRosatiSkew (polarizationVec hT η) A.J)
    (hpos : let hT := torusCohomology_cupProductOf X
      let hD := spec_hodgeDecomposition_of_cupLeft_alone X hT (spec_cupLeft_cupProductOf X)
      PolarizationPositive hF hB hD hT hω) :
    let hT := torusCohomology_cupProductOf X
    letI := hT.finite
    A.IsWeilType ↔
      hermSignature (weilHermitian (polarizationForm hT hω) ⟨A.J, A.J_sq⟩
        (polarizationForm_skew hT hω hR)) = (3, 3) := by
  let hT := torusCohomology_cupProductOf X
  letI := hT.finite
  let hD := spec_hodgeDecomposition_of_cupLeft_alone X hT
    (spec_cupLeft_cupProductOf X)
  let S := abelianVarietyCohomologyOf hF hB hD hT
  obtain ⟨I, hI, hIC, hdict⟩ :=
    spec_exists_weightOneComplexStructure_dictionary_aux X hF hB
  have hpositive :=
    (spec_polarizationPositive_iff_aux X hF hB hω I hIC).mp hpos
  let AJ : S.weight1.Hom S.weight1 := ⟨A.J, A.preserves⟩
  have hcommC : complexifyRealEnd I * A.J.baseChange ℂ =
      A.J.baseChange ℂ * complexifyRealEnd I := by
    apply LinearMap.ext
    intro x
    change complexifyRealEnd I (A.J.baseChange ℂ x) =
      A.J.baseChange ℂ (complexifyRealEnd I x)
    rw [hIC]
    exact LinearMap.congr_fun (negGradingOperator_commutes S.weight1 AJ) x
  have hcommR := realEnd_commutes_of_complexify_commutes I A.J hcommC
  apply isWeilType_iff_hermSignature_eq hF hB hD hT hd hdim A hω hR I hI
  · intro x
    exact LinearMap.congr_fun hcommR x
  · exact hpositive.2
  · exact hdict hd A

theorem spec_polarizationPositive_isotropic_aux
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (hF : FiniteBetti X) (hB : BettiDeRhamIso X)
    {η : HQ X 2} (hω : Symplectic.IsNondegenerate
      (polarizationVec (torusCohomology_cupProductOf X) η))
    (hpos : let hT := torusCohomology_cupProductOf X
      let hD := spec_hodgeDecomposition_of_cupLeft_alone X hT
        (spec_cupLeft_cupProductOf X)
      PolarizationPositive hF hB hD hT hω) :
    let hT := torusCohomology_cupProductOf X
    letI := hT.finite
    let hD := spec_hodgeDecomposition_of_cupLeft_alone X hT
      (spec_cupLeft_cupProductOf X)
    let S := abelianVarietyCohomologyOf hF hB hD hT
    (∀ x ∈ S.weight1.H (1, 0), ∀ y ∈ S.weight1.H (1, 0),
      (polarizationForm hT hω).baseChange ℂ x y = 0) ∧
    (∀ x ∈ S.weight1.H (0, 1), ∀ y ∈ S.weight1.H (0, 1),
      (polarizationForm hT hω).baseChange ℂ x y = 0) := by
  dsimp only at hpos ⊢
  letI := (torusCohomology_cupProductOf X).finite
  obtain ⟨P, hP⟩ := hpos
  constructor
  · intro x hx y hy
    rw [← hP]
    exact P.orthogonal_of_ne_swap (by norm_num) hx hy
  · intro x hx y hy
    rw [← hP]
    exact P.orthogonal_of_ne_swap (by norm_num) hx hy

theorem spec_neg_not_polarizationPositive_aux
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (hF : FiniteBetti X) (hB : BettiDeRhamIso X)
    (hdim : 0 < dim X.left)
    {η : HQ X 2}
    (hω : Symplectic.IsNondegenerate
      (polarizationVec (torusCohomology_cupProductOf X) η))
    (hωneg : Symplectic.IsNondegenerate
      (polarizationVec (torusCohomology_cupProductOf X) (-η)))
    (hpos : let hT := torusCohomology_cupProductOf X
      let hD := spec_hodgeDecomposition_of_cupLeft_alone X hT
        (spec_cupLeft_cupProductOf X)
      PolarizationPositive hF hB hD hT hω) :
    let hT := torusCohomology_cupProductOf X
    let hD := spec_hodgeDecomposition_of_cupLeft_alone X hT
      (spec_cupLeft_cupProductOf X)
    ¬ PolarizationPositive hF hB hD hT hωneg := by
  dsimp only at hpos ⊢
  let hT := torusCohomology_cupProductOf X
  letI := hT.finite
  let hD := spec_hodgeDecomposition_of_cupLeft_alone X hT
    (spec_cupLeft_cupProductOf X)
  let S := abelianVarietyCohomologyOf hF hB hD hT
  have hvecneg : polarizationVec hT (-η) = -polarizationVec hT η := by
    simp [polarizationVec]
  have hformneg : polarizationForm hT hωneg = -polarizationForm hT hω := by
    ext x y
    obtain ⟨φ, rfl⟩ := hω.2 x
    obtain ⟨ψ, rfl⟩ := hω.2 y
    have hx : contract (polarizationVec hT (-η)) (-φ) =
        contract (polarizationVec hT η) φ := by
      rw [hvecneg]
      simp
    have hy : contract (polarizationVec hT (-η)) (-ψ) =
        contract (polarizationVec hT η) ψ := by
      rw [hvecneg]
      simp
    rw [polarizationForm, polarizationForm, ← hx, ← hy,
      dualForm_contract_contract]
    simp only [LinearMap.neg_apply, LinearMap.flip_apply, hx, hy,
      dualForm_contract_contract]
  intro hneg
  obtain ⟨P, hP⟩ := hpos
  obtain ⟨Pneg, hPneg⟩ := hneg
  have hrank : 0 < Module.finrank ℂ ↥(S.weight1.H (1, 0)) := by
    change 0 < Module.finrank ℂ (cohomologyHodgePiece X 1 (1, 0))
    rw [(spec_finrank_cohomologyHodgePiece_one X hD).1]
    exact hdim
  letI : Nontrivial ↥(S.weight1.H (1, 0)) := Module.nontrivial_of_finrank_pos hrank
  obtain ⟨x, hx⟩ := exists_ne (0 : ↥(S.weight1.H (1, 0)))
  have hpx := P.positive 1 0 (by norm_num) (x : ℂ ⊗[ℚ] HQ X 1) x.2 (by simpa)
  have hpn := Pneg.positive 1 0 (by norm_num) (x : ℂ ⊗[ℚ] HQ X 1) x.2 (by simpa)
  rw [hP] at hpx
  rw [hPneg, hformneg] at hpn
  have hbcneg : (-polarizationForm hT hω).baseChange ℂ =
      -(polarizationForm hT hω).baseChange ℂ := by
    change LinearMap.BilinForm.tensorDistrib ℚ ℂ
        ((LinearMap.mul ℂ ℂ) ⊗ₜ[ℚ] (-polarizationForm hT hω)) = _
    rw [TensorProduct.tmul_neg, map_neg]
    rfl
  rw [hbcneg] at hpn
  simp only [Iexp, sub_zero, zpow_one] at hpx hpn
  simp at hpx hpn
  linarith

theorem spec_pol1IsotropicLine_orthogonal_aux :
    pol1StandardSymplectic.orthogonal pol1IsotropicLine = pol1IsotropicLine := by
  ext x
  change (∀ y ∈ pol1IsotropicLine, pol1StandardSymplectic y x = 0) ↔
    x ∈ pol1IsotropicLine
  rw [pol1IsotropicLine]
  simp only [Submodule.mem_span_singleton]
  constructor
  · intro hx
    have h := hx ![1, 0] ⟨1, by simp⟩
    simp only [pol1StandardSymplectic, LinearMap.mk₂_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, mul_zero, one_mul, zero_mul, sub_zero] at h
    refine ⟨x 0, ?_⟩
    funext i
    fin_cases i <;> simp [h]
  · rintro ⟨a, rfl⟩ y hy
    simp only [pol1StandardSymplectic, LinearMap.mk₂_apply, Pi.smul_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons,
      smul_eq_mul, mul_one, mul_zero, zero_mul, sub_zero]
    obtain ⟨b, rfl⟩ := hy
    simp

theorem spec_weightOneComplexOperator_h10_aux
    {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    (M : QHodgeStructure 1 V) (x : ℂ ⊗[ℚ] V) (hx : x ∈ M.H (1, 0)) :
    (-gradingOperator M.H M.isInternal) x = -Complex.I • x := by
  rw [LinearMap.neg_apply, gradingOperator_apply_of_mem M.H M.isInternal hx]
  simp

theorem spec_weightOneComplexOperator_h01_aux
    {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    (M : QHodgeStructure 1 V) (x : ℂ ⊗[ℚ] V) (hx : x ∈ M.H (0, 1)) :
    (-gradingOperator M.H M.isInternal) x = Complex.I • x := by
  rw [LinearMap.neg_apply, gradingOperator_apply_of_mem M.H M.isInternal hx]
  simp

theorem spec_weightOneComplexOperator_commutes_aux
    {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    (M : QHodgeStructure 1 V) (T : M.Hom M) (x : ℂ ⊗[ℚ] V) :
    (-gradingOperator M.H M.isInternal) (T.toLinearMap.baseChange ℂ x) =
      T.toLinearMap.baseChange ℂ ((-gradingOperator M.H M.isInternal) x) := by
  have hcomm : (-gradingOperator M.H M.isInternal).comp (T.toLinearMap.baseChange ℂ) =
      (T.toLinearMap.baseChange ℂ).comp (-gradingOperator M.H M.isInternal) := by
    apply linearMap_ext_of_isInternal M.isInternal
    intro pq y hy
    have hTy : T.toLinearMap.baseChange ℂ y ∈ M.H pq :=
      T.maps_pieces pq (Submodule.mem_map_of_mem hy)
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.neg_apply, LinearMap.neg_apply,
      gradingOperator_apply_of_mem M.H M.isInternal hTy,
      gradingOperator_apply_of_mem M.H M.isInternal hy, map_neg, map_smul]
  exact LinearMap.congr_fun hcomm x

private def pol1SkewMapQ {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    (E : LinearMap.BilinForm ℚ V) :
    Module.End ℚ V →ₗ[ℚ] (Fin (Module.finrank ℚ V) × Fin (Module.finrank ℚ V) → ℚ) :=
  let b := Module.finBasis ℚ V
  { toFun := fun A ij => E (A (b ij.1)) (b ij.2) + E (b ij.1) (A (b ij.2))
    map_add' := by intros; funext ij; simp; ring
    map_smul' := by intros; funext ij; simp [mul_add] }

private def pol1SkewMapC {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
    (E : LinearMap.BilinForm ℚ V) :
    Module.End ℂ (ℂ ⊗[ℚ] V) →ₗ[ℂ]
      (Fin (Module.finrank ℚ V) × Fin (Module.finrank ℚ V) → ℂ) :=
  let b := Algebra.TensorProduct.basis ℂ (Module.finBasis ℚ V)
  { toFun := fun A ij => E.baseChange ℂ (A (b ij.1)) (b ij.2) +
        E.baseChange ℂ (b ij.1) (A (b ij.2))
    map_add' := by intros; funext ij; simp; ring
    map_smul' := by intros; funext ij; simp [mul_add] }

private theorem pol1_mem_ker_skewMapQ {V : Type*} [AddCommGroup V] [Module ℚ V]
    [FiniteDimensional ℚ V] (E : LinearMap.BilinForm ℚ V) (A : Module.End ℚ V) :
    A ∈ LinearMap.ker (pol1SkewMapQ E) ↔
      ∀ x y, E (A x) y = -E x (A y) := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h
    have hB : E.compl₁₂ A LinearMap.id + E.compl₁₂ LinearMap.id A = 0 := by
      apply LinearMap.ext_basis (Module.finBasis ℚ V) (Module.finBasis ℚ V)
      intro k l
      have := congrFun h (k, l)
      simpa [pol1SkewMapQ] using this
    intro x y
    have := LinearMap.congr_fun₂ hB x y
    simp only [LinearMap.add_apply, LinearMap.compl₁₂_apply, LinearMap.id_apply,
      LinearMap.zero_apply] at this
    exact eq_neg_of_add_eq_zero_left this
  · intro h
    funext p
    simp [pol1SkewMapQ, h]

private theorem pol1_mem_ker_skewMapC {V : Type*} [AddCommGroup V] [Module ℚ V]
    [FiniteDimensional ℚ V] (E : LinearMap.BilinForm ℚ V)
    (A : Module.End ℂ (ℂ ⊗[ℚ] V)) :
    A ∈ LinearMap.ker (pol1SkewMapC E) ↔
      ∀ x y, E.baseChange ℂ (A x) y = -E.baseChange ℂ x (A y) := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h
    have hB : (E.baseChange ℂ).compl₁₂ A LinearMap.id +
        (E.baseChange ℂ).compl₁₂ LinearMap.id A = 0 := by
      apply LinearMap.ext_basis (Algebra.TensorProduct.basis ℂ (Module.finBasis ℚ V))
        (Algebra.TensorProduct.basis ℂ (Module.finBasis ℚ V))
      intro k l
      have := congrFun h (k, l)
      simpa [Algebra.TensorProduct.basis_apply, pol1SkewMapC] using this
    intro x y
    have := LinearMap.congr_fun₂ hB x y
    simp only [LinearMap.add_apply, LinearMap.compl₁₂_apply, LinearMap.id_apply,
      LinearMap.zero_apply] at this
    exact eq_neg_of_add_eq_zero_left this
  · intro h
    funext p
    simp [pol1SkewMapC, h]

private theorem pol1_complexSpan_ker_skewMap {V : Type*} [AddCommGroup V] [Module ℚ V]
    [FiniteDimensional ℚ V] (E : LinearMap.BilinForm ℚ V) :
    complexSpan (LinearMap.ker (pol1SkewMapQ E)) =
      LinearMap.ker (pol1SkewMapC E) := by
  -- Scalar extension commutes with the kernel of the skew-adjointness equations.
  let ψ := (TensorProduct.piScalarRight ℚ ℂ ℂ
    (Fin (Module.finrank ℚ V) × Fin (Module.finrank ℚ V))).toLinearMap
  have hcompat : ∀ X : Module.End ℚ V,
      pol1SkewMapC E (X.baseChange ℂ) = ψ (1 ⊗ₜ[ℚ] pol1SkewMapQ E X) := by
    intro X
    funext p
    simp [ψ, pol1SkewMapC, pol1SkewMapQ, TensorProduct.piScalarRightHom_tmul,
      LinearMap.BilinForm.baseChange_tmul]
  have key : ∀ y : ℂ ⊗[ℚ] Module.End ℚ V,
      ψ ((pol1SkewMapQ E).baseChange ℂ y) =
        pol1SkewMapC E (endBaseChangeEquiv V y) := by
    intro y
    induction y using TensorProduct.inductionOn with
    | tmul z X =>
      rw [LinearMap.baseChange_tmul, endBaseChangeEquiv_apply, tensorProductEnd_tmul,
        map_smul, hcompat, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    | add y y' hy hy' => simp only [map_add, hy, hy']
  ext c
  rw [mem_complexSpan_iff, ← ker_baseChange_eq, LinearMap.mem_ker, LinearMap.mem_ker,
    ← (TensorProduct.piScalarRight ℚ ℂ ℂ _).injective.eq_iff, map_zero]
  change ψ ((pol1SkewMapQ E).baseChange ℂ ((endBaseChangeEquiv V).symm c)) = 0 ↔ _
  rw [key, LinearEquiv.apply_symm_apply]

private def pol1SkewLie {V : Type*} [AddCommGroup V] [Module ℚ V]
    [FiniteDimensional ℚ V] (E : LinearMap.BilinForm ℚ V) :
    LieSubalgebra ℚ (Module.End ℚ V) where
  toSubmodule := LinearMap.ker (pol1SkewMapQ E)
  lie_mem' := by
    intro A B hA hB
    apply (pol1_mem_ker_skewMapQ E _).2
    have hA' := (pol1_mem_ker_skewMapQ E A).1 hA
    have hB' := (pol1_mem_ker_skewMapQ E B).1 hB
    intro x y
    rw [Ring.lie_def]
    simp only [LinearMap.sub_apply, Module.End.mul_apply]
    rw [map_sub E, map_sub (E x)]
    change E (A (B x)) y - E (B (A x)) y =
      -(E x (A (B y)) - E x (B (A y)))
    rw [hA' (B x) y, hB' (A x) y, hB' x (A y), hA' x (B y)]
    module

theorem spec_polarization_hodgeLieAlgebra_skew_aux
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (hF : FiniteBetti X) (hB : BettiDeRhamIso X)
    {A : Module.End ℚ (HQ X 1)} {x y : HQ X 1} {eta : HQ X 2}
    (homega : Symplectic.IsNondegenerate
      (polarizationVec (torusCohomology_cupProductOf X) eta))
    (hfirst : (eta : H^(2 * 1)(X; ℚ)) ∈ Hdg^1(X; ℚ))
    (hA : let hT := torusCohomology_cupProductOf X
      letI := hT.finite
      let hD := spec_hodgeDecomposition_of_cupLeft_alone X hT
        (spec_cupLeft_cupProductOf X)
      A ∈ hodgeLieAlgebra (abelianVarietyCohomologyOf hF hB hD hT).weight1.H
        (abelianVarietyCohomologyOf hF hB hD hT).weight1.isInternal) :
    let hT := torusCohomology_cupProductOf X
    letI := hT.finite
    polarizationForm hT homega (A x) y = -polarizationForm hT homega x (A y) := by
  let hT := torusCohomology_cupProductOf X
  letI := hT.finite
  let hD := spec_hodgeDecomposition_of_cupLeft_alone X hT
    (spec_cupLeft_cupProductOf X)
  let M := (abelianVarietyCohomologyOf hF hB hD hT).weight1
  let E := polarizationForm hT homega
  obtain ⟨I, -, hIC, -⟩ :=
    spec_exists_weightOneComplexStructure_dictionary_aux X hF hB
  have hiso := ((spec_firstRiemannRelation_aux X hF hB homega I hIC).mp hfirst).1
  have hCskew : ∀ u v : ℂ ⊗[ℚ] HQ X 1,
      E.baseChange ℂ (gradingOperator M.H M.isInternal u) v =
        -E.baseChange ℂ u (gradingOperator M.H M.isInternal v) := by
    intro u v
    have hu : u ∈ ⨆ i, M.H i := by
      rw [M.isInternal.submodule_iSup_eq_top]
      trivial
    induction hu using Submodule.iSup_induction' with
    | zero => simp
    | add u u' _ _ hu hu' => simp [hu, hu']; ring
    | mem pq u hu =>
      have hv : v ∈ ⨆ i, M.H i := by
        rw [M.isInternal.submodule_iSup_eq_top]
        trivial
      induction hv using Submodule.iSup_induction' with
      | zero => simp
      | add v v' _ _ hv hv' => simp [hv, hv']; ring
      | mem rs v hv =>
        by_cases hpq10 : pq = (1, 0)
        · subst pq
          by_cases hrs10 : rs = (1, 0)
          · subst rs
            rw [gradingOperator_apply_of_mem M.H M.isInternal hu,
              gradingOperator_apply_of_mem M.H M.isInternal hv]
            have hz := hiso.1 u hu v hv
            simp only [map_smul, LinearMap.smul_apply]
            rw [hz]
            simp
          · by_cases hrs01 : rs = (0, 1)
            · subst rs
              rw [gradingOperator_apply_of_mem M.H M.isInternal hu,
                gradingOperator_apply_of_mem M.H M.isInternal hv]
              simp only [map_smul, LinearMap.smul_apply]
              ring
            · have hrsbot : M.H rs = ⊥ := by
                change cohomologyHodgePiece X 1 rs = ⊥
                exact cohomologyHodgePiece_one_eq_bot X rs hrs10 hrs01
              rw [hrsbot] at hv
              simp only [Submodule.mem_bot] at hv
              subst v
              simp
        · by_cases hpq01 : pq = (0, 1)
          · subst pq
            by_cases hrs10 : rs = (1, 0)
            · subst rs
              rw [gradingOperator_apply_of_mem M.H M.isInternal hu,
                gradingOperator_apply_of_mem M.H M.isInternal hv]
              simp only [map_smul, LinearMap.smul_apply]
              ring
            · by_cases hrs01 : rs = (0, 1)
              · subst rs
                rw [gradingOperator_apply_of_mem M.H M.isInternal hu,
                  gradingOperator_apply_of_mem M.H M.isInternal hv]
                have hz := hiso.2 u hu v hv
                simp only [map_smul, LinearMap.smul_apply]
                rw [hz]
                simp
              · have hrsbot : M.H rs = ⊥ := by
                  change cohomologyHodgePiece X 1 rs = ⊥
                  exact cohomologyHodgePiece_one_eq_bot X rs hrs10 hrs01
                rw [hrsbot] at hv
                simp only [Submodule.mem_bot] at hv
                subst v
                simp
          · have hpqbot : M.H pq = ⊥ := by
              change cohomologyHodgePiece X 1 pq = ⊥
              exact cohomologyHodgePiece_one_eq_bot X pq hpq10 hpq01
            rw [hpqbot] at hu
            simp only [Submodule.mem_bot] at hu
            subst u
            simp
  have hspan : gradingOperator M.H M.isInternal ∈
      complexSpan (pol1SkewLie E).toSubmodule := by
    change gradingOperator M.H M.isInternal ∈
      complexSpan (LinearMap.ker (pol1SkewMapQ E))
    rw [pol1_complexSpan_ker_skewMap]
    exact (pol1_mem_ker_skewMapC E _).2 hCskew
  have hle : hodgeLieAlgebra M.H M.isInternal ≤ pol1SkewLie E :=
    hodgeLieAlgebra_le M.H M.isInternal hspan
  exact (pol1_mem_ker_skewMapQ E A).1 (hle hA) x y

private theorem pol1_baseChange_map {R S V : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup V] [Module R V]
    (P : Submodule R V) (f : V →ₗ[R] V) :
    (P.map f).baseChange S = (P.baseChange S).map (f.baseChange S) := by
  rw [Submodule.baseChange_eq_span, Submodule.baseChange_eq_span, Submodule.map_span]
  congr 1
  ext z
  constructor
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨1 ⊗ₜ[R] v, ⟨v, hv, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨f v, ⟨v, hv, rfl⟩, rfl⟩

private theorem pol1_mem_of_tmul_mem_baseChange {R S V : Type*} [Field R] [Field S]
    [Algebra R S] [AddCommGroup V] [Module R V] (P : Submodule R V) (x : V)
    (hx : 1 ⊗ₜ[R] x ∈ P.baseChange S) : x ∈ P := by
  have hle : P.baseChange S ≤ LinearMap.ker (P.mkQ.baseChange S) := by
    rw [Submodule.baseChange_eq_span, Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    change P.mkQ.baseChange S (1 ⊗ₜ[R] y) = 0
    rw [LinearMap.baseChange_tmul, Submodule.mkQ_apply,
      (Submodule.Quotient.mk_eq_zero P).mpr hy, TensorProduct.tmul_zero]
  have hz := hle hx
  rw [LinearMap.mem_ker, LinearMap.baseChange_tmul] at hz
  have : P.mkQ x = 0 := by simpa using hz
  rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this

set_option maxHeartbeats 400000 in
theorem spec_polarization_orthogonal_stable_complement_aux
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (hF : FiniteBetti X) (hB : BettiDeRhamIso X)
    {eta : HQ X 2} (homega : Symplectic.IsNondegenerate
      (polarizationVec (torusCohomology_cupProductOf X) eta))
    (hpos : let hT := torusCohomology_cupProductOf X
      let hD := spec_hodgeDecomposition_of_cupLeft_alone X hT
        (spec_cupLeft_cupProductOf X)
      PolarizationPositive hF hB hD hT homega)
    (W : Submodule ℚ (HQ X 1))
    (hW : let hT := torusCohomology_cupProductOf X
      letI := hT.finite
      let hD := spec_hodgeDecomposition_of_cupLeft_alone X hT
        (spec_cupLeft_cupProductOf X)
      ∀ A ∈ hodgeLieAlgebra (abelianVarietyCohomologyOf hF hB hD hT).weight1.H
        (abelianVarietyCohomologyOf hF hB hD hT).weight1.isInternal,
        W.map A ≤ W) :
    let hT := torusCohomology_cupProductOf X
    letI := hT.finite
    let hD := spec_hodgeDecomposition_of_cupLeft_alone X hT
      (spec_cupLeft_cupProductOf X)
    let L := hodgeLieAlgebra (abelianVarietyCohomologyOf hF hB hD hT).weight1.H
      (abelianVarietyCohomologyOf hF hB hD hT).weight1.isInternal
    let Wperp := (polarizationForm hT homega).orthogonal W
    (∀ A ∈ L, Wperp.map A ≤ Wperp) ∧ W ⊓ Wperp = ⊥ ∧ W ⊔ Wperp = ⊤ := by
  let hT := torusCohomology_cupProductOf X
  letI := hT.finite
  let hD := spec_hodgeDecomposition_of_cupLeft_alone X hT
    (spec_cupLeft_cupProductOf X)
  let M := (abelianVarietyCohomologyOf hF hB hD hT).weight1
  letI : LieRing (Module.End ℚ (HQ X 1)) := LieRing.ofAssociativeRing
  let L := hodgeLieAlgebra M.H M.isInternal
  let E := polarizationForm hT homega
  let Wperp := E.orthogonal W
  have hfirst : (eta : H^(2 * 1)(X; ℚ)) ∈ Hdg^1(X; ℚ) := by
    obtain ⟨I, -, hIC, -⟩ := spec_exists_weightOneComplexStructure_dictionary_aux X hF hB
    exact ((spec_polarizationPositive_iff_aux X hF hB homega I hIC).mp hpos).1
  have hstable : ∀ A ∈ L, Wperp.map A ≤ Wperp := by
    intro A hA z hz
    obtain ⟨x, hx, rfl⟩ := hz
    intro w hw
    change E w (A x) = 0
    rw [← neg_eq_zero, ← spec_polarization_hodgeLieAlgebra_skew_aux X hF hB homega hfirst hA]
    exact hx (A w) (hW A hA ⟨w, hw, rfl⟩)
  refine ⟨hstable, ?_⟩
  obtain ⟨I, hI, hIC, -⟩ := spec_exists_weightOneComplexStructure_dictionary_aux X hF hB
  have hposI : ∀ x, x ≠ 0 → 0 < E.baseChange ℝ x (I x) :=
    ((spec_polarizationPositive_iff_aux X hF hB homega I hIC).mp hpos).2
  have hWC : (W.baseChange ℂ).map
      (-gradingOperator M.H M.isInternal) ≤ W.baseChange ℂ := by
    let Stab : Submodule ℂ (Module.End ℂ (ℂ ⊗[ℚ] HQ X 1)) :=
      { carrier := {A | (W.baseChange ℂ).map A ≤ W.baseChange ℂ}
        zero_mem' := by simp
        add_mem' := by
          intro A B hA hB
          rintro z ⟨x, hx, rfl⟩
          exact (W.baseChange ℂ).add_mem (hA ⟨x, hx, rfl⟩) (hB ⟨x, hx, rfl⟩)
        smul_mem' := by
          intro c A hA
          rintro z ⟨x, hx, rfl⟩
          exact (W.baseChange ℂ).smul_mem c (hA ⟨x, hx, rfl⟩) }
    have hspan : complexSpan L.toSubmodule ≤ Stab := by
      rw [complexSpan, Submodule.span_le]
      rintro A ⟨a, ha, rfl⟩
      change (W.baseChange ℂ).map (a.baseChange ℂ) ≤ W.baseChange ℂ
      rw [← pol1_baseChange_map]
      exact Submodule.baseChange_mono ℂ (hW a ha)
    have hC : (W.baseChange ℂ).map (gradingOperator M.H M.isInternal) ≤ W.baseChange ℂ :=
      hspan (gradingOperator_mem_span_hodgeLieAlgebra M.H M.isInternal)
    rintro z ⟨x, hx, rfl⟩
    change -(gradingOperator M.H M.isInternal x) ∈ W.baseChange ℂ
    exact (W.baseChange ℂ).neg_mem (hC ⟨x, hx, rfl⟩)
  have hdisj : W ⊓ Wperp = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxR : (1 : ℝ) ⊗ₜ[ℚ] x ∈ W.baseChange ℝ :=
      Submodule.tmul_mem_baseChange_of_mem 1 hx.1
    have hIR : I ((1 : ℝ) ⊗ₜ[ℚ] x) ∈ W.baseChange ℝ := by
      let e := TensorProduct.AlgebraTensorModule.cancelBaseChange ℚ ℝ ℂ ℂ (HQ X 1)
      apply pol1_mem_of_tmul_mem_baseChange (R := ℝ) (S := ℂ) (W.baseChange ℝ)
      have hxC : e ((1 : ℂ) ⊗ₜ[ℝ] ((1 : ℝ) ⊗ₜ[ℚ] x)) ∈ W.baseChange ℂ := by
        simpa [e] using Submodule.tmul_mem_baseChange_of_mem 1 hx.1
      have hout : e ((1 : ℂ) ⊗ₜ[ℝ] I ((1 : ℝ) ⊗ₜ[ℚ] x)) ∈ W.baseChange ℂ := by
        have hc := hWC ⟨_, hxC, rfl⟩
        change (-gradingOperator M.H M.isInternal)
          (e ((1 : ℂ) ⊗ₜ[ℝ] ((1 : ℝ) ⊗ₜ[ℚ] x))) ∈ W.baseChange ℂ at hc
        rw [← hIC] at hc
        simpa [complexifyRealEnd, e] using hc
      have hbridge : W.baseChange ℂ ≤
          ((W.baseChange ℝ).baseChange ℂ).map e.toLinearMap := by
        rw [Submodule.baseChange_eq_span, Submodule.span_le]
        rintro _ ⟨w, hw, rfl⟩
        refine ⟨(1 : ℂ) ⊗ₜ[ℝ] ((1 : ℝ) ⊗ₜ[ℚ] w),
          Submodule.tmul_mem_baseChange_of_mem 1
            (Submodule.tmul_mem_baseChange_of_mem 1 hw), ?_⟩
        simp [e]
      obtain ⟨y, hy, hey⟩ := hbridge hout
      have := e.injective hey
      exact this ▸ hy
    have hzero : E.baseChange ℝ ((1 : ℝ) ⊗ₜ[ℚ] x) (I ((1 : ℝ) ⊗ₜ[ℚ] x)) = 0 := by
      let z := I ((1 : ℝ) ⊗ₜ[ℚ] x)
      change E.baseChange ℝ ((1 : ℝ) ⊗ₜ[ℚ] x) z = 0
      have hzmem : z ∈ W.baseChange ℝ := hIR
      rw [Submodule.baseChange_eq_span] at hzmem
      refine Submodule.span_induction (p := fun y _ =>
        E.baseChange ℝ ((1 : ℝ) ⊗ₜ[ℚ] x) y = 0) ?_ (by simp)
          (fun y z _ _ hy hz => by simp [hy, hz])
          (fun c y _ hy => by simp [hy]) hzmem
      rintro y ⟨w, hw, rfl⟩
      simpa [LinearMap.BilinForm.baseChange_tmul] using
        (isAlt_polarizationForm hT homega).eq_iff.mpr (hx.2 w hw)
    by_contra hx0
    have hxR0 : (1 : ℝ) ⊗ₜ[ℚ] x ≠ 0 := by simpa using hx0
    exact (ne_of_gt (hposI _ hxR0)) hzero
  have hc : IsCompl W Wperp :=
    (E.isCompl_orthogonal_iff_disjoint (isAlt_polarizationForm hT homega).isRefl).2
    (disjoint_iff.mpr hdisj)
  exact ⟨hdisj, hc.sup_eq_top⟩

end HodgeLean.Adapters
