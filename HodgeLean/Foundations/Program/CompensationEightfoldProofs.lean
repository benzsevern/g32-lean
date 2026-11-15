import HodgeLean.Foundations.Program.CompensationEightfoldTransport

/-! # Proof obligations for the eightfold compensation stage C8

Auxiliary theorems for the statements of `CompensationEightfold.lean`.
HC no distance; AV milestone no distance.
-/

set_option maxHeartbeats 400000
set_option maxRecDepth 10000

noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations ComplexConjugate

namespace HodgeLean.Foundations.Program

section Descent

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
  {M : HodgeBlocks.QHodgeStructure 1 V} {d : ℚ}

theorem cq8_weilClasses_span_aux (A : HodgeBlocks.WeilAction M d)
    (hH : M.H (1, 0) ⊔ M.H (0, 1) = ⊤) (hWeil : A.IsWeilType) (hd : 0 < d) :
    Submodule.span ℂ (HodgeBlocks.complexifyWedge _ '' (A.weilClasses hH hWeil : Set
      (⋀[ℚ]^(Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)) +
        Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0))) V))) =
      LinearMap.range (exteriorPower.map (Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)) +
          Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0))) A.Vs.subtype) ⊔
        LinearMap.range (exteriorPower.map (Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)) +
          Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0))) A.Vsbar.subtype) := by
  let k := Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0))
  let f := HodgeBlocks.WeilAction.derivationKernelOperatorQ A k
  let Φ := HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv (V := V) (k + k)
  have hexact : Function.Exact ((LinearMap.ker f).subtype.baseChange ℂ)
      (f.baseChange ℂ) := by
    simpa only [LinearMap.baseChange_eq_ltensor] using
      (Module.Flat.lTensor_exact ℂ f.exact_subtype_ker_map)
  have hrange : (LinearMap.ker f).baseChange ℂ = LinearMap.ker (f.baseChange ℂ) :=
    (LinearMap.exact_iff.mp hexact).symm
  have hconj := HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv_derivationKernelOperatorQ A k
  have hmap : ((LinearMap.ker f).baseChange ℂ).map Φ.toLinearMap =
      LinearMap.ker (HodgeBlocks.WeilAction.derivationKernelOperator A k) := by
    rw [hrange]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hh := LinearMap.congr_fun hconj y
      change Φ ((f.baseChange ℂ) y) =
        HodgeBlocks.WeilAction.derivationKernelOperator A k (Φ y) at hh
      change (f.baseChange ℂ) y = 0 at hy
      change HodgeBlocks.WeilAction.derivationKernelOperator A k (Φ y) = 0
      rw [← hh, hy, map_zero]
    · intro hx
      refine ⟨Φ.symm x, ?_, Φ.apply_symm_apply x⟩
      change (f.baseChange ℂ) (Φ.symm x) = 0
      apply Φ.injective
      have hh := LinearMap.congr_fun hconj (Φ.symm x)
      change Φ ((f.baseChange ℂ) (Φ.symm x)) =
        HodgeBlocks.WeilAction.derivationKernelOperator A k (Φ (Φ.symm x)) at hh
      rw [hh, Φ.apply_symm_apply]
      exact hx
  have hspan : ((LinearMap.ker f).baseChange ℂ).map Φ.toLinearMap =
      Submodule.span ℂ (HodgeBlocks.complexifyWedge (k + k) ''
        (LinearMap.ker f : Set (⋀[ℚ]^(k + k) V))) := by
    rw [Submodule.baseChange_eq_span, Submodule.map_span]
    congr 1
    ext x
    constructor
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      exact ⟨w, hw, (HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv_tmul _ _).symm⟩
    · rintro ⟨w, hw, rfl⟩
      refine ⟨1 ⊗ₜ[ℚ] w, ⟨w, hw, rfl⟩, ?_⟩
      exact HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv_tmul _ _
  rw [A.weilClasses_eq_ker_derivationKernelOperatorQ hH hWeil hd]
  change Submodule.span ℂ (HodgeBlocks.complexifyWedge (k + k) ''
    (LinearMap.ker f : Set (⋀[ℚ]^(k + k) V))) = _
  rw [← hspan, hmap]
  exact A.ker_derivationKernelOperator_eq_sup hH hWeil hd

theorem cq8_nonreal_eigenvector {U : Type*} [AddCommGroup U] [Module ℚ U]
    (T : Module.End ℚ U) (s : ℂ) (hs : conj s ≠ s) (w : U)
    (h : T.baseChange ℂ (1 ⊗ₜ[ℚ] w) = s • (1 ⊗ₜ[ℚ] w)) : w = 0 := by
  have hc := congrArg (HodgeBlocks.sigmaQ U) h
  simp only [HodgeBlocks.sigmaQ_baseChange, map_smulₛₗ] at hc
  have hfix : HodgeBlocks.sigmaQ U ((1 : ℂ) ⊗ₜ[ℚ] w) = 1 ⊗ₜ[ℚ] w := by
    change HodgeBlocks.sigmaQR U _ = _
    rw [HodgeBlocks.sigmaQ_tmul, map_one]
  rw [hfix] at hc
  have he : (conj s - s) • ((1 : ℂ) ⊗ₜ[ℚ] w) = 0 := by
    rw [sub_smul, ← hc, h, sub_self]
  have hz : (1 : ℂ) ⊗ₜ[ℚ] w = 0 :=
    (smul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr hs)
  apply HodgeBlocks.complexify_injective
  exact hz.trans (map_zero (HodgeBlocks.complexify U)).symm

theorem cq8_weilClasses_parts_ne_zero_aux (A : HodgeBlocks.WeilAction M d)
    (hH : M.H (1, 0) ⊔ M.H (0, 1) = ⊤) (hWeil : A.IsWeilType) (hd : 0 < d)
    (hκ : 1 ≤ Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)))
    {w : ⋀[ℚ]^(Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)) +
      Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0))) V}
    (hw : w ∈ A.weilClasses hH hWeil) (hw0 : w ≠ 0)
    {x y : ⋀[ℂ]^(Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)) +
      Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0))) (ℂ ⊗[ℚ] V)}
    (hx : x ∈ LinearMap.range (exteriorPower.map _ A.Vs.subtype))
    (hy : y ∈ LinearMap.range (exteriorPower.map _ A.Vsbar.subtype))
    (hxy : HodgeBlocks.complexifyWedge _ w = x + y) :
    x ≠ 0 ∧ y ≠ 0 := by
  let n := Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)) +
    Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0))
  have hn : n ≠ 0 := by omega
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hω : HodgeBlocks.WeilAction.omegaC d ≠ 0 :=
    HodgeBlocks.WeilAction.omegaC_ne_zero hd
  have hne : (n : ℂ) * HodgeBlocks.WeilAction.omegaC d ≠
      -((n : ℂ) * HodgeBlocks.WeilAction.omegaC d) := by
    intro hh
    have hz : (2 : ℂ) * ((n : ℂ) * HodgeBlocks.WeilAction.omegaC d) = 0 := by
      linear_combination hh
    exact (mul_ne_zero (by norm_num) (mul_ne_zero hnC hω)) hz
  have hside (s : ℂ) (z : ⋀[ℂ]^n (ℂ ⊗[ℚ] V))
      (hz : z ∈ LinearMap.range
        (exteriorPower.map n (Module.End.eigenspace A.Jc s).subtype)) :
      HodgeBlocks.derivationExt A.Jc n z = ((n : ℂ) * s) • z := by
    obtain ⟨v, rfl⟩ := hz
    exact LinearMap.congr_fun
      (HodgeBlocks.derivationExt_comp_exteriorPower_map_eigenspace A.Jc n s) v
  have hrat (s : ℂ) (hs : conj s ≠ s)
      (he : HodgeBlocks.derivationExt A.Jc n (HodgeBlocks.complexifyWedge n w) =
        s • HodgeBlocks.complexifyWedge n w) : False := by
    apply hw0
    apply cq8_nonreal_eigenvector (HodgeBlocks.derivationExt A.J n) s hs w
    let Φ := HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv (V := V) n
    apply Φ.injective
    rw [map_smul]
    simp only [Φ, LinearMap.baseChange_tmul,
      HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv_tmul,
      HodgeBlocks.complexifyWedge_derivationExt]
    exact he
  constructor
  · intro hx0
    have he := hside (-HodgeBlocks.WeilAction.omegaC d) y hy
    have hw' : HodgeBlocks.complexifyWedge n w = y := by
      simpa only [hx0, zero_add] using hxy
    refine hrat ((n : ℂ) * (-HodgeBlocks.WeilAction.omegaC d)) ?_ ?_
    · simpa only [map_mul, map_neg, HodgeBlocks.WeilAction.conj_omegaC,
        map_natCast, neg_neg, mul_neg] using hne
    · rw [hw']; exact he
  · intro hy0
    have he := hside (HodgeBlocks.WeilAction.omegaC d) x hx
    have hw' : HodgeBlocks.complexifyWedge n w = x := by
      simpa only [hy0, add_zero] using hxy
    refine hrat ((n : ℂ) * HodgeBlocks.WeilAction.omegaC d) ?_ ?_
    · simpa only [map_mul, HodgeBlocks.WeilAction.conj_omegaC,
        map_natCast, mul_neg] using hne.symm
    · rw [hw']; exact he

end Descent

section Rank

variable {X : Over (Spec ↧ℂ)} [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
  {μc : CupProduct X} [GrpObj X]

theorem cq8_weilClassOf_finrank_aux (hF : FiniteBetti X) (hB : BettiDeRhamIso X)
    (hD : HodgeDecomposition X) (hT : TorusCohomology μc) {d : ℚ} (hd : 0 < d)
    (A : letI := hT.finite
      HodgeBlocks.WeilAction (abelianVarietyCohomologyOf hF hB hD hT).weight1 d)
    (hW : letI := hT.finite; A.IsWeilType) (hX : 0 < TopologicalSpace.dim X.left) :
    letI := hT.finite
    Module.finrank ℚ ↥(weilClassOf hF hB hD hT A hW) = 2 := by
  let := hT.finite
  have hdim := two_mul_finrank_vs_inf_h10_eq hF hB hD hT hd A hW
  have hk : 1 ≤ Module.finrank ℂ
      ↥(A.Vs ⊓ (abelianVarietyCohomologyOf hF hB hD hT).weight1.H (1, 0)) := by
    omega
  have hr := A.finrank_weilClasses_eq_two
    (h10_sup_h01_eq_top hF hB hD hT) hW hd hk
  unfold weilClassOf
  calc
    _ = Module.finrank ℚ ↥(A.weilClasses (h10_sup_h01_eq_top hF hB hD hT) hW) := by
      apply LinearEquiv.finrank_eq
      apply (Submodule.equivMapOfInjective _ ?_ _).symm
      exact (HQ.castEquiv X (two_mul _).symm).injective.comp (hT.bijective _).injective
    _ = 2 := hr

end Rank

section Surface

variable (E : Over (Spec ↧ℂ)) [GrpObj E] [IsCommMonObj E] [IsIntegral E.left] [Smooth E.hom]
  [IsProjective E.hom]

theorem cq8_surfaceEnd2_Vs_aux (hE : TopologicalSpace.dim E.left = 1) (ρ : E ⟶ E) [IsMonHom ρ]
    (hρ : 𝟙 E * ρ * (ρ ≫ ρ) = 1)
    (W : letI := (finiteBetti_abelian (E ⊗ E)).finite 1
      HodgeBlocks.WeilAction (abelianWeightOneHodgeStructure (E ⊗ E)) 3)
    (hJ : W.J = cp_weilOperator (E ⊗ E) (cp_conjAut E ρ)) :
    letI := (finiteBetti_abelian (E ⊗ E)).finite 1
    ∀ x ∈ LinearMap.range (exteriorPower.map 2 W.Vs.subtype),
      exteriorPower.map 2 ((homPullback (cq8_surfaceEnd2 E ρ) 1).baseChange ℂ) x =
        (1 + cp_zeta) ^ 2 • x := by
  letI := (finiteBetti_abelian E).finite 1
  letI := (finiteBetti_abelian (E ⊗ E)).finite 1
  have hr := cq8_curve_ranks E hE ρ hρ
  have hc : ((1 + HodgeBlocks.WeilAction.omegaC (3 : ℚ)) / 2) =
      1 + cp_zeta := by
    simp only [HodgeBlocks.WeilAction.omegaC, cp_zeta]
    norm_num
    ring
  have hh := cq8_surface_square E ρ hρ W hJ
    (HodgeBlocks.WeilAction.omegaC 3) hr.1.le hr.2.le
  intro x hx
  have hhx := hh x hx
  rw [hc] at hhx
  exact hhx

theorem cq8_surfaceEnd2_Vsbar_aux (hE : TopologicalSpace.dim E.left = 1) (ρ : E ⟶ E)
    [IsMonHom ρ] (hρ : 𝟙 E * ρ * (ρ ≫ ρ) = 1)
    (W : letI := (finiteBetti_abelian (E ⊗ E)).finite 1
      HodgeBlocks.WeilAction (abelianWeightOneHodgeStructure (E ⊗ E)) 3)
    (hJ : W.J = cp_weilOperator (E ⊗ E) (cp_conjAut E ρ)) :
    letI := (finiteBetti_abelian (E ⊗ E)).finite 1
    ∀ x ∈ LinearMap.range (exteriorPower.map 2 W.Vsbar.subtype),
      exteriorPower.map 2 ((homPullback (cq8_surfaceEnd2 E ρ) 1).baseChange ℂ) x =
        conj ((1 + cp_zeta) ^ 2) • x := by
  letI := (finiteBetti_abelian E).finite 1
  letI := (finiteBetti_abelian (E ⊗ E)).finite 1
  have hr := cq8_curve_ranks E hE ρ hρ
  have hc : ((1 + -HodgeBlocks.WeilAction.omegaC (3 : ℚ)) / 2) =
      conj (1 + cp_zeta) := by
    have hh : ((1 + HodgeBlocks.WeilAction.omegaC (3 : ℚ)) / 2) =
        1 + cp_zeta := by
      simp only [HodgeBlocks.WeilAction.omegaC, cp_zeta]
      norm_num
      ring
    have hh' := congrArg conj hh
    simpa only [map_div₀, map_add, map_one, map_ofNat,
      HodgeBlocks.WeilAction.conj_omegaC] using hh'
  have hp : Module.finrank ℂ (Module.End.eigenspace
      ((cp_weilOperator E ρ).baseChange ℂ) (- -HodgeBlocks.WeilAction.omegaC 3)) ≤ 1 := by
    rw [neg_neg]
    exact hr.1.le
  have hh := cq8_surface_square E ρ hρ W hJ
    (-HodgeBlocks.WeilAction.omegaC 3) hr.2.le hp
  intro x hx
  have hhx := hh x hx
  rw [hc, ← map_pow] at hhx
  exact hhx

theorem cq8_surfaceEnd2_weilClassOf_aux (hE : TopologicalSpace.dim E.left = 1) (ρ : E ⟶ E)
    [IsMonHom ρ] (hρ : 𝟙 E * ρ * (ρ ≫ ρ) = 1)
    (W : letI := (finiteBetti_abelian (E ⊗ E)).finite 1
      HodgeBlocks.WeilAction (abelianWeightOneHodgeStructure (E ⊗ E)) 3)
    (hJ : W.J = cp_weilOperator (E ⊗ E) (cp_conjAut E ρ))
    (hW : letI := (finiteBetti_abelian (E ⊗ E)).finite 1; W.IsWeilType) :
    letI := (finiteBetti_abelian (E ⊗ E)).finite 1
    (weilClassOf (finiteBetti_abelian (E ⊗ E)) (spec_bettiDeRhamIso_abelian (E ⊗ E))
        (hodgeDecomposition_of_abelian (E ⊗ E)) (torusCohomology_cupProductOf (E ⊗ E))
        W hW).map (homPullback (cq8_surfaceEnd2 E ρ) _) ≤
      weilClassOf (finiteBetti_abelian (E ⊗ E)) (spec_bettiDeRhamIso_abelian (E ⊗ E))
        (hodgeDecomposition_of_abelian (E ⊗ E)) (torusCohomology_cupProductOf (E ⊗ E)) W hW := by
  letI := (finiteBetti_abelian (E ⊗ E)).finite 1
  exact cq8_weilClassOf_invariant
    (finiteBetti_abelian (E ⊗ E)) (spec_bettiDeRhamIso_abelian (E ⊗ E))
    (hodgeDecomposition_of_abelian (E ⊗ E)) (torusCohomology_cupProductOf (E ⊗ E))
    W hW (cq8_surfaceEnd2 E ρ)
    (cq8_surface_preserves_eigenspace E ρ hρ W hJ _)
    (cq8_surface_preserves_eigenspace E ρ hρ W hJ _)

end Surface

section ScalarExtension

variable (A Y : Over (Spec ↧ℂ))
  [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
  [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]

theorem cq8_crossC_normalization_aux (I : HQ Y 4 →ₗ[ℚ] ℚ) (P : HQ (A ⊗ Y) 10 →ₗ[ℚ] HQ A 6)
    (h : ∀ (a : HQ A 6) (b : HQ Y 4), P (cq8_cross A Y 6 4 a b) = I b • a)
    (a : ℂ ⊗[ℚ] HQ A 6) (b : ℂ ⊗[ℚ] HQ Y 4) :
    P.baseChange ℂ (cq8_crossC A Y 6 4 a b) = cq8_scalarC I b • a := by
  induction a using TensorProduct.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply, smul_zero]
  | tmul z a =>
    induction b using TensorProduct.induction_on with
    | zero => simp only [map_zero, smul_zero, zero_smul]
    | tmul w b =>
      simp only [cq8_crossC, LinearMap.compl₁₂_apply,
        LinearMap.baseChange_tmul, CupProduct.cupC_tmul]
      change (z * w) ⊗ₜ[ℚ] P (cq8_cross A Y 6 4 a b) =
        cq8_scalarC I (w ⊗ₜ[ℚ] b) • (z ⊗ₜ[ℚ] a)
      rw [h]
      simp [cq8_scalarC, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
        Algebra.smul_def, mul_assoc, mul_comm, mul_left_comm]
    | add b c hb hc =>
      simp only [map_add, smul_add, add_smul, hb, hc]
  | add a c ha hc =>
    simp only [map_add, LinearMap.add_apply, smul_add, ha, hc]

theorem cq8_crossC_vanishing_aux {U : Type*} [AddCommGroup U] [Module ℚ U] {n : ℕ}
    (i j : ℕ) (hij : i + j = n) (P : HQ (A ⊗ Y) n →ₗ[ℚ] U)
    (h : ∀ (a : HQ A i) (b : HQ Y j),
      P (HQ.castEquiv (A ⊗ Y) hij (cq8_cross A Y i j a b)) = 0)
    (a : ℂ ⊗[ℚ] HQ A i) (b : ℂ ⊗[ℚ] HQ Y j) :
    P.baseChange ℂ ((HQ.castEquiv (A ⊗ Y) hij).toLinearMap.baseChange ℂ
      (cq8_crossC A Y i j a b)) = 0 := by
  induction a using TensorProduct.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | tmul z a =>
    induction b using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul w b =>
      simp only [cq8_crossC, LinearMap.compl₁₂_apply, LinearMap.baseChange_tmul,
        CupProduct.cupC_tmul]
      change (z * w) ⊗ₜ[ℚ] P (HQ.castEquiv (A ⊗ Y) hij (cq8_cross A Y i j a b)) = 0
      rw [h, TensorProduct.tmul_zero]
    | add b c hb hc => simp only [map_add, hb, hc, add_zero]
  | add a c ha hc =>
    simp only [map_add, LinearMap.add_apply, ha, hc, add_zero]

end ScalarExtension

end HodgeLean.Foundations.Program
