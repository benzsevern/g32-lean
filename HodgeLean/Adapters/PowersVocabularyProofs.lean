import HodgeLean.Foundations.PowersVocabularyDefs
import HodgeLean.Foundations.EQWCore
import HodgeLean.Adapters.F1575PowersFix

/-! # Proofs for the PW-0 vocabulary spec

The agent's working file. Fill every proof hole. **Do not change the statement of
any `_aux` theorem**: `PowersVocabulary.lean` (frozen) restates each one and must still typecheck.
Helper lemmas may be added freely, in this file or in new files.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
attribute [local instance 100] LieRing.ofAssociativeRing
open CategoryTheory AlgebraicGeometry ComplexPoint
open scoped TensorProduct
namespace HodgeLean.Adapters
open RealDefs Foundations Foundations.WeilPower Foundations.Symplectic InvariantsExterior

section Algebra

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- Spec S1. -/
theorem spec_pw0_gkLie_adjoin_eq_aux (E : LinearMap.BilinForm ℚ V) (J : Module.End ℚ V) :
    gkLie E (Algebra.adjoin ℚ {J}) J = weilSU E J := by
  ext X
  refine ⟨fun h => h.1, fun h => ⟨h, fun r hr => ?_⟩⟩
  have hle : Algebra.adjoin ℚ {J} ≤ Subalgebra.centralizer ℚ {X} := by
    rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff, SetLike.mem_coe,
      Subalgebra.mem_centralizer_iff]
    rintro g rfl
    exact h.1
  exact (Subalgebra.mem_centralizer_iff ℚ).mp (hle hr) X rfl

/-- Spec S4. -/
theorem spec_pw0_cmPowerPullback_adjoin_aux (J : Module.End ℚ V) {m : ℕ} (r s : Fin m → ℚ) :
    cmPowerPullback (Algebra.adjoin ℚ {J})
        (fun i => algebraMap ℚ (Algebra.adjoin ℚ {J}) (r i) +
          s i • ⟨J, Algebra.self_mem_adjoin_singleton ℚ J⟩) =
      weilPowerPullback J r s := by
  ext x
  simp only [cmPowerPullback, weilPowerPullback, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.sum_apply, LinearMap.add_apply, LinearMap.flip_apply, TensorProduct.mk_apply,
    Subalgebra.coe_add, Subalgebra.coe_smul, Subalgebra.coe_algebraMap, Module.algebraMap_end_apply,
    LinearMap.smul_apply, TensorProduct.add_tmul, Finset.sum_add_distrib]
  have key : ∀ (y : V) (t : Fin m → ℚ),
      ∑ i, (t i • y) ⊗ₜ[ℚ] (Pi.single i 1 : Fin m → ℚ) = y ⊗ₜ[ℚ] t := by
    intro y t
    simp_rw [TensorProduct.smul_tmul, ← TensorProduct.tmul_sum]
    congr 1
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [key, key]

/-- Under `J² = -d`, every element of `ℚ[J]` has the form `r + s J`. -/
private theorem adjoin_quadratic_eq (J : Module.End ℚ V) {d : ℚ}
    (hJ : J.comp J = (-d) • LinearMap.id) (x : Module.End ℚ V)
    (hx : x ∈ Algebra.adjoin ℚ {J}) : ∃ r s : ℚ, x = r • (1 : Module.End ℚ V) + s • J := by
  have hJv : ∀ v, J (J v) = (-d) • v := fun v => LinearMap.congr_fun hJ v
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    exact ⟨0, 1, by rw [hx, zero_smul, one_smul, zero_add]⟩
  | algebraMap c => exact ⟨c, 0, by rw [zero_smul, add_zero, Algebra.algebraMap_eq_smul_one]⟩
  | add x y _ _ hx hy =>
    obtain ⟨r₁, s₁, rfl⟩ := hx
    obtain ⟨r₂, s₂, rfl⟩ := hy
    exact ⟨r₁ + r₂, s₁ + s₂, by module⟩
  | mul x y _ _ hx hy =>
    obtain ⟨r₁, s₁, rfl⟩ := hx
    obtain ⟨r₂, s₂, rfl⟩ := hy
    refine ⟨r₁ * r₂ - d * s₁ * s₂, r₁ * s₂ + s₁ * r₂, ?_⟩
    ext v
    simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply,
      Module.End.one_apply, map_add, map_smul, hJv]
    module

/-- Under `J² = -d`, the two closure predicates agree. -/
private theorem isCMPowerClosed_adjoin_iff (J : Module.End ℚ V) {d : ℚ}
    (hJ : J.comp J = (-d) • LinearMap.id) {m n : ℕ}
    (D : Submodule ℚ (⋀[ℚ]^2 (V ⊗[ℚ] (Fin m → ℚ)))) (W : Submodule ℚ (⋀[ℚ]^n V))
    (F : ∀ k, Submodule ℚ (⋀[ℚ]^k (V ⊗[ℚ] (Fin m → ℚ)))) :
    IsCMPowerClosed (Algebra.adjoin ℚ {J}) D W F ↔ IsDivisorPulledWeilClosed J D W F := by
  constructor
  · intro hF
    refine ⟨hF.unit_mem, hF.divisor_le, fun r s w hw => ?_, hF.wedge_mem⟩
    rw [← spec_pw0_cmPowerPullback_adjoin_aux J r s]
    exact hF.pullback_mem _ w hw
  · intro hF
    refine ⟨hF.unit_mem, hF.divisor_le, fun a w hw => ?_, hF.wedge_mem⟩
    choose r s hrs using fun i => adjoin_quadratic_eq J hJ (a i) (a i).2
    have ha : a = fun i => algebraMap ℚ (Algebra.adjoin ℚ {J}) (r i) +
        s i • ⟨J, Algebra.self_mem_adjoin_singleton ℚ J⟩ := by
      funext i
      apply Subtype.ext
      rw [hrs i, Subalgebra.coe_add, Subalgebra.coe_smul, Subalgebra.coe_algebraMap,
        Algebra.algebraMap_eq_smul_one]
    rw [ha, spec_pw0_cmPowerPullback_adjoin_aux J r s]
    exact hF.pullback_mem r s w hw

/-- Spec S5. -/
theorem spec_pw0_cmPowerSpan_adjoin_eq_aux (J : Module.End ℚ V) {d : ℚ}
    (hJ : J.comp J = (-d) • LinearMap.id) {m n : ℕ}
    (D : Submodule ℚ (⋀[ℚ]^2 (V ⊗[ℚ] (Fin m → ℚ)))) (W : Submodule ℚ (⋀[ℚ]^n V)) (k : ℕ) :
    cmPowerSpan (Algebra.adjoin ℚ {J}) D W k = divisorPulledWeilSpan J D W k := by
  simp only [cmPowerSpan, divisorPulledWeilSpan, isCMPowerClosed_adjoin_iff J hJ]

variable [FiniteDimensional ℚ V]

/-- Spec S2. -/
theorem spec_pw0_hodgeLieIsGk_adjoin_iff_aux (H : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℚ] V))
    (hH : DirectSum.IsInternal H) (E : LinearMap.BilinForm ℚ V) (hE : E.Nondegenerate)
    (hAlt : E.IsAlt) (J : Module.End ℚ V) (hJ : J.comp J = (-3 : ℚ) • LinearMap.id)
    (hskew : ∀ x y, E (J x) y = -E x (J y)) :
    HodgeLieIsGk H hH E (Algebra.adjoin ℚ {J}) J ↔
      complexSpan (hodgeLieAlgebra H hH).toSubmodule =
        (complexSU E hE J hJ hskew).toSubmodule := by
  rw [HodgeLieIsGk, spec_pw0_gkLie_adjoin_eq_aux,
    spec_eqw_complexSpan_weilSU_eq_complexSU E hE hAlt J hJ hskew]

omit [FiniteDimensional ℚ V] in
private theorem pw0_exteriorComplexify_map {U : Type*} [AddCommGroup U] [Module ℚ U] (k : ℕ)
    (f : U →ₗ[ℚ] V) :
    (exteriorComplexify k).comp (exteriorPower.map k f) =
      ((exteriorPower.map k (f.baseChange ℂ)).restrictScalars ℚ).comp (exteriorComplexify k) := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro x
  simp [LinearMap.compAlternatingMap_apply, exteriorComplexify_ιMulti,
    exteriorPower.map_apply_ιMulti]
  congr 1

omit [FiniteDimensional ℚ V] in
/-- A pullback `x ↦ g x ⊗ u` intertwines `G` with its power action when `g` commutes with `G`. -/
private theorem pw0_pullback_commutes_power_grading (g : Module.End ℚ V)
    (G : Module.End ℂ (ℂ ⊗[ℚ] V)) (hGg : G.comp (g.baseChange ℂ) = (g.baseChange ℂ).comp G)
    {m : ℕ} (r s : Fin m → ℚ) :
    (powerAction m G).comp ((weilPowerPullback g r s).baseChange ℂ) =
      ((weilPowerPullback g r s).baseChange ℂ).comp G := by
  apply LinearMap.ext
  intro z
  apply (powerBaseChange m).injective
  simp [LinearMap.comp_apply, powerAction]
  rw [powerBaseChange_pullback]
  rw [map_add, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, powerBaseChange_pullback]
  exact congrArg (fun x => G z ⊗ₜ[ℂ] multiplicityEquiv m (1 ⊗ₜ[ℚ] r) + x)
    (congrArg (fun x => x ⊗ₜ[ℂ] multiplicityEquiv m (1 ⊗ₜ[ℚ] s))
      (by simpa [LinearMap.comp_apply] using LinearMap.congr_fun hGg z))

omit [FiniteDimensional ℚ V] in
/-- `cmPowerPullback R a` intertwines the grading with its power action when every `a i` commutes
with it. -/
private theorem pw0_cmPowerPullback_commutes (R : Subalgebra ℚ (Module.End ℚ V)) {m : ℕ}
    (a : Fin m → R) (G : Module.End ℂ (ℂ ⊗[ℚ] V))
    (hG : ∀ i, G.comp ((a i : Module.End ℚ V).baseChange ℂ) =
      ((a i : Module.End ℚ V).baseChange ℂ).comp G) :
    (powerAction m G).comp ((cmPowerPullback R a).baseChange ℂ) =
      ((cmPowerPullback R a).baseChange ℂ).comp G := by
  have hsplit : cmPowerPullback R a =
      ∑ i, weilPowerPullback (a i : Module.End ℚ V) 0 (Pi.single i 1) := by
    ext x
    simp [cmPowerPullback, weilPowerPullback]
  rw [hsplit]
  induction (Finset.univ : Finset (Fin m)) using Finset.induction_on with
  | empty => simp [LinearMap.baseChange_zero]
  | insert i t hi ih =>
    rw [Finset.sum_insert hi, LinearMap.baseChange_add, LinearMap.comp_add, LinearMap.add_comp,
      ih, pw0_pullback_commutes_power_grading _ G (hG i)]

set_option linter.unusedSectionVars false in
/-- Spec S6. -/
theorem spec_pw0_cmPowerSpan_le_rationalExteriorHodge_aux
    (H : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)) (hH : DirectSum.IsInternal H)
    (R : Subalgebra ℚ (Module.End ℚ V))
    (hR : ∀ r ∈ R, ∀ pq, ∀ x ∈ H pq, (r : Module.End ℚ V).baseChange ℂ x ∈ H pq)
    {n : ℕ} (W : Submodule ℚ (⋀[ℚ]^n V))
    (hW : ∀ w ∈ W, exteriorDer n (gradingOperator H hH) (exteriorComplexify n w) = 0)
    (m k : ℕ) :
    cmPowerSpan R (rationalExteriorHodge H hH m 2) W k ≤ rationalExteriorHodge H hH m k := by
  refine iInf₂_le (rationalExteriorHodge H hH m) ⟨?_, le_rfl, ?_, ?_⟩
  · change exteriorDer 0 (powerAction m (gradingOperator H hH))
      (exteriorComplexify 0 (exteriorPower.ιMulti ℚ 0 Fin.elim0)) = 0
    simp [exteriorDer_ιMulti]
  · intro a w hw
    have hG : ∀ i, (gradingOperator H hH).comp ((a i : Module.End ℚ V).baseChange ℂ) =
        ((a i : Module.End ℚ V).baseChange ℂ).comp (gradingOperator H hH) := by
      intro i
      apply linearMap_ext_of_isInternal hH
      intro pq x hx
      have hxa := hR (a i) (a i).2 pq x hx
      rw [LinearMap.comp_apply, gradingOperator_apply_of_mem H hH hxa,
        LinearMap.comp_apply, gradingOperator_apply_of_mem H hH hx, map_smul]
    change exteriorDer n (powerAction m (gradingOperator H hH))
      (exteriorComplexify n (exteriorPower.map n (cmPowerPullback R a) w)) = 0
    have hm := LinearMap.congr_fun (pw0_exteriorComplexify_map n (cmPowerPullback R a)) w
    change exteriorComplexify n (exteriorPower.map n (cmPowerPullback R a) w) = _ at hm
    rw [hm]
    change exteriorDer n (powerAction m (gradingOperator H hH))
      (exteriorPower.map n ((cmPowerPullback R a).baseChange ℂ) (exteriorComplexify n w)) = 0
    rw [exteriorDer_map _ _ _ _ (pw0_cmPowerPullback_commutes R a _ hG), hW w hw, map_zero]
  · intro i j v w hv hw
    change exteriorDer (i + j) (powerAction m (gradingOperator H hH))
      (exteriorComplexify (i + j) (exteriorPower.wedge ℚ _ i j v w)) = 0
    rw [exteriorComplexify_wedge, exteriorDer_wedge]
    change exteriorDer i (powerAction m (gradingOperator H hH)) (exteriorComplexify i v) = 0 at hv
    change exteriorDer j (powerAction m (gradingOperator H hH)) (exteriorComplexify j w) = 0 at hw
    rw [hv, hw, map_zero, LinearMap.zero_apply, map_zero, add_zero]

end Algebra

section Weil

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
  {M : HodgeBlocks.QHodgeStructure 1 V}

omit [FiniteDimensional ℚ V] in
/-- An endomorphism with range in `N` that acts on `N` as the scalar `c` has trace
`c · dim N`. -/
private theorem pw0b_trace_eq_of_range_le {U : Type*} [AddCommGroup U] [Module ℂ U]
    [Module.Finite ℂ U] (T : Module.End ℂ U) (N : Submodule ℂ U) (c : ℂ)
    (hT : ∀ x, T x ∈ N) (hc : ∀ x ∈ N, T x = c • x) :
    LinearMap.trace ℂ U T = c * Module.finrank ℂ N := by
  have h1 : T = N.subtype ∘ₗ T.codRestrict N hT := by
    ext x
    rfl
  have h2 : T.codRestrict N hT ∘ₗ N.subtype = c • LinearMap.id := by
    ext x
    simp [hc x x.2]
  rw [h1, LinearMap.trace_comp_comm', h2, map_smul, LinearMap.trace_id, smul_eq_mul]

/-- Spec S3. -/
theorem isWeilType_of_hodgeLieIsGk_aux {d : ℚ} (hd : 0 < d) (A : HodgeBlocks.WeilAction M d)
    (hTop : M.H (1, 0) ⊔ M.H (0, 1) = ⊤) (E : LinearMap.BilinForm ℚ V)
    (R : Subalgebra ℚ (Module.End ℚ V)) (hGk : HodgeLieIsGk M.H M.isInternal E R A.J) :
    A.IsWeilType := by
  let C := gradingOperator M.H M.isInternal
  let Jc := A.J.baseChange ℂ
  let ω := HodgeBlocks.WeilAction.omegaC d
  have hω2 : ω ^ 2 = -(d : ℂ) := HodgeBlocks.WeilAction.omegaC_sq hd
  have hω0 : ω ≠ 0 := HodgeBlocks.WeilAction.omegaC_ne_zero hd
  -- the trace conditions on the grading operator
  have hC : C ∈ complexSpan (weilSU E A.J).toSubmodule := by
    have h1 : C ∈ complexSpan (hodgeLieAlgebra M.H M.isInternal).toSubmodule :=
      gradingOperator_mem_span_hodgeLieAlgebra M.H M.isInternal
    rw [show complexSpan (hodgeLieAlgebra M.H M.isInternal).toSubmodule = _ from hGk] at h1
    exact Submodule.span_mono (Set.image_mono fun X hX => hX.1) h1
  obtain ⟨-, -, htrC, htrJC⟩ := (spec_eqw_mem_complexSpan_weilSU_iff E A.J C).mp hC
  -- elementary identities
  have hJ2 : ∀ x, Jc (Jc x) = (-(d : ℂ)) • x := by
    intro x
    have h := LinearMap.congr_fun (congrArg (LinearMap.baseChange ℂ) A.J_sq) x
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_smul, LinearMap.baseChange_id] at h
    rw [← LinearMap.comp_apply]
    change (A.J.baseChange ℂ).comp (A.J.baseChange ℂ) x = _
    rw [h, LinearMap.smul_apply, LinearMap.id_apply, ← algebraMap_smul ℂ (-d) x]
    simp
  have hC10 : ∀ x ∈ M.H (1, 0), C x = Complex.I • x := by
    intro x hx
    rw [gradingOperator_apply_of_mem M.H M.isInternal hx]
    simp
  have hC01 : ∀ x ∈ M.H (0, 1), C x = (-Complex.I) • x := by
    intro x hx
    rw [gradingOperator_apply_of_mem M.H M.isInternal hx]
    simp
  have hCi : ∀ x, C x + Complex.I • x ∈ M.H (1, 0) := by
    intro x
    have hx : x ∈ M.H (1, 0) ⊔ M.H (0, 1) := hTop ▸ Submodule.mem_top
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add, hC10 a ha, hC01 b hb]
    have : Complex.I • a + (-Complex.I) • b + Complex.I • (a + b) = (2 * Complex.I) • a := by
      module
    rw [this]
    exact (M.H (1, 0)).smul_mem _ ha
  have hJH : ∀ x ∈ M.H (1, 0), Jc x ∈ M.H (1, 0) := fun x hx => A.preserves (1, 0) ⟨x, hx, rfl⟩
  have hVs : ∀ x, Jc x + ω • x ∈ A.Vs := by
    intro x
    change _ ∈ Module.End.eigenspace A.Jc ω
    rw [Module.End.mem_eigenspace_iff]
    change Jc (Jc x + ω • x) = ω • (Jc x + ω • x)
    rw [map_add, map_smul, hJ2, smul_add, smul_smul, ← pow_two, hω2, add_comm]
  have hVsbar : ∀ x, Jc x - ω • x ∈ A.Vsbar := by
    intro x
    change _ ∈ Module.End.eigenspace A.Jc (-ω)
    rw [Module.End.mem_eigenspace_iff]
    change Jc (Jc x - ω • x) = (-ω) • (Jc x - ω • x)
    rw [map_sub, map_smul, hJ2, smul_sub, smul_smul]
    have : (-ω * ω) = -(ω ^ 2) := by ring
    rw [this, hω2]
    module
  have hJVs : ∀ x ∈ A.Vs, Jc x = ω • x := fun x hx => Module.End.mem_eigenspace_iff.mp hx
  have hJVsbar : ∀ x ∈ A.Vsbar, Jc x = (-ω) • x := fun x hx => Module.End.mem_eigenspace_iff.mp hx
  -- three trace computations
  have t1 : LinearMap.trace ℂ _ (Jc + ω • 1) = (2 * ω) * Module.finrank ℂ A.Vs :=
    pw0b_trace_eq_of_range_le _ A.Vs _ (fun x => hVs x) (fun x hx => by
      change Jc x + ω • x = _
      rw [hJVs x hx]
      module)
  have t2 : LinearMap.trace ℂ _ (Jc - ω • 1) = (-2 * ω) * Module.finrank ℂ A.Vsbar :=
    pw0b_trace_eq_of_range_le _ A.Vsbar _ (fun x => hVsbar x) (fun x hx => by
      change Jc x - ω • x = _
      rw [hJVsbar x hx]
      module)
  have t3 : LinearMap.trace ℂ _ (Jc * C + Complex.I • Jc + ω • C + (Complex.I * ω) • 1) =
      (4 * Complex.I * ω) * Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)) := by
    apply pw0b_trace_eq_of_range_le _ (A.Vs ⊓ M.H (1, 0))
    · intro x
      have he : (Jc * C + Complex.I • Jc + ω • C + (Complex.I * ω) • 1) x =
          Jc (C x + Complex.I • x) + ω • (C x + Complex.I • x) := by
        simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.mul_apply,
          Module.End.one_apply, map_add, map_smul]
        module
      rw [he]
      exact ⟨hVs _, (M.H (1, 0)).add_mem (hJH _ (hCi x)) ((M.H (1, 0)).smul_mem _ (hCi x))⟩
    · intro x hx
      simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.mul_apply,
        Module.End.one_apply]
      rw [hC10 x hx.2, map_smul, hJVs x hx.1]
      module
  rw [map_add, map_smul, LinearMap.trace_one] at t1
  rw [map_sub, map_smul, LinearMap.trace_one, A.finrank_Vsbar_eq_Vs] at t2
  rw [map_add, map_add, map_add, map_smul, map_smul, map_smul, LinearMap.trace_one,
    LinearMap.trace_mul_comm, htrC] at t3
  change LinearMap.trace ℂ _ (Jc * C) = 0 at htrJC
  rw [LinearMap.trace_mul_comm] at htrJC
  rw [htrJC] at t3
  set n : ℂ := (Module.finrank ℂ (ℂ ⊗[ℚ] V) : ℂ)
  set v : ℂ := (Module.finrank ℂ A.Vs : ℂ)
  set p : ℂ := (Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)) : ℂ)
  simp only [smul_eq_mul] at t1 t2 t3
  have hn : ω * (n - 2 * v) = 0 := by linear_combination (t1 - t2) / 2
  have htJ : LinearMap.trace ℂ _ Jc = 0 := by linear_combination (t1 + t2) / 2
  rw [htJ] at t3
  have hp : (Complex.I * ω) * (n - 4 * p) = 0 := by linear_combination t3
  have h1 := (mul_eq_zero.mp hn).resolve_left hω0
  have h2 := (mul_eq_zero.mp hp).resolve_left (mul_ne_zero Complex.I_ne_zero hω0)
  have h3 : (2 * Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)) : ℂ) = Module.finrank ℂ A.Vs := by
    linear_combination (h1 - h2) / 2
  unfold HodgeBlocks.WeilAction.IsWeilType
  exact_mod_cast h3

omit [FiniteDimensional ℚ V] in
private theorem pw0b_exteriorHodge_grading_zero (H : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℚ] V))
    (hH : DirectSum.IsInternal H) (m k : ℕ) (p : ℤ)
    (v : ⋀[ℂ]^k (ℂ ⊗[ℚ] (V ⊗[ℚ] (Fin m → ℚ))))
    (hv : v ∈ exteriorHodge H m k (p, p)) :
    exteriorDer k (powerAction m (gradingOperator H hH)) v = 0 := by
  have h := exteriorHodge_le_eigenspace H hH m k (p, p) hv
  rw [Module.End.mem_eigenspace_iff] at h
  simpa using h

omit [FiniteDimensional ℚ V] in
private theorem pw0b_f1575SingleCopyComplex_commutes (G : Module.End ℂ (ℂ ⊗[ℚ] V)) :
    G.comp (f1575SingleCopyComplex (V := V)).toLinearMap =
      (f1575SingleCopyComplex (V := V)).toLinearMap.comp (powerAction 1 G) := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul a v =>
    induction v using TensorProduct.inductionOn with
    | tmul x u => simp [f1575SingleCopyComplex, powerAction, powerBaseChange]
    | add x y hx hy => simpa only [TensorProduct.tmul_add, map_add] using congrArg₂ (· + ·) hx hy
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

/-- Spec S7. -/
theorem spec_pw0_weilClasses_grading_aux {d : ℚ} (A : HodgeBlocks.WeilAction M d)
    (hTop : M.H (1, 0) ⊔ M.H (0, 1) = ⊤) (hW : A.IsWeilType) :
    ∀ w ∈ A.weilClasses hTop hW,
      exteriorDer _ (gradingOperator M.H M.isInternal) (exteriorComplexify _ w) = 0 := by
  intro w hw
  let q := Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0))
  have hwH := A.isHodgeClass_of_mem_weilClasses hTop hW hw
  have hw' : (1 : ℂ) ⊗ₜ[ℚ] w ∈ (M.exteriorPower (V := V) (q + q)).H (q, q) := by
    simpa [q, HodgeBlocks.IsHodgeClass, HodgeBlocks.WeilAction.weightCast_H] using hwH
  have hwsrc : (f1575SingleCopyExterior (V := V) (q + q)).symm
      ((1 : ℂ) ⊗ₜ[ℚ] w) ∈ exteriorHodge M.H 1 (q + q) (q, q) := by
    change (1 : ℂ) ⊗ₜ[ℚ] w ∈ M.exteriorPowerH (V := V) (q + q) (q, q) at hw'
    rw [← f1575SingleCopyExterior_map_hodge] at hw'
    rw [Submodule.mem_map_equiv] at hw'
    exact hw'
  have hzsrc := pw0b_exteriorHodge_grading_zero M.H M.isInternal 1 (q + q) (q : ℤ) _ hwsrc
  let e := f1575SingleCopyExterior (V := V) (q + q)
  have he : exteriorPower.map (q + q) (f1575SingleCopyComplex (V := V)).toLinearMap
      (e.symm ((1 : ℂ) ⊗ₜ[ℚ] w)) = exteriorBaseChange (q + q) ((1 : ℂ) ⊗ₜ[ℚ] w) := by
    change (exteriorEquiv (q + q) (f1575SingleCopyComplex (V := V)))
      ((exteriorEquiv (q + q) (f1575SingleCopyComplex (V := V))).symm
        ((exteriorBaseChange (q + q)) ((1 : ℂ) ⊗ₜ[ℚ] w))) = _
    rw [LinearEquiv.apply_symm_apply]
  have hc : exteriorBaseChange (q + q) ((1 : ℂ) ⊗ₜ[ℚ] w) = exteriorComplexify (q + q) w := by
    change (exteriorBaseChange (q + q)).toLinearMap ((1 : ℂ) ⊗ₜ[ℚ] w) = _
    rw [exteriorBaseChange_eq_lift, LinearMap.liftBaseChange_tmul, one_smul]
  change exteriorDer (q + q) (gradingOperator M.H M.isInternal) (exteriorComplexify (q + q) w) = 0
  rw [← hc, ← he, exteriorDer_map _ _ _ _ (pw0b_f1575SingleCopyComplex_commutes
    (gradingOperator M.H M.isInternal)), hzsrc, map_zero]

omit [FiniteDimensional ℚ V] in
private theorem pw0b_rationalExteriorHodge_wedge (H : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℚ] V))
    (hH : DirectSum.IsInternal H) (m i j : ℕ)
    (v : ⋀[ℚ]^i (V ⊗[ℚ] (Fin m → ℚ)))
    (w : ⋀[ℚ]^j (V ⊗[ℚ] (Fin m → ℚ)))
    (hv : v ∈ rationalExteriorHodge H hH m i)
    (hw : w ∈ rationalExteriorHodge H hH m j) :
    exteriorPower.wedge ℚ _ i j v w ∈ rationalExteriorHodge H hH m (i + j) := by
  change exteriorDer (i + j) (powerAction m (gradingOperator H hH))
    (exteriorComplexify (i + j) (exteriorPower.wedge ℚ _ i j v w)) = 0
  rw [exteriorComplexify_wedge, exteriorDer_wedge]
  change exteriorDer i (powerAction m (gradingOperator H hH)) (exteriorComplexify i v) = 0 at hv
  change exteriorDer j (powerAction m (gradingOperator H hH)) (exteriorComplexify j w) = 0 at hw
  rw [hv, hw, map_zero, LinearMap.zero_apply, map_zero, add_zero]

private theorem pw0b_weilAction_commutes_grading {d : ℚ} (A : HodgeBlocks.WeilAction M d) :
    (gradingOperator M.H M.isInternal).comp (A.J.baseChange ℂ) =
      (A.J.baseChange ℂ).comp (gradingOperator M.H M.isInternal) := by
  apply linearMap_ext_of_isInternal M.isInternal
  intro pq x hx
  have hxJ : A.J.baseChange ℂ x ∈ M.H pq := A.preserves pq ⟨x, hx, rfl⟩
  rw [LinearMap.comp_apply, gradingOperator_apply_of_mem M.H M.isInternal hxJ,
    LinearMap.comp_apply, gradingOperator_apply_of_mem M.H M.isInternal hx, map_smul]

omit [FiniteDimensional ℚ V] in
private theorem pw0b_exteriorComplexify_map {U : Type*} [AddCommGroup U] [Module ℚ U]
    (k : ℕ) (f : U →ₗ[ℚ] V) :
    (exteriorComplexify k).comp (exteriorPower.map k f) =
      ((exteriorPower.map k (f.baseChange ℂ)).restrictScalars ℚ).comp (exteriorComplexify k) := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro x
  simp [LinearMap.compAlternatingMap_apply, exteriorComplexify_ιMulti,
    exteriorPower.map_apply_ιMulti]
  congr 1

omit [FiniteDimensional ℚ V] in
private theorem pw0b_pullback_commutes_power_grading (J : Module.End ℚ V)
    (G : Module.End ℂ (ℂ ⊗[ℚ] V)) (hGJ : G.comp (J.baseChange ℂ) =
      (J.baseChange ℂ).comp G) {m : ℕ} (r s : Fin m → ℚ) :
    (powerAction m G).comp ((weilPowerPullback J r s).baseChange ℂ) =
      ((weilPowerPullback J r s).baseChange ℂ).comp G := by
  apply LinearMap.ext
  intro z
  apply (powerBaseChange m).injective
  simp [LinearMap.comp_apply, powerAction]
  rw [powerBaseChange_pullback]
  rw [map_add, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, powerBaseChange_pullback]
  exact congrArg (fun x => G z ⊗ₜ[ℂ] multiplicityEquiv m (1 ⊗ₜ[ℚ] r) + x)
    (congrArg (fun x => x ⊗ₜ[ℂ] multiplicityEquiv m (1 ⊗ₜ[ℚ] s))
      (by simpa [LinearMap.comp_apply] using LinearMap.congr_fun hGJ z))

/-- The reverse inclusion of S8, rationally: every generator is a rational Hodge class. -/
private theorem pw0b_divisorPulledWeilSpan_le {d : ℚ} (A : HodgeBlocks.WeilAction M d)
    (hTop : M.H (1, 0) ⊔ M.H (0, 1) = ⊤) (hW : A.IsWeilType) (m k : ℕ) :
    divisorPulledWeilSpan A.J (rationalExteriorHodge M.H M.isInternal m 2)
        (A.weilClasses hTop hW) k ≤ rationalExteriorHodge M.H M.isInternal m k := by
  apply divisorPulledWeilSpan_le
  constructor
  · change exteriorDer 0 (powerAction m (gradingOperator M.H M.isInternal))
      (exteriorComplexify 0 (exteriorPower.ιMulti ℚ 0 Fin.elim0)) = 0
    simp [exteriorDer_ιMulti]
  · exact le_rfl
  · intro r s w hw
    have hzw := spec_pw0_weilClasses_grading_aux A hTop hW w hw
    change exteriorDer _ (powerAction m (gradingOperator M.H M.isInternal))
      (exteriorComplexify _ (exteriorPower.map _ (weilPowerPullback A.J r s) w)) = 0
    have hm := LinearMap.congr_fun (pw0b_exteriorComplexify_map _ (weilPowerPullback A.J r s)) w
    change exteriorComplexify _ (exteriorPower.map _ (weilPowerPullback A.J r s) w) = _ at hm
    rw [hm]
    change exteriorDer _ (powerAction m (gradingOperator M.H M.isInternal))
      (exteriorPower.map _ ((weilPowerPullback A.J r s).baseChange ℂ)
        (exteriorComplexify _ w)) = 0
    rw [exteriorDer_map _ _ _ _
      (pw0b_pullback_commutes_power_grading A.J _
        (pw0b_weilAction_commutes_grading A) r s), hzw, map_zero]
  · exact pw0b_rationalExteriorHodge_wedge M.H M.isInternal m

private theorem pw0b_vs_eq (A : HodgeBlocks.WeilAction M 3) :
    Module.End.eigenspace (A.J.baseChange ℂ) root = A.Vs := by
  simp [HodgeBlocks.WeilAction.Vs, HodgeBlocks.WeilAction.omegaC, root]

private theorem pw0b_middleDegree (A : HodgeBlocks.WeilAction M 3)
    (hTop : M.H (1, 0) ⊔ M.H (0, 1) = ⊤) (hW : A.IsWeilType) :
    Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)) + Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)) =
      Module.finrank ℂ (Module.End.eigenspace (A.J.baseChange ℂ) root) := by
  rw [pw0b_vs_eq, A.finrank_Vs_eq_twice_inf_H10 hTop hW]

private theorem pw0b_topLines (A : HodgeBlocks.WeilAction M 3)
    (hTop : M.H (1, 0) ⊔ M.H (0, 1) = ⊤) (hW : A.IsWeilType) (n : ℕ)
    (hn : Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)) + Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)) = n) :
    exteriorSpanC (hn ▸ A.weilClasses hTop hW) =
      LinearMap.range (exteriorPower.map n A.Vs.subtype) ⊔
        LinearMap.range (exteriorPower.map n A.Vsbar.subtype) := by
  subst n
  exact weilClasses_baseChange_eq_topLines A hTop hW (by norm_num)

private theorem pw0b_weil_pullback (A : HodgeBlocks.WeilAction M 3)
    (hTop : M.H (1, 0) ⊔ M.H (0, 1) = ⊤) (hW : A.IsWeilType) (m n : ℕ)
    (hn : Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)) + Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)) = n) :
    ∀ r s w, w ∈ (hn ▸ A.weilClasses hTop hW) →
      exteriorPower.map n (weilPowerPullback A.J r s) w ∈
        divisorPulledWeilSpan A.J (rationalExteriorHodge M.H M.isInternal m 2)
          (A.weilClasses hTop hW) n := by
  subst n
  exact (isDivisorPulledWeilClosed_span _ _ _).pullback_mem

omit [FiniteDimensional ℚ V] in
private theorem pw0b_map_mem_range {U W : Type*} [AddCommGroup U] [Module ℂ U]
    [AddCommGroup W] [Module ℂ W] (f : U →ₗ[ℂ] W) (P : Submodule ℂ W)
    (hf : ∀ x, f x ∈ P) (k : ℕ) (v : ⋀[ℂ]^k U) :
    exteriorPower.map k f v ∈ LinearMap.range (exteriorPower.map k P.subtype) := by
  refine ⟨exteriorPower.map k (f.codRestrict P hf) v, ?_⟩
  rw [← LinearMap.comp_apply, ← exteriorPower.map_comp]
  rfl

private theorem pw0b_detW_mem (A : HodgeBlocks.WeilAction M 3)
    (hTop : M.H (1, 0) ⊔ M.H (0, 1) = ⊤) (hW : A.IsWeilType)
    (E : LinearMap.BilinForm ℚ V) (hE : E.Nondegenerate)
    (hskew : ∀ x y, E (A.J x) y = -E x (A.J y)) (m : ℕ) (a : Fin m → ℂ) :
    let e := polarizedSplitting E hE A.J A.J_sq hskew
    let n := Module.finrank ℂ (Module.End.eigenspace (A.J.baseChange ℂ) root)
    (exteriorEquiv n (powerModel m e)).symm (detW a) ∈
      exteriorSpanC (divisorPulledWeilSpan A.J (rationalExteriorHodge M.H M.isInternal m 2)
        (A.weilClasses hTop hW) n) := by
  let W := Module.End.eigenspace (A.J.baseChange ℂ) root
  let e := polarizedSplitting E hE A.J A.J_sq hskew
  let n := Module.finrank ℂ W
  have hn : Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)) + Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)) = n :=
    pw0b_middleDegree A hTop hW
  let T : Submodule ℚ (⋀[ℚ]^n V) := hn ▸ A.weilClasses hTop hW
  let P := divisorPulledWeilSpan A.J (rationalExteriorHodge M.H M.isInternal m 2)
    (A.weilClasses hTop hW) n
  let Q := (exteriorSpanC P).comap (exteriorEquiv n (powerModel m e)).symm.toLinearMap
  change detW a ∈ Q
  apply (show Submodule.span ℂ (Set.range (fun r : Fin m → ℚ =>
    detW (K := ℂ) (W := W) (U' := Fin m → ℂ) (fun i => (r i : ℂ)))) ≤ Q from ?_)
    (detW_mem_span_rat a)
  apply Submodule.span_le.mpr
  rintro _ ⟨r, rfl⟩
  apply detWOf_rat_mem_exteriorSpanC A.J e (polarizedSplitting_J _ _ _ _ _) T P
    (pw0b_weil_pullback A hTop hW m n hn) _ _ r
  rw [show exteriorSpanC T = _ from pw0b_topLines A hTop hW n hn]
  apply Submodule.mem_sup_left
  apply pw0b_map_mem_range
  intro w
  change e.symm (w, 0) ∈ A.Vs
  simp only [e, polarizedSplitting_symm_apply, map_zero, Submodule.coe_zero, add_zero]
  rw [← pw0b_vs_eq A]
  exact w.property

private theorem pw0b_detWDual_mem (A : HodgeBlocks.WeilAction M 3)
    (hTop : M.H (1, 0) ⊔ M.H (0, 1) = ⊤) (hW : A.IsWeilType)
    (E : LinearMap.BilinForm ℚ V) (hE : E.Nondegenerate)
    (hskew : ∀ x y, E (A.J x) y = -E x (A.J y)) (m : ℕ) (a : Fin m → ℂ) :
    let e := polarizedSplitting E hE A.J A.J_sq hskew
    let n := Module.finrank ℂ (Module.End.eigenspace (A.J.baseChange ℂ) root)
    (exteriorEquiv n (powerModel m e)).symm (detWDual a) ∈
      exteriorSpanC (divisorPulledWeilSpan A.J (rationalExteriorHodge M.H M.isInternal m 2)
        (A.weilClasses hTop hW) n) := by
  let W := Module.End.eigenspace (A.J.baseChange ℂ) root
  let e := polarizedSplitting E hE A.J A.J_sq hskew
  let n := Module.finrank ℂ W
  have hn : Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)) + Module.finrank ℂ ↥(A.Vs ⊓ M.H (1, 0)) = n :=
    pw0b_middleDegree A hTop hW
  let T : Submodule ℚ (⋀[ℚ]^n V) := hn ▸ A.weilClasses hTop hW
  let P := divisorPulledWeilSpan A.J (rationalExteriorHodge M.H M.isInternal m 2)
    (A.weilClasses hTop hW) n
  let Q := (exteriorSpanC P).comap (exteriorEquiv n (powerModel m e)).symm.toLinearMap
  change detWDual a ∈ Q
  apply (show Submodule.span ℂ (Set.range (fun r : Fin m → ℚ =>
    detWDual (K := ℂ) (W := W) (U := Fin m → ℂ) (fun i => (r i : ℂ)))) ≤ Q from ?_)
    (detWDual_mem_span_rat a)
  apply Submodule.span_le.mpr
  rintro _ ⟨r, rfl⟩
  apply detWDualOf_rat_mem_exteriorSpanC A.J e (polarizedSplitting_J _ _ _ _ _) T P
    (pw0b_weil_pullback A hTop hW m n hn) _ _ r
  rw [show exteriorSpanC T = _ from pw0b_topLines A hTop hW n hn]
  apply Submodule.mem_sup_right
  apply pw0b_map_mem_range
  intro w
  change e.symm (0, w) ∈ A.Vsbar
  simp only [e, polarizedSplitting_symm_apply, Submodule.coe_zero, zero_add]
  simp [HodgeBlocks.WeilAction.Vsbar, HodgeBlocks.WeilAction.omegaC, root]

/-- Spec S8. -/
theorem spec_pw0_exteriorHodgeClasses_eq_divisorPulledWeilSpan_aux
    (A : HodgeBlocks.WeilAction M 3) (hTop : M.H (1, 0) ⊔ M.H (0, 1) = ⊤) (hW : A.IsWeilType)
    (E : LinearMap.BilinForm ℚ V) (hE : E.Nondegenerate)
    (hskew : ∀ x y, E (A.J x) y = -E x (A.J y))
    (hSU : complexSpan (hodgeLieAlgebra M.H M.isInternal).toSubmodule =
      (complexSU E hE A.J A.J_sq hskew).toSubmodule) (m k : ℕ) :
    exteriorHodgeClasses M.H M.isInternal m k =
      ((divisorPulledWeilSpan A.J (rationalExteriorHodge M.H M.isInternal m 2)
        (A.weilClasses hTop hW) k).baseChange ℂ).map (exteriorBaseChange k).toLinearMap := by
  let e := polarizedSplitting E hE A.J A.J_sq hskew
  let P := divisorPulledWeilSpan A.J (rationalExteriorHodge M.H M.isInternal m 2)
    (A.weilClasses hTop hW)
  have hP := isDivisorPulledWeilClosed_span A.J
    (rationalExteriorHodge M.H M.isInternal m 2) (A.weilClasses hTop hW)
  apply le_antisymm
  · change exteriorHodgeClasses M.H M.isInternal m k ≤ exteriorSpanC (P k)
    rw [exteriorHodgeClasses_eq_generated M.H M.isInternal E hE A.J A.J_sq hskew m k hSU]
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
      congr 1
      funext i
      exact Fin.elim0 i
    | theta u u' =>
      have hθ : (exteriorEquiv 2 (powerModel m e)).symm (theta u u') ∈
          exteriorHodgeClasses M.H M.isInternal m 2 := by
        rw [exteriorHodgeClasses_eq_generated M.H M.isInternal E hE A.J A.J_sq hskew m 2 hSU]
        exact ⟨theta u u', Submodule.subset_span (GeneratorProduct.theta u u'), rfl⟩
      exact exteriorSpanC_mono hP.divisor_le hθ
    | detW a => exact pw0b_detW_mem A hTop hW E hE hskew m a
    | detWDual a => exact pw0b_detWDual_mem A hTop hW E hE hskew m a
    | @wedge i j v w hv hw ihv ihw =>
      simp only [f1575_exteriorEquiv_symm] at ihv ihw ⊢
      rw [f1575_exterior_map_wedge]
      exact exteriorSpanC_wedge (P i) (P j) (P (i + j))
        (fun v hv w hw => hP.wedge_mem i j v w hv hw) ihv ihw
  · change _ ≤ ((rationalExteriorHodge M.H M.isInternal m k).baseChange ℂ).map
      (exteriorBaseChange k).toLinearMap
    exact Submodule.map_mono (Submodule.baseChange_mono ℂ
      (pw0b_divisorPulledWeilSpan_le A hTop hW m k))

/-- Spec S9. -/
theorem spec_pw0_rationalExteriorHodge_eq_divisorPulledWeilSpan_aux
    (A : HodgeBlocks.WeilAction M 3) (hTop : M.H (1, 0) ⊔ M.H (0, 1) = ⊤) (hW : A.IsWeilType)
    (E : LinearMap.BilinForm ℚ V) (hE : E.Nondegenerate)
    (hskew : ∀ x y, E (A.J x) y = -E x (A.J y))
    (hSU : complexSpan (hodgeLieAlgebra M.H M.isInternal).toSubmodule =
      (complexSU E hE A.J A.J_sq hskew).toSubmodule) (m k : ℕ) :
    rationalExteriorHodge M.H M.isInternal m k =
      divisorPulledWeilSpan A.J (rationalExteriorHodge M.H M.isInternal m 2)
        (A.weilClasses hTop hW) k := by
  have h := spec_pw0_exteriorHodgeClasses_eq_divisorPulledWeilSpan_aux A hTop hW E hE hskew hSU m k
  apply le_antisymm
  · apply (Submodule.baseChange_le_iff (A := ℂ)).mp
    apply (Submodule.map_le_map_iff_of_injective (exteriorBaseChange k).injective _ _).mp
    change exteriorHodgeClasses M.H M.isInternal m k ≤ _
    rw [h]
  · apply (Submodule.baseChange_le_iff (A := ℂ)).mp
    apply (Submodule.map_le_map_iff_of_injective (exteriorBaseChange k).injective _ _).mp
    change _ ≤ exteriorHodgeClasses M.H M.isInternal m k
    rw [h]

/-- Spec S10. -/
theorem spec_pw0_rationalExteriorHodge_eq_cmPowerSpan_aux
    (A : HodgeBlocks.WeilAction M 3) (hTop : M.H (1, 0) ⊔ M.H (0, 1) = ⊤)
    (E : LinearMap.BilinForm ℚ V) (hE : E.Nondegenerate) (hAlt : E.IsAlt)
    (hskew : ∀ x y, E (A.J x) y = -E x (A.J y))
    (hGk : HodgeLieIsGk M.H M.isInternal E (Algebra.adjoin ℚ {A.J}) A.J) (m k : ℕ) :
    rationalExteriorHodge M.H M.isInternal m k =
      cmPowerSpan (Algebra.adjoin ℚ {A.J}) (rationalExteriorHodge M.H M.isInternal m 2)
        (A.weilClasses hTop
          (isWeilType_of_hodgeLieIsGk_aux (by norm_num) A hTop E _ hGk)) k := by
  have hSU := (spec_pw0_hodgeLieIsGk_adjoin_iff_aux M.H M.isInternal E hE hAlt A.J A.J_sq
    hskew).mp hGk
  rw [spec_pw0_cmPowerSpan_adjoin_eq_aux A.J A.J_sq]
  exact spec_pw0_rationalExteriorHodge_eq_divisorPulledWeilSpan_aux A hTop _ E hE hskew hSU m k

end Weil

section Geometric

variable {X : Over (Spec ↧ℂ)} [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
  {μ : CupProduct X} [GrpObj X]

/-- Spec S11. -/
theorem spec_pw0_abelian_rationalExteriorHodge_eq_aux (hF : FiniteBetti X)
    (hB : BettiDeRhamIso X) (hD : HodgeDecomposition X) (hT : TorusCohomology μ)
    (A : letI := hT.finite
      HodgeBlocks.WeilAction (abelianVarietyCohomologyOf hF hB hD hT).weight1 3)
    (hW : letI := hT.finite; A.IsWeilType) {η : HQ X 2}
    (hω : IsNondegenerate (polarizationVec hT η))
    (hR : letI := hT.finite; IsRosatiSkew (polarizationVec hT η) A.J)
    (hSU : letI := hT.finite
      complexSpan (hodgeLieAlgebra (abelianVarietyCohomologyOf hF hB hD hT).weight1.H
          (abelianVarietyCohomologyOf hF hB hD hT).weight1.isInternal).toSubmodule =
        (complexSU (polarizationForm hT hω) (nondegenerate_polarizationForm hT hω) A.J A.J_sq
          (polarizationForm_skew hT hω hR)).toSubmodule)
    (m k : ℕ) :
    letI := hT.finite
    let S := abelianVarietyCohomologyOf hF hB hD hT
    rationalExteriorHodge S.weight1.H S.weight1.isInternal m k =
      divisorPulledWeilSpan A.J (rationalExteriorHodge S.weight1.H S.weight1.isInternal m 2)
        (A.weilClasses (h10_sup_h01_eq_top hF hB hD hT) hW) k := by
  let _ := hT.finite
  exact spec_pw0_rationalExteriorHodge_eq_divisorPulledWeilSpan_aux A
    (h10_sup_h01_eq_top hF hB hD hT) hW (polarizationForm hT hω)
    (nondegenerate_polarizationForm hT hω) (polarizationForm_skew hT hω hR) hSU m k

end Geometric

/-- Spec S12. -/
theorem spec_pw0_not_hodgeLieIsGk_hsuCMHodge_aux :
    ¬ HodgeLieIsGk hsuCMHodge spec_hsuCMHodge_isInternal hsuE (Algebra.adjoin ℚ {hsuJ}) hsuJ := by
  intro h
  exact spec_hsuCMHodge_hSU_fails ((spec_pw0_hodgeLieIsGk_adjoin_iff_aux hsuCMHodge
    spec_hsuCMHodge_isInternal hsuE spec_hsuE_nondegenerate spec_hsuE_isAlt hsuJ spec_hsuJ_sq
    spec_hsuE_skew).mp h)

end HodgeLean.Adapters
