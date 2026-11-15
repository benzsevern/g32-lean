import HodgeLean.Adapters.F1575PowersOne

/-! # Proofs for the F-1575 all-powers spec

The agent's working file. Fill every proof hole. **Do not change the statement of
any `_aux` theorem**: `F1575PowersFix.lean` (frozen) restates each one and must still typecheck.
Helper lemmas may be added freely, in this file or in new files.
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

private theorem rationalExteriorHodge_wedge {V : Type*} [AddCommGroup V] [Module ℚ V]
    [FiniteDimensional ℚ V] (H : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℚ] V))
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

private theorem exteriorHodge_grading_zero {V : Type*} [AddCommGroup V] [Module ℚ V]
    [FiniteDimensional ℚ V] (H : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℚ] V))
    (hH : DirectSum.IsInternal H) (m k : ℕ) (p : ℤ)
    (v : ⋀[ℂ]^k (ℂ ⊗[ℚ] (V ⊗[ℚ] (Fin m → ℚ))))
    (hv : v ∈ exteriorHodge H m k (p, p)) :
    exteriorDer k (powerAction m (gradingOperator H hH)) v = 0 := by
  have h := exteriorHodge_le_eigenspace H hH m k (p, p) hv
  rw [Module.End.mem_eigenspace_iff] at h
  simpa using h

private theorem weilAction_commutes_grading {V : Type*} [AddCommGroup V] [Module ℚ V]
    [FiniteDimensional ℚ V] (M : HodgeBlocks.QHodgeStructure 1 V)
    (A : HodgeBlocks.WeilAction M 3) :
    (gradingOperator M.H M.isInternal).comp (A.J.baseChange ℂ) =
      (A.J.baseChange ℂ).comp (gradingOperator M.H M.isInternal) := by
  apply linearMap_ext_of_isInternal M.isInternal
  intro pq x hx
  have hxJ : A.J.baseChange ℂ x ∈ M.H pq := A.preserves pq ⟨x, hx, rfl⟩
  rw [LinearMap.comp_apply, gradingOperator_apply_of_mem M.H M.isInternal hxJ,
    LinearMap.comp_apply, gradingOperator_apply_of_mem M.H M.isInternal hx, map_smul]

private theorem exteriorComplexify_map {U V : Type*} [AddCommGroup U] [Module ℚ U]
    [AddCommGroup V] [Module ℚ V] (k : ℕ) (f : U →ₗ[ℚ] V) :
    (exteriorComplexify k).comp (exteriorPower.map k f) =
      ((exteriorPower.map k (f.baseChange ℂ)).restrictScalars ℚ).comp (exteriorComplexify k) := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro x
  simp [LinearMap.compAlternatingMap_apply, exteriorComplexify_ιMulti,
    exteriorPower.map_apply_ιMulti]
  congr 1

private theorem exterior_map_preserves_eigenspace_range {V : Type*} [AddCommGroup V]
    [Module ℂ V] (T : Module.End ℂ V) (c : ℂ) (n : ℕ) :
    (LinearMap.range (exteriorPower.map n (Module.End.eigenspace T c).subtype)).map
      (exteriorPower.map n T) ≤
      LinearMap.range (exteriorPower.map n (Module.End.eigenspace T c).subtype) := by
  rintro _ ⟨x, hx, rfl⟩
  rcases hx with ⟨y, rfl⟩
  refine ⟨exteriorPower.map n (c • LinearMap.id) y, ?_⟩
  have hbase : (Module.End.eigenspace T c).subtype.comp (c • LinearMap.id) =
      T.comp (Module.End.eigenspace T c).subtype := by
    ext z
    simpa [LinearMap.comp_apply, LinearMap.smul_apply] using
      (Module.End.mem_eigenspace_iff.mp z.property).symm
  have hext := congrArg (exteriorPower.map n) hbase
  simpa only [exteriorPower.map_comp, LinearMap.comp_apply] using
    DFunLike.congr_fun hext y

private theorem weilClasses_map_J_mem (hM : IsMemberOfM hF hB hD hT A η) :
    letI := hT.finite
    let W := A.weilClasses (h10_sup_h01_eq_top hF hB hD hT) hM.isWeilType
    ∀ w ∈ W, exteriorPower.map _ A.J w ∈ W := by
  letI := hT.finite
  dsimp only
  intro w hw
  change HodgeBlocks.complexifyWedge _ (exteriorPower.map _ A.J w) ∈
    ((LinearMap.range (exteriorPower.map _ A.Vs.subtype) ⊔
      LinearMap.range (exteriorPower.map _ A.Vsbar.subtype)).restrictScalars ℚ)
  rw [HodgeBlocks.complexifyWedge_exteriorPower_map]
  let n := Module.finrank ℂ ↥(A.Vs ⊓ (abelianVarietyCohomologyOf hF hB hD hT).weight1.H (1, 0)) +
    Module.finrank ℂ ↥(A.Vs ⊓ (abelianVarietyCohomologyOf hF hB hD hT).weight1.H (1, 0))
  have hVs := exterior_map_preserves_eigenspace_range A.Jc (HodgeBlocks.WeilAction.omegaC 3) n
  have hVsbar := exterior_map_preserves_eigenspace_range A.Jc (-HodgeBlocks.WeilAction.omegaC 3) n
  let R : Submodule ℂ (⋀[ℂ]^n (ℂ ⊗[ℚ] HQ X 1)) :=
    LinearMap.range (exteriorPower.map n A.Vs.subtype) ⊔
      LinearMap.range (exteriorPower.map n A.Vsbar.subtype)
  have hmap : R.map (exteriorPower.map n A.Jc) ≤ R := by
    dsimp [R]
    rw [Submodule.map_sup]
    exact sup_le_sup hVs hVsbar
  exact hmap ⟨_, hw, rfl⟩

private theorem f1575SingleCopyComplex_commutes {V : Type*} [AddCommGroup V] [Module ℚ V]
    [FiniteDimensional ℚ V] (G : Module.End ℂ (ℂ ⊗[ℚ] V)) :
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

private theorem pullback_commutes_power_grading {V : Type*} [AddCommGroup V] [Module ℚ V]
    [FiniteDimensional ℚ V] (J : Module.End ℚ V)
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

/-- Spec S1: the multiplicity-one identification with the geometric `divisorWeilSpan`. -/
theorem f1575PowerOne_map_eq_divisorWeilSpan_aux (hM : IsMemberOfM hF hB hD hT A η)
    (hC : CupFiltered X μ) (p : ℕ) :
    letI := hT.finite
    (f1575PowerHodgeTwoPulledWeilSpan hM 1 (2 * p)).map
      ((hT.cupWedgeEquiv (2 * p)).toLinearMap ∘ₗ exteriorPower.map (2 * p) (powerOneFlatten X)) =
      divisorWeilSpan hF hB hD hT A hM.isWeilType p := by
  letI := hT.finite
  let S := abelianVarietyCohomologyOf hF hB hD hT
  let P := f1575PowerHodgeTwoPulledWeilSpan hM 1
  let D := divisorWeilSpan hF hB hD hT A hM.isWeilType
  let L : ∀ k : ℕ, (⋀[ℚ]^k (HQ X 1 ⊗[ℚ] (Fin 1 → ℚ))) →ₗ[ℚ] HQ X k :=
    fun k => (hT.cupWedgeEquiv k).toLinearMap ∘ₗ exteriorPower.map k (powerOneFlatten X)
  have L_cast : ∀ {i j : ℕ} (h : i = j)
      (z : ⋀[ℚ]^i (HQ X 1 ⊗[ℚ] (Fin 1 → ℚ))),
      L j (h ▸ z) = HQ.castEquiv X h (L i z) := by
    intro i j h z
    subst j
    rw [HQ.castEquiv_apply_self]
  have P_cast : ∀ {i j : ℕ} (h : i = j)
      (z : ⋀[ℚ]^i (HQ X 1 ⊗[ℚ] (Fin 1 → ℚ))), z ∈ P i → h ▸ z ∈ P j := by
    intro i j h z hz
    subst j
    exact hz
  have L_wedge : ∀ (i j : ℕ) (v : ⋀[ℚ]^i (HQ X 1 ⊗[ℚ] (Fin 1 → ℚ)))
      (w : ⋀[ℚ]^j (HQ X 1 ⊗[ℚ] (Fin 1 → ℚ))),
      L (i + j) (exteriorPower.wedge ℚ _ i j v w) = μ.cup rfl (L i v) (L j w) := by
    intro i j v w
    simp only [L, LinearMap.comp_apply, exteriorPower_map_wedge]
    change μ.cupWedgeMap (i + j) (exteriorPower.wedge ℚ _ i j
      (exteriorPower.map i (powerOneFlatten X) v)
      (exteriorPower.map j (powerOneFlatten X) w)) = _
    exact μ.cupWedgeMap_wedge i j _ _
  change (P (2 * p)).map (L (2 * p)) = D p
  apply le_antisymm
  · apply (Submodule.map_le_iff_le_comap).mpr
    let F : ∀ k, Submodule ℚ (⋀[ℚ]^k (HQ X 1 ⊗[ℚ] (Fin 1 → ℚ))) :=
      fun k => (f1575EvenCohomologySpanQ D k).comap (L k)
    have hFc : IsDivisorPulledWeilClosed A.J
        (rationalExteriorHodge S.weight1.H S.weight1.isInternal 1 2)
        (A.weilClasses (h10_sup_h01_eq_top hF hB hD hT) hM.isWeilType) F := by
      refine { unit_mem := ?_, divisor_le := ?_, pullback_mem := ?_, wedge_mem := ?_ }
      · change L 0 (exteriorPower.ιMulti ℚ 0 Fin.elim0) ∈ f1575EvenCohomologySpanQ D 0
        refine Or.inr ⟨0, rfl, ?_⟩
        rw [HQ.castEquiv_apply_self]
        have hunit : L 0 (exteriorPower.ιMulti ℚ 0 Fin.elim0) = unitClass X := by
          change μ.cupWedgeMap 0 (exteriorPower.map 0 (powerOneFlatten X)
            (exteriorPower.ιMulti ℚ 0 Fin.elim0)) = unitClass X
          rw [exteriorPower.map_apply_ιMulti]
          have hf : powerOneFlatten X ∘ Fin.elim0 = Fin.elim0 := by
            funext i
            exact Fin.elim0 i
          rw [hf]
          exact μ.cupWedgeMap_zero
        rw [hunit]
        exact unitClass_mem_divisorWeilSpan hF hB hD hT A hM.isWeilType
      · intro v hv
        change L 2 v ∈ f1575EvenCohomologySpanQ D 2
        refine Or.inr ⟨1, rfl, ?_⟩
        apply hdg_one_le_divisorWeilSpan hF hB hD hT A hM.isWeilType
        rw [show L 2 = f1575SingleCopyCohomologyQ μ 2 by
          exact powerOne_cupWedge_map_eq_f1575SingleCopyCohomologyQ 2]
        rw [← f1575_rationalHodge_map_eq hF hB hD hT hC 1]
        exact ⟨v, hv, rfl⟩
      · intro r s w hw
        let q := Module.finrank ℂ ↥(A.Vs ⊓ S.weight1.H (1, 0))
        change L (q + q) (exteriorPower.map _ (weilPowerPullback A.J r s) w) ∈
          f1575EvenCohomologySpanQ D (q + q)
        refine Or.inr ⟨q, by omega, ?_⟩
        apply weilClassOf_le_divisorWeilSpan hF hB hD hT A hM.isWeilType
        have hW : exteriorPower.map _ (r 0 • LinearMap.id + s 0 • A.J) w ∈
            A.weilClasses (h10_sup_h01_eq_top hF hB hD hT) hM.isWeilType :=
          weilClasses_map_linear_mem hM (r 0) (s 0) w hw
        refine ⟨_, hW, ?_⟩
        dsimp [q]
        apply congrArg (HQ.castEquiv X (two_mul _).symm)
        change μ.cupWedgeMap _ (exteriorPower.map _ (r 0 • LinearMap.id + s 0 • A.J) w) =
          L _ (exteriorPower.map _ (weilPowerPullback A.J r s) w)
        dsimp only [L, LinearMap.comp_apply]
        change μ.cupWedgeMap _ (exteriorPower.map _ (r 0 • LinearMap.id + s 0 • A.J) w) =
          μ.cupWedgeMap _ (exteriorPower.map _ (powerOneFlatten X)
            (exteriorPower.map _ (weilPowerPullback A.J r s) w))
        congr 1
        rw [← LinearMap.comp_apply, ← exteriorPower.map_comp,
          powerOneFlatten_comp_weilPowerPullback]
      · intro i j v w hv hw
        change L (i + j) (exteriorPower.wedge ℚ _ i j v w) ∈
          f1575EvenCohomologySpanQ D (i + j)
        rw [show L (i + j) (exteriorPower.wedge ℚ _ i j v w) =
            μ.cup rfl (L i v) (L j w) by
          simp only [L, LinearMap.comp_apply, exteriorPower_map_wedge]
          change μ.cupWedgeMap (i + j) (exteriorPower.wedge ℚ _ i j
            (exteriorPower.map i (powerOneFlatten X) v)
            (exteriorPower.map j (powerOneFlatten X) w)) = _
          exact μ.cupWedgeMap_wedge i j _ _]
        exact f1575EvenCohomologySpanQ_cup D
          (fun h a b ha hb => cup_mem_divisorWeilSpan hF hB hD hT A hM.isWeilType
            h a b ha hb) rfl hv hw
    have hle := divisorPulledWeilSpan_le A.J
      (rationalExteriorHodge S.weight1.H S.weight1.isInternal 1 2)
      (A.weilClasses (h10_sup_h01_eq_top hF hB hD hT) hM.isWeilType) hFc (2 * p)
    change P (2 * p) ≤ F (2 * p) at hle
    simpa only [F, f1575EvenCohomologySpanQ_even] using hle
  · let E : ∀ a, Submodule ℚ (HQ X (2 * a)) := fun a => (P (2 * a)).map (L (2 * a))
    apply divisorWeilSpan_le hF hB hD hT A hM.isWeilType (F := E) _ p
    refine { unit_mem := ?_, hdg_one_le := ?_, weil_le := ?_, cup_mem := ?_ }
    · refine ⟨exteriorPower.ιMulti ℚ 0 Fin.elim0,
        (isDivisorPulledWeilClosed_span A.J
          (rationalExteriorHodge S.weight1.H S.weight1.isInternal 1 2)
          (A.weilClasses (h10_sup_h01_eq_top hF hB hD hT) hM.isWeilType)).unit_mem, ?_⟩
      have hunit : L 0 (exteriorPower.ιMulti ℚ 0 Fin.elim0) = unitClass X := by
        change μ.cupWedgeMap 0 (exteriorPower.map 0 (powerOneFlatten X)
          (exteriorPower.ιMulti ℚ 0 Fin.elim0)) = unitClass X
        rw [exteriorPower.map_apply_ιMulti]
        have hf : powerOneFlatten X ∘ Fin.elim0 = Fin.elim0 := by
          funext i
          exact Fin.elim0 i
        rw [hf]
        exact μ.cupWedgeMap_zero
      exact hunit
    · rw [← f1575_rationalHodge_map_eq hF hB hD hT hC 1]
      rintro _ ⟨v, hv, rfl⟩
      exact ⟨v, (isDivisorPulledWeilClosed_span A.J
        (rationalExteriorHodge S.weight1.H S.weight1.isInternal 1 2)
        (A.weilClasses (h10_sup_h01_eq_top hF hB hD hT) hM.isWeilType)).divisor_le hv, rfl⟩
    · rintro _ ⟨w, hw, rfl⟩
      let q := Module.finrank ℂ ↥(A.Vs ⊓ S.weight1.H (1, 0))
      let r : Fin 1 → ℚ := fun _ => 1
      let s : Fin 1 → ℚ := fun _ => 0
      let z₀ := exteriorPower.map (q + q) (weilPowerPullback A.J r s) w
      have hz₀ : z₀ ∈ P (q + q) :=
        (isDivisorPulledWeilClosed_span A.J
          (rationalExteriorHodge S.weight1.H S.weight1.isInternal 1 2)
          (A.weilClasses (h10_sup_h01_eq_top hF hB hD hT) hM.isWeilType)).pullback_mem r s w hw
      let hq : q + q = 2 * q := by omega
      refine ⟨hq ▸ z₀, P_cast hq z₀ hz₀, ?_⟩
      rw [L_cast]
      apply congrArg (HQ.castEquiv X hq)
      dsimp [z₀, r, s]
      change μ.cupWedgeMap _ (exteriorPower.map _ (powerOneFlatten X)
        (exteriorPower.map _ (weilPowerPullback A.J (fun _ => 1) (fun _ => 0)) w)) =
        μ.cupWedgeMap _ w
      congr 1
      rw [← LinearMap.comp_apply, ← exteriorPower.map_comp,
        powerOneFlatten_comp_weilPowerPullback]
      simp
    · intro a b hab x y hx hy
      rcases hx with ⟨u, hu, rfl⟩
      rcases hy with ⟨v, hv, rfl⟩
      let z₀ := exteriorPower.wedge ℚ _ (2 * a) (2 * b) u v
      have hz₀ : z₀ ∈ P (2 * a + 2 * b) :=
        (isDivisorPulledWeilClosed_span A.J
          (rationalExteriorHodge S.weight1.H S.weight1.isInternal 1 2)
          (A.weilClasses (h10_sup_h01_eq_top hF hB hD hT) hM.isWeilType)).wedge_mem
            _ _ u v hu hv
      refine ⟨hab ▸ z₀, P_cast hab z₀ hz₀, ?_⟩
      rw [L_cast, L_wedge, CupProduct.castEquiv_cup]

/-- Spec S2: every generator is a rational Hodge class (the reverse inclusion, rationally). -/
theorem f1575PowerHodgeTwoPulledWeilSpan_le_rationalExteriorHodge_aux
    (hM : IsMemberOfM hF hB hD hT A η) (m k : ℕ) :
    letI := hT.finite
    let S := abelianVarietyCohomologyOf hF hB hD hT
    f1575PowerHodgeTwoPulledWeilSpan hM m k ≤
      rationalExteriorHodge S.weight1.H S.weight1.isInternal m k := by
  letI := hT.finite
  let S := abelianVarietyCohomologyOf hF hB hD hT
  apply divisorPulledWeilSpan_le
  constructor
  · change exteriorDer 0 (powerAction m (gradingOperator S.weight1.H S.weight1.isInternal))
      (exteriorComplexify 0 (exteriorPower.ιMulti ℚ 0 Fin.elim0)) = 0
    simp [exteriorDer_ιMulti]
  · exact le_rfl
  · intro r s w hw
    let q := Module.finrank ℂ ↥(A.Vs ⊓ S.weight1.H (1, 0))
    have hwH := A.isHodgeClass_of_mem_weilClasses
      (h10_sup_h01_eq_top hF hB hD hT) hM.isWeilType hw
    have hw' : (1 : ℂ) ⊗ₜ[ℚ] w ∈ (S.weight1.exteriorPower (V := HQ X 1) (q + q)).H (q, q) := by
      simpa [q, HodgeBlocks.IsHodgeClass, HodgeBlocks.WeilAction.weightCast_H] using hwH
    have hwsrc : (f1575SingleCopyExterior (V := HQ X 1) (q + q)).symm
        ((1 : ℂ) ⊗ₜ[ℚ] w) ∈ exteriorHodge S.weight1.H 1 (q + q) (q, q) := by
      change (1 : ℂ) ⊗ₜ[ℚ] w ∈ S.weight1.exteriorPowerH (V := HQ X 1) (q + q) (q, q) at hw'
      rw [← f1575SingleCopyExterior_map_hodge] at hw'
      rw [Submodule.mem_map_equiv] at hw'
      exact hw'
    have hzsrc := exteriorHodge_grading_zero S.weight1.H S.weight1.isInternal 1 (q + q)
      (q : ℤ) _ hwsrc
    let e := f1575SingleCopyExterior (V := HQ X 1) (q + q)
    have he : exteriorPower.map (q + q) (f1575SingleCopyComplex (V := HQ X 1)).toLinearMap
        (e.symm ((1 : ℂ) ⊗ₜ[ℚ] w)) =
        exteriorBaseChange (q + q) ((1 : ℂ) ⊗ₜ[ℚ] w) := by
      change (exteriorEquiv (q + q) (f1575SingleCopyComplex (V := HQ X 1)))
        ((exteriorEquiv (q + q) (f1575SingleCopyComplex (V := HQ X 1))).symm
          ((exteriorBaseChange (q + q)) ((1 : ℂ) ⊗ₜ[ℚ] w))) = _
      rw [LinearEquiv.apply_symm_apply]
    have hzbase : exteriorDer (q + q) (gradingOperator S.weight1.H S.weight1.isInternal)
        (exteriorBaseChange (q + q) ((1 : ℂ) ⊗ₜ[ℚ] w)) = 0 := by
      rw [← he, exteriorDer_map _ _ _ _ (f1575SingleCopyComplex_commutes
        (gradingOperator S.weight1.H S.weight1.isInternal)), hzsrc, map_zero]
    have hzw : exteriorDer (q + q) (gradingOperator S.weight1.H S.weight1.isInternal)
        (exteriorComplexify (q + q) w) = 0 := by
      have hc : exteriorBaseChange (q + q) ((1 : ℂ) ⊗ₜ[ℚ] w) =
          exteriorComplexify (q + q) w := by
        change (exteriorBaseChange (q + q)).toLinearMap ((1 : ℂ) ⊗ₜ[ℚ] w) = _
        rw [exteriorBaseChange_eq_lift, LinearMap.liftBaseChange_tmul, one_smul]
      rw [← hc]
      exact hzbase
    change exteriorDer _ (powerAction m (gradingOperator S.weight1.H S.weight1.isInternal))
      (exteriorComplexify _ (exteriorPower.map _ (weilPowerPullback A.J r s) w)) = 0
    have hm := LinearMap.congr_fun (exteriorComplexify_map _ (weilPowerPullback A.J r s)) w
    change exteriorComplexify _ (exteriorPower.map _ (weilPowerPullback A.J r s) w) = _ at hm
    rw [hm]
    change exteriorDer _ (powerAction m (gradingOperator S.weight1.H S.weight1.isInternal))
      (exteriorPower.map _ ((weilPowerPullback A.J r s).baseChange ℂ)
        (exteriorComplexify _ w)) = 0
    rw [exteriorDer_map _ _ _ _
      (pullback_commutes_power_grading A.J _
        (weilAction_commutes_grading S.weight1 A) r s), hzw, map_zero]
  · exact rationalExteriorHodge_wedge S.weight1.H S.weight1.isInternal m

/-- Spec S3: equality of the complex Hodge classes with the complexified span, from `hSU`. -/
theorem f1575Power_hodgeClasses_eq_hodgeTwoPulledWeilSpan_aux
    (hM : IsMemberOfM hF hB hD hT A η)
    (hSU : F1575MemberHodgeGroupIsSU hF hB hD hT A hM) (m k : ℕ) :
    letI := hT.finite
    let S := abelianVarietyCohomologyOf hF hB hD hT
    exteriorHodgeClasses S.weight1.H S.weight1.isInternal m k =
      ((f1575PowerHodgeTwoPulledWeilSpan hM m k).baseChange ℂ).map
        (exteriorBaseChange k).toLinearMap := by
  letI := hT.finite
  let S := abelianVarietyCohomologyOf hF hB hD hT
  apply le_antisymm
  · exact f1575Power_hodgeClasses_le_hodgeTwoPulledWeilSpan hM hSU m k
  · change _ ≤ ((rationalExteriorHodge S.weight1.H S.weight1.isInternal m k).baseChange ℂ).map
      (exteriorBaseChange k).toLinearMap
    exact Submodule.map_mono (Submodule.baseChange_mono ℂ
      (f1575PowerHodgeTwoPulledWeilSpan_le_rationalExteriorHodge_aux hM m k))

/-- Spec S4: the rational form of S3, from `hSU`. -/
theorem f1575Power_rationalExteriorHodge_eq_hodgeTwoPulledWeilSpan_aux
    (hM : IsMemberOfM hF hB hD hT A η)
    (hSU : F1575MemberHodgeGroupIsSU hF hB hD hT A hM) (m k : ℕ) :
    letI := hT.finite
    let S := abelianVarietyCohomologyOf hF hB hD hT
    rationalExteriorHodge S.weight1.H S.weight1.isInternal m k =
      f1575PowerHodgeTwoPulledWeilSpan hM m k := by
  letI := hT.finite
  let S := abelianVarietyCohomologyOf hF hB hD hT
  apply le_antisymm
  · apply (Submodule.baseChange_le_iff (A := ℂ)).mp
    apply (Submodule.map_le_map_iff_of_injective (exteriorBaseChange k).injective _ _).mp
    change exteriorHodgeClasses S.weight1.H S.weight1.isInternal m k ≤ _
    rw [f1575Power_hodgeClasses_eq_hodgeTwoPulledWeilSpan_aux hM hSU m k]
  · exact f1575PowerHodgeTwoPulledWeilSpan_le_rationalExteriorHodge_aux hM m k

end HodgeLean.Adapters
