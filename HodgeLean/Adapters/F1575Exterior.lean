import HodgeLean.RealDefs.WeilClasses
import HodgeLean.Foundations.WeilPowerClasses
import HodgeLean.Adapters.F1575WeilDescent

/-! # The single-copy exterior Hodge comparison for F-1575

The comparison uses C1, C2, C4, C7 and O5. In cohomological degree `2*p`,
the complex span of rational abstract Hodge classes maps exactly onto the
complexification of geometric `Hdg^p`.
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

section SingleCopy

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]

/-- Remove the one-dimensional rational multiplicity factor.

Source: constructed here for F-1575 step 3 from the canonical equivalence
`(Fin 1 → ℚ) ≃ ℚ`. -/
def f1575SingleCopy : (V ⊗[ℚ] (Fin 1 → ℚ)) ≃ₗ[ℚ] V :=
  (TensorProduct.congr (LinearEquiv.refl ℚ V)
    (LinearEquiv.funUnique (Fin 1) ℚ ℚ)).trans (TensorProduct.rid ℚ V)

example : (V ⊗[ℚ] (Fin 1 → ℚ)) ≃ₗ[ℚ] V := f1575SingleCopy

/-- Remove the complex multiplicity factor in the coordinates of `WeilPower`.

Source: constructed here for F-1575 step 3 by base change of the one-copy
multiplicity model. -/
def f1575SingleCopyComplex :
    (ℂ ⊗[ℚ] (V ⊗[ℚ] (Fin 1 → ℚ))) ≃ₗ[ℂ] (ℂ ⊗[ℚ] V) :=
  (powerBaseChange 1).trans
    ((TensorProduct.congr (LinearEquiv.refl ℂ _)
      (LinearEquiv.funUnique (Fin 1) ℂ ℂ)).trans (TensorProduct.rid ℂ _))

example : (ℂ ⊗[ℚ] (V ⊗[ℚ] (Fin 1 → ℚ))) ≃ₗ[ℂ] (ℂ ⊗[ℚ] V) :=
  f1575SingleCopyComplex

omit [Module.Finite ℚ V] in
theorem f1575SingleCopyComplex_pure (x : ℂ ⊗[ℚ] V) (u : Fin 1 → ℂ) :
    f1575SingleCopyComplex ((powerBaseChange 1).symm (x ⊗ₜ[ℂ] u)) = u 0 • x := by
  simp [f1575SingleCopyComplex, LinearEquiv.funUnique]

omit [Module.Finite ℚ V] in
theorem f1575SingleCopyComplex_tmul (a : ℂ) (v : V ⊗[ℚ] (Fin 1 → ℚ)) :
    f1575SingleCopyComplex (a ⊗ₜ[ℚ] v) = a ⊗ₜ[ℚ] f1575SingleCopy v := by
  induction v using TensorProduct.inductionOn with
  | tmul x u =>
    simp [f1575SingleCopyComplex, f1575SingleCopy, powerBaseChange, multiplicityEquiv,
      Module.Basis.equivFun_apply, Module.Basis.baseChange_repr_tmul,
      LinearEquiv.funUnique, TensorProduct.smul_tmul', Algebra.smul_def]
  | add v w hv hw => simp only [TensorProduct.tmul_add, map_add, hv, hw]

/-- The single-copy exterior comparison, with target in the package's convention.

Source: constructed here for F-1575 step 3 by applying the exterior-power
functor and the standard exterior base-change equivalence. -/
def f1575SingleCopyExterior (k : ℕ) :
    (⋀[ℂ]^k (ℂ ⊗[ℚ] (V ⊗[ℚ] (Fin 1 → ℚ)))) ≃ₗ[ℂ]
      (ℂ ⊗[ℚ] ⋀[ℚ]^k V) :=
  (exteriorEquiv k f1575SingleCopyComplex).trans
    (HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv k).symm

example (k : ℕ) :
    (⋀[ℂ]^k (ℂ ⊗[ℚ] (V ⊗[ℚ] (Fin 1 → ℚ)))) ≃ₗ[ℂ] (ℂ ⊗[ℚ] ⋀[ℚ]^k V) :=
  f1575SingleCopyExterior k

theorem f1575SingleCopyExterior_pure (k : ℕ) (x : Fin k → ℂ ⊗[ℚ] V)
    (u : Fin k → (Fin 1 → ℂ)) :
    f1575SingleCopyExterior k
      (exteriorPower.ιMulti ℂ k (fun i => (powerBaseChange 1).symm (x i ⊗ₜ[ℂ] u i))) =
      (HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv k).symm
        (exteriorPower.ιMulti ℂ k (fun i => u i 0 • x i)) := by
  unfold f1575SingleCopyExterior
  rw [LinearEquiv.trans_apply]
  apply congrArg (HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv (V := V) k).symm
  change exteriorPower.map k (f1575SingleCopyComplex (V := V)).toLinearMap
    (exteriorPower.ιMulti ℂ k _) = _
  rw [exteriorPower.map_apply_ιMulti]
  congr 1
  funext i
  exact f1575SingleCopyComplex_pure (x i) (u i)

/-- The abstract single-copy pieces are exactly the package's exterior pieces. -/
theorem f1575SingleCopyExterior_map_hodge (M : HodgeBlocks.QHodgeStructure 1 V)
    (k : ℕ) (pq : ℤ × ℤ) :
    (exteriorHodge M.H 1 k pq).map (f1575SingleCopyExterior k).toLinearMap =
      M.exteriorPowerH (V := V) k pq := by
  rw [exteriorPowerH_eq_wedgePiece, exteriorHodge, Submodule.map_span]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨ps, x, u, hx, hps, rfl⟩, rfl⟩
    rw [LinearEquiv.coe_coe, f1575SingleCopyExterior_pure]
    apply Submodule.subset_span
    refine ⟨ps, (fun i => u i 0 • x i), ?_, fun i => (M.H (ps i)).smul_mem _ (hx i), rfl⟩
    simpa [HodgeBlocks.totalBidegree, prod_mk_sum] using hps
  · apply Submodule.span_le.mpr
    rintro _ ⟨ps, x, hps, hx, rfl⟩
    apply Submodule.subset_span
    refine ⟨exteriorPower.ιMulti ℂ k
      (fun i => (powerBaseChange 1).symm (x i ⊗ₜ[ℂ] (1 : Fin 1 → ℂ))),
      ⟨ps, x, (fun _ => 1), hx, ?_, rfl⟩, ?_⟩
    · simpa [HodgeBlocks.totalBidegree, prod_mk_sum] using hps
    · simp only [LinearEquiv.coe_coe, f1575SingleCopyExterior_pure, Pi.one_apply, one_smul]

/-- The exterior comparison is defined over the rationals. -/
theorem f1575SingleCopyExterior_complexify (k : ℕ)
    (v : ⋀[ℚ]^k (V ⊗[ℚ] (Fin 1 → ℚ))) :
    f1575SingleCopyExterior k (exteriorComplexify k v) =
      (1 : ℂ) ⊗ₜ[ℚ] exteriorPower.map k (f1575SingleCopy (V := V)).toLinearMap v := by
  have hh : ((f1575SingleCopyExterior (V := V) k).toLinearMap.restrictScalars ℚ).comp
      (exteriorComplexify k) =
      (TensorProduct.mk ℚ ℂ (⋀[ℚ]^k V) 1).comp
        (exteriorPower.map k (f1575SingleCopy (V := V)).toLinearMap) := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro x
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      LinearMap.restrictScalars_apply, LinearEquiv.coe_coe,
      exteriorComplexify_ιMulti, exteriorPower.map_apply_ιMulti, TensorProduct.mk_apply]
    apply (HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv (V := V) k).injective
    simp only [f1575SingleCopyExterior, LinearEquiv.trans_apply,
      LinearEquiv.apply_symm_apply, HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv_tmul,
      HodgeBlocks.complexifyWedge_ιMulti]
    change exteriorPower.map k (f1575SingleCopyComplex (V := V)).toLinearMap
      (exteriorPower.ιMulti ℂ k _) = _
    rw [exteriorPower.map_apply_ιMulti]
    congr 1
    funext i
    exact f1575SingleCopyComplex_tmul 1 (x i)
  exact LinearMap.congr_fun hh v

/-- In even degree the diagonal sum is just its unique diagonal Hodge piece. -/
theorem f1575_diagonal_eq (M : HodgeBlocks.QHodgeStructure 1 V) (p : ℕ) :
    (⨆ q : ℤ, M.exteriorPowerH (V := V) (2 * p) (q, q)) =
      M.exteriorPowerH (V := V) (2 * p) (p, p) := by
  apply le_antisymm
  · refine iSup_le fun q => ?_
    by_cases h : q = p
    · subst q; exact le_rfl
    · rw [M.exteriorPowerH_supported (V := V) (2 * p) (q, q) (by push_cast; omega)]
      exact bot_le
  · exact le_iSup (fun q : ℤ => M.exteriorPowerH (V := V) (2 * p) (q, q)) (p : ℤ)

/-- Rational single-copy Hodge classes, in the package's exterior convention. -/
theorem f1575_mem_rationalExteriorHodge_iff (M : HodgeBlocks.QHodgeStructure 1 V)
    (p : ℕ) (v : ⋀[ℚ]^(2 * p) (V ⊗[ℚ] (Fin 1 → ℚ))) :
    v ∈ rationalExteriorHodge M.H M.isInternal 1 (2 * p) ↔
      (1 : ℂ) ⊗ₜ[ℚ] exteriorPower.map (2 * p) (f1575SingleCopy (V := V)).toLinearMap v ∈
        M.exteriorPowerH (V := V) (2 * p) (p, p) := by
  rw [mem_rationalExteriorHodge_iff]
  have hm : (⨆ q : ℤ, exteriorHodge M.H 1 (2 * p) (q, q)).map
      (f1575SingleCopyExterior (V := V) (2 * p)).toLinearMap =
      M.exteriorPowerH (V := V) (2 * p) (p, p) := by
    rw [Submodule.map_iSup]
    simp_rw [f1575SingleCopyExterior_map_hodge]
    exact f1575_diagonal_eq M p
  rw [← hm, ← f1575SingleCopyExterior_complexify, Submodule.mem_map_equiv,
    LinearEquiv.symm_apply_apply]

end SingleCopy

/-- The actual C7 comparison for one copy, in complex exterior coordinates.

Source: constructed here for F-1575 step 3 from C7 (`TorusCohomology`) and
the single-copy exterior comparison. -/
def f1575SingleCopyCohomology (hT : TorusCohomology μ) (k : ℕ) :
    letI := hT.finite
    (⋀[ℂ]^k (ℂ ⊗[ℚ] (HQ X 1 ⊗[ℚ] (Fin 1 → ℚ)))) ≃ₗ[ℂ]
      (ℂ ⊗[ℚ] HQ X k) :=
  letI := hT.finite
  letI := (finiteBetti_of_torusCohomology hT).finite k
  (f1575SingleCopyExterior k).trans
    (HodgeBlocks.QHodgeStructure.complexificationCongr (V := ⋀[ℚ]^k (HQ X 1))
      (W := HQ X k) (hT.cupWedgeEquiv k))

example (hT : TorusCohomology μ) (k : ℕ) :
    letI := hT.finite
    (⋀[ℂ]^k (ℂ ⊗[ℚ] (HQ X 1 ⊗[ℚ] (Fin 1 → ℚ)))) ≃ₗ[ℂ] (ℂ ⊗[ℚ] HQ X k) :=
  f1575SingleCopyCohomology hT k

/-- Under O5, the abstract single-copy Hodge pieces agree with the geometric pieces. -/
theorem f1575SingleCopyCohomology_map_hodge (hF : FiniteBetti X)
    (hB : BettiDeRhamIso X) (hD : HodgeDecomposition X) (hT : TorusCohomology μ)
    (hC : CupFiltered X μ) (k : ℕ) (pq : ℤ × ℤ) :
    letI := hT.finite
    (exteriorHodge (abelianVarietyCohomologyOf hF hB hD hT).weight1.H 1 k pq).map
      (f1575SingleCopyCohomology hT k).toLinearMap = cohomologyHodgePiece X k pq := by
  let := hT.finite
  let := (finiteBetti_of_torusCohomology hT).finite k
  change (exteriorHodge _ 1 k pq).map
    ((HodgeBlocks.QHodgeStructure.complexificationCongr (V := ⋀[ℚ]^k (HQ X 1))
      (W := HQ X k) (hT.cupWedgeEquiv k)).toLinearMap.comp
        (f1575SingleCopyExterior k).toLinearMap) = _
  rw [Submodule.map_comp]
  rw [f1575SingleCopyExterior_map_hodge]
  change ((cohomologyHodgeStructure hF hB hD 1).exteriorPowerH (V := HQ X 1) k pq).map
    (HodgeBlocks.QHodgeStructure.complexificationCongr (V := ⋀[ℚ]^k (HQ X 1))
      (W := HQ X k) (hT.cupWedgeEquiv k)).toLinearMap = _
  rw [← comap_cohomologyHodgePiece_eq_exteriorPowerH hF hB hD hT hC k pq]
  exact Submodule.map_comap_eq_of_surjective
    (HodgeBlocks.QHodgeStructure.complexificationCongr (V := ⋀[ℚ]^k (HQ X 1))
      (W := HQ X k) (hT.cupWedgeEquiv k)).surjective _

/-- The rational single-copy cup-wedge map.

Source: constructed here for F-1575 step 3 from C7's cup-wedge map after
removing the one-dimensional multiplicity factor. -/
def f1575SingleCopyCohomologyQ (μ : CupProduct X) (k : ℕ) :
    (⋀[ℚ]^k (HQ X 1 ⊗[ℚ] (Fin 1 → ℚ))) →ₗ[ℚ] HQ X k :=
  (μ.cupWedgeMap k).comp (exteriorPower.map k (f1575SingleCopy (V := HQ X 1)).toLinearMap)

example (μ : CupProduct X) (k : ℕ) :
    (⋀[ℚ]^k (HQ X 1 ⊗[ℚ] (Fin 1 → ℚ))) →ₗ[ℚ] HQ X k :=
  f1575SingleCopyCohomologyQ μ k

theorem f1575SingleCopyCohomology_complexify (hT : TorusCohomology μ) (k : ℕ)
    (v : ⋀[ℚ]^k (HQ X 1 ⊗[ℚ] (Fin 1 → ℚ))) :
    letI := hT.finite
    f1575SingleCopyCohomology hT k (exteriorComplexify k v) =
      (1 : ℂ) ⊗ₜ[ℚ] f1575SingleCopyCohomologyQ μ k v := by
  let := hT.finite
  let := (finiteBetti_of_torusCohomology hT).finite k
  simp only [f1575SingleCopyCohomology, LinearEquiv.trans_apply,
    f1575SingleCopyExterior_complexify,
    HodgeBlocks.QHodgeStructure.complexificationCongr_tmul,
    TorusCohomology.cupWedgeEquiv_apply]
  rfl

/-- Rational Hodge classes correspond under C7 and O5, with cohomological degree `2*p`. -/
theorem f1575_rationalHodge_map_eq (hF : FiniteBetti X) (hB : BettiDeRhamIso X)
    (hD : HodgeDecomposition X) (hT : TorusCohomology μ) (hC : CupFiltered X μ) (p : ℕ) :
    letI := hT.finite
    (rationalExteriorHodge (abelianVarietyCohomologyOf hF hB hD hT).weight1.H
      (abelianVarietyCohomologyOf hF hB hD hT).weight1.isInternal 1 (2 * p)).map
        (f1575SingleCopyCohomologyQ μ (2 * p)) = Hdg^p(X; ℚ) := by
  let := hT.finite
  have hi (v : ⋀[ℚ]^(2 * p) (HQ X 1 ⊗[ℚ] (Fin 1 → ℚ))) :
      v ∈ rationalExteriorHodge (abelianVarietyCohomologyOf hF hB hD hT).weight1.H
        (abelianVarietyCohomologyOf hF hB hD hT).weight1.isInternal 1 (2 * p) ↔
      f1575SingleCopyCohomologyQ μ (2 * p) v ∈ Hdg^p(X; ℚ) := by
    rw [f1575_mem_rationalExteriorHodge_iff]
    simpa only [HodgeBlocks.IsHodgeClass, HodgeBlocks.WeilAction.weightCast_H,
      HodgeBlocks.QHodgeStructure.exteriorPower, HodgeBlocks.complexify_apply,
      f1575SingleCopyCohomologyQ, LinearMap.comp_apply] using
      isHodgeClass_exteriorPower_iff hF hB hD hT hC p
        (exteriorPower.map (2 * p) (f1575SingleCopy (V := HQ X 1)).toLinearMap v)
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    exact (hi v).mp hv
  · intro y hy
    obtain ⟨w, hw⟩ := (hT.bijective (2 * p)).surjective y
    obtain ⟨v, hv⟩ := exteriorPower.map_surjective (n := 2 * p)
      (f1575SingleCopy (V := HQ X 1)).surjective w
    have he : f1575SingleCopyCohomologyQ μ (2 * p) v = y := by
      simp [f1575SingleCopyCohomologyQ, hv, hw]
    exact ⟨v, (hi v).mpr (he.symm ▸ hy), he⟩

/-- F-1575 step 2's complex span is exactly the complexification of geometric `Hdg^p`. -/
theorem f1575_exteriorHodgeClasses_map_eq (hF : FiniteBetti X) (hB : BettiDeRhamIso X)
    (hD : HodgeDecomposition X) (hT : TorusCohomology μ) (hC : CupFiltered X μ) (p : ℕ) :
    letI := hT.finite
    (exteriorHodgeClasses (abelianVarietyCohomologyOf hF hB hD hT).weight1.H
      (abelianVarietyCohomologyOf hF hB hD hT).weight1.isInternal 1 (2 * p)).map
        (f1575SingleCopyCohomology hT (2 * p)).toLinearMap = (Hdg^p(X; ℚ)).baseChange ℂ := by
  let := hT.finite
  have he : (f1575SingleCopyCohomology hT (2 * p)).toLinearMap.comp
      (exteriorBaseChange (V := HQ X 1 ⊗[ℚ] (Fin 1 → ℚ)) (2 * p)).toLinearMap =
      (f1575SingleCopyCohomologyQ μ (2 * p)).baseChange ℂ := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a v =>
      rw [LinearMap.comp_apply, exteriorBaseChange_eq_lift, LinearMap.liftBaseChange_tmul,
        map_smul, LinearEquiv.coe_coe, f1575SingleCopyCohomology_complexify,
        LinearMap.baseChange_tmul]
      simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [exteriorHodgeClasses, ← Submodule.map_comp, he, ← f1575_baseChange_map,
    f1575_rationalHodge_map_eq hF hB hD hT hC p]
  rfl

end HodgeLean.Adapters
