import HodgeLean.Adapters.AbelianPowerHodgeDefs
import HodgeLean.Adapters.AbelianCMData
import HodgeLean.Adapters.AbelianHomPullbackDegrees
import HodgeLean.Adapters.AbelianHodgeDischarge
import HodgeLean.Adapters.F1575PowersOne

/-! # Powers, from the exterior model to `HQ(Y)`, stage G2: proof obligations

One `_aux` theorem per statement of `AbelianPowerHodge.lean`, all open. HC no distance; AV
milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.WeilPower

namespace HodgeLean.Adapters

section Power

variable {A Y : Over (Spec ↧ℂ)} [GrpObj A] [IsIntegral A.left] [Smooth A.hom]
  [IsProjective A.hom] [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left] [Smooth Y.hom]
  [IsProjective Y.hom] {r : ℕ}

theorem spec_g2_h1Inv_comp_h1Map_aux (P : AbelianPowerData A Y r) :
    P.h1Inv ∘ₗ P.h1Map = LinearMap.id := by
  apply TensorProduct.ext'
  intro x c
  simp only [LinearMap.comp_apply, AbelianPowerData.h1Inv, LinearMap.sum_apply,
    AbelianPowerData.h1Map, map_sum, TensorProduct.rid_tmul, LinearMap.lTensor_tmul,
    LinearMap.proj_apply, LinearEquiv.coe_coe]
  rw [Finset.sum_comm]
  simp only [map_smul, LinearMap.flip_apply, TensorProduct.mk_apply,
    LinearMap.id_apply]
  have hp (i j : Fin r) :
      homPullback (P.incl i) 1 (homPullback (P.proj j) 1 x) =
        homPullback (P.incl i ≫ P.proj j) 1 x := by
    rw [spec_homPullback_comp, LinearMap.comp_apply]
  simp_rw [hp, P.incl_proj]
  have hpb (i j : Fin r) :
      homPullback (if i = j then 𝟙 A else 1) 1 x = if i = j then x else 0 := by
    split_ifs <;> simp [spec_homPullback_id, spec_homPullback_one]
  simp_rw [hpb]
  have hsum (i : Fin r) :
      (∑ j, c j • (if i = j then x else 0) ⊗ₜ[ℚ] (Pi.single i 1 : Fin r → ℚ)) =
        c i • x ⊗ₜ[ℚ] (Pi.single i 1 : Fin r → ℚ) := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [hji.symm]
    · simp
  simp_rw [hsum]
  simp_rw [← TensorProduct.tmul_smul]
  rw [← TensorProduct.tmul_sum]
  congr 1
  rw [← Finset.univ_sum_single c]
  apply Finset.sum_congr rfl
  intro i _
  ext j
  by_cases h : j = i
  · subst j
    simp
  · simp [Pi.single_eq_of_ne h]

set_option maxHeartbeats 400000 in
theorem spec_g2_h1Map_comp_h1Inv_aux (P : AbelianPowerData A Y r) :
    P.h1Map ∘ₗ P.h1Inv = LinearMap.id := by
  ext y
  simp [AbelianPowerData.h1Map, AbelianPowerData.h1Inv]
  have hdiag (i : Fin r) :
      (∑ j, (Pi.single j (1 : ℚ) : Fin r → ℚ) i •
        homPullback (P.proj i) 1 (homPullback (P.incl j) 1 y)) =
        homPullback (P.proj i) 1 (homPullback (P.incl i) 1 y) := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Pi.single_eq_of_ne hji.symm]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  simp_rw [hdiag]
  have hprod :
      homPullback (∏ i, P.proj i ≫ P.incl i) 1 =
        ∑ i, homPullback (P.proj i ≫ P.incl i) 1 := by
    induction (Finset.univ : Finset (Fin r)) using Finset.induction_on with
    | empty => rw [Finset.prod_empty, Finset.sum_empty, spec_homPullback_one]
    | insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, spec_homPullback_mul, ih]
  calc
    ∑ i, homPullback (P.proj i) 1 (homPullback (P.incl i) 1 y) =
        (∑ i, homPullback (P.proj i ≫ P.incl i) 1) y := by
          rw [LinearMap.sum_apply]
          apply Finset.sum_congr rfl
          intro i _
          rw [spec_homPullback_comp, LinearMap.comp_apply]
    _ = homPullback (∏ i, P.proj i ≫ P.incl i) 1 y := by rw [hprod]
    _ = y := by rw [P.sum_proj_incl, spec_homPullback_id, LinearMap.id_apply]

theorem spec_g2_dim_eq_aux (P : AbelianPowerData A Y r) : dim Y.left = r * dim A.left := by
  let := (torusCohomology_cupProductOf A).finite
  let e : HQ A 1 ⊗[ℚ] (Fin r → ℚ) ≃ₗ[ℚ] HQ Y 1 := LinearEquiv.ofLinearMap P.h1Map P.h1Inv
    (spec_g2_h1Map_comp_h1Inv_aux P) (spec_g2_h1Inv_comp_h1Map_aux P)
  have h := e.finrank_eq
  rw [Module.finrank_tensorProduct, Module.finrank_fin_fun] at h
  have hA := (torusCohomology_cupProductOf A).finrank_eq
  have hY := (torusCohomology_cupProductOf Y).finrank_eq
  rw [hA, hY] at h
  apply Nat.eq_of_mul_eq_mul_left (n := 2) (by omega)
  simpa [mul_assoc, mul_comm, mul_left_comm] using h.symm

private theorem h1Map_baseChange_powerBaseChange (P : AbelianPowerData A Y r)
    (x : ℂ ⊗[ℚ] HQ A 1) (u : Fin r → ℂ) :
    P.h1Map.baseChange ℂ ((powerBaseChange r).symm (x ⊗ₜ[ℂ] u)) =
      ∑ i, u i • (homPullback (P.proj i) 1).baseChange ℂ x := by
  obtain ⟨q, rfl⟩ := (multiplicityEquiv r).surjective u
  induction x using TensorProduct.inductionOn with
  | tmul a v =>
    induction q using TensorProduct.inductionOn with
    | tmul b c =>
      simp only [powerBaseChange, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
        TensorProduct.congr_symm_tmul, LinearEquiv.refl_symm, LinearEquiv.refl_apply,
        LinearEquiv.symm_apply_apply]
      rw [TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul]
      simp [AbelianPowerData.h1Map, multiplicityEquiv]
      rw [TensorProduct.tmul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [TensorProduct.tmul_smul]
      rw [TensorProduct.smul_tmul']
      congr 1
      simp [smul_eq_mul, mul_comm]
    | add q₁ q₂ h₁ h₂ => simp only [TensorProduct.tmul_add, map_add, h₁, h₂, Pi.add_apply,
        add_smul, Finset.sum_add_distrib]
  | add x₁ x₂ h₁ h₂ => simp only [TensorProduct.add_tmul, map_add, h₁, h₂,
      map_add, smul_add, Finset.sum_add_distrib]

private theorem powerBaseChange_h1Inv_baseChange (P : AbelianPowerData A Y r)
    (y : ℂ ⊗[ℚ] HQ Y 1) :
    powerBaseChange r (P.h1Inv.baseChange ℂ y) =
      ∑ i, (homPullback (P.incl i) 1).baseChange ℂ y ⊗ₜ[ℂ]
        (Pi.single i 1 : Fin r → ℂ) := by
  induction y using TensorProduct.inductionOn with
  | tmul a y =>
    simp [AbelianPowerData.h1Inv, powerBaseChange, multiplicityEquiv,
      TensorProduct.tmul_sum, Module.Basis.equivFun_apply]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    ext j
    by_cases h : j = i
    · subst j
      simp
    · simp [Pi.single_eq_of_ne h]
  | add y₁ y₂ h₁ h₂ =>
    simp only [map_add, h₁, h₂, TensorProduct.add_tmul, Finset.sum_add_distrib]

theorem spec_g2_h1Map_hodgePiece_aux (P : AbelianPowerData A Y r) (pq : ℤ × ℤ) :
    (powerWeightOnePiece (cohomologyHodgePiece A 1) r pq).map (P.h1Map.baseChange ℂ) =
      cohomologyHodgePiece Y 1 pq := by
  apply le_antisymm
  · rintro _ ⟨z, hz, rfl⟩
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨x, hx, u, rfl⟩ := hz
      rw [h1Map_baseChange_powerBaseChange]
      have hproj (i : Fin r) :
          (homPullback (P.proj i) 1).baseChange ℂ x ∈ cohomologyHodgePiece Y 1 pq := by
        let := P.proj_isMonHom i
        exact spec_homPullback_hodgePiece_one (P.proj i) pq (Submodule.mem_map_of_mem hx)
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
        (hproj i)
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx
  · intro y hy
    have hinv : P.h1Inv.baseChange ℂ y ∈
        powerWeightOnePiece (cohomologyHodgePiece A 1) r pq := by
      have heq : P.h1Inv.baseChange ℂ y =
          ∑ i, (powerBaseChange r).symm
            ((homPullback (P.incl i) 1).baseChange ℂ y ⊗ₜ[ℂ]
              (Pi.single i 1 : Fin r → ℂ)) := by
        apply (powerBaseChange r).injective
        rw [powerBaseChange_h1Inv_baseChange, map_sum]
        simp
      rw [heq]
      apply Submodule.sum_mem
      intro i _
      apply Submodule.subset_span
      refine ⟨_, ?_, _, rfl⟩
      let := P.incl_isMonHom i
      exact spec_homPullback_hodgePiece_one (P.incl i) pq (Submodule.mem_map_of_mem hy)
    refine ⟨P.h1Inv.baseChange ℂ y, hinv, ?_⟩
    have h := congrArg (LinearMap.baseChange ℂ) (spec_g2_h1Map_comp_h1Inv_aux P)
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_id] at h
    exact LinearMap.congr_fun h y

theorem spec_g2_cohomologyMap_bijective_aux (P : AbelianPowerData A Y r) (k : ℕ) :
    Function.Bijective (P.cohomologyMap k) := by
  have hsurj : Function.Surjective P.h1Map := fun y =>
    ⟨P.h1Inv y, by rw [← LinearMap.comp_apply, spec_g2_h1Map_comp_h1Inv_aux, LinearMap.id_apply]⟩
  exact ((torusCohomology_cupProductOf Y).cupWedgeEquiv k).bijective.comp
    ⟨exteriorPower.map_injective P.h1Inv (spec_g2_h1Inv_comp_h1Map_aux P),
      exteriorPower.map_surjective hsurj⟩

/-- The complexified model map, read through `exteriorBaseChange`, is `⋀^k Φ_ℂ` followed by the
complexified torus isomorphism of `Y`, read through `exteriorBaseChange` of `Y`. -/
theorem g2_cohomologyMap_baseChange_eq (P : AbelianPowerData A Y r) (k : ℕ) :
    letI := (finiteBetti_abelian A).finite 1
    letI := (torusCohomology_cupProductOf Y).finite
    letI := (finiteBetti_abelian Y).finite k
    (P.cohomologyMap k).baseChange ℂ ∘ₗ (exteriorBaseChange k).symm.toLinearMap =
      (HodgeBlocks.QHodgeStructure.complexificationCongr (V := ⋀[ℚ]^k (HQ Y 1))
          (W := HQ Y k) ((torusCohomology_cupProductOf Y).cupWedgeEquiv k)).toLinearMap ∘ₗ
        (exteriorBaseChange (V := HQ Y 1) k).symm.toLinearMap ∘ₗ
          exteriorPower.map k (P.h1Map.baseChange ℂ) := by
  let := (finiteBetti_abelian A).finite 1
  let := (torusCohomology_cupProductOf Y).finite
  let := (finiteBetti_abelian Y).finite k
  have key : ((P.cohomologyMap k).baseChange ℂ ∘ₗ (exteriorBaseChange k).symm.toLinearMap) ∘ₗ
        (exteriorBaseChange k).toLinearMap =
      ((HodgeBlocks.QHodgeStructure.complexificationCongr (V := ⋀[ℚ]^k (HQ Y 1))
          (W := HQ Y k) ((torusCohomology_cupProductOf Y).cupWedgeEquiv k)).toLinearMap ∘ₗ
        (exteriorBaseChange (V := HQ Y 1) k).symm.toLinearMap ∘ₗ
          exteriorPower.map k (P.h1Map.baseChange ℂ)) ∘ₗ (exteriorBaseChange k).toLinearMap := by
    refine TensorProduct.AlgebraTensorModule.ext fun c y => ?_
    rw [← mul_one c, ← smul_eq_mul, ← TensorProduct.smul_tmul', map_smul, map_smul]
    congr 1
    have hq : (((P.cohomologyMap k).baseChange ℂ ∘ₗ (exteriorBaseChange k).symm.toLinearMap) ∘ₗ
          (exteriorBaseChange k).toLinearMap).restrictScalars ℚ ∘ₗ
          TensorProduct.mk ℚ ℂ (⋀[ℚ]^k (HQ A 1 ⊗[ℚ] (Fin r → ℚ))) 1 =
        (((HodgeBlocks.QHodgeStructure.complexificationCongr (V := ⋀[ℚ]^k (HQ Y 1))
          (W := HQ Y k) ((torusCohomology_cupProductOf Y).cupWedgeEquiv k)).toLinearMap ∘ₗ
          (exteriorBaseChange (V := HQ Y 1) k).symm.toLinearMap ∘ₗ
          exteriorPower.map k (P.h1Map.baseChange ℂ)) ∘ₗ
          (exteriorBaseChange k).toLinearMap).restrictScalars ℚ ∘ₗ
          TensorProduct.mk ℚ ℂ (⋀[ℚ]^k (HQ A 1 ⊗[ℚ] (Fin r → ℚ))) 1 := by
      refine exteriorPower.linearMap_ext (AlternatingMap.ext fun v => ?_)
      simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
        LinearMap.restrictScalars_apply, TensorProduct.mk_apply, LinearEquiv.coe_coe,
        LinearMap.baseChange_tmul, exteriorBaseChange_one_ιMulti,
        exteriorPower.map_apply_ιMulti, Function.comp_def]
      rw [← exteriorBaseChange_one_ιMulti, ← exteriorBaseChange_one_ιMulti,
        LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, LinearMap.baseChange_tmul,
        HodgeBlocks.QHodgeStructure.complexificationCongr_tmul, AbelianPowerData.cohomologyMap,
        LinearMap.comp_apply, exteriorPower.map_apply_ιMulti]
      rfl
    exact LinearMap.congr_fun hq y
  refine LinearMap.ext fun z => ?_
  have h := LinearMap.congr_fun key ((exteriorBaseChange k).symm z)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h
  exact h

theorem spec_g2_cohomologyMap_hodgePiece_aux (P : AbelianPowerData A Y r) (k : ℕ)
    (pq : ℤ × ℤ) :
    letI := (finiteBetti_abelian A).finite 1
    (exteriorHodge (cohomologyHodgePiece A 1) r k pq).map
        ((P.cohomologyMap k).baseChange ℂ ∘ₗ (exteriorBaseChange k).symm.toLinearMap) =
      cohomologyHodgePiece Y k pq := by
  let := (finiteBetti_abelian A).finite 1
  let := (torusCohomology_cupProductOf Y).finite
  let := (finiteBetti_abelian Y).finite k
  rw [g2_cohomologyMap_baseChange_eq P k]
  set CC := HodgeBlocks.QHodgeStructure.complexificationCongr (V := ⋀[ℚ]^k (HQ Y 1))
    (W := HQ Y k) ((torusCohomology_cupProductOf Y).cupWedgeEquiv k)
  set G := CC.toLinearMap ∘ₗ (exteriorBaseChange (V := HQ Y 1) k).symm.toLinearMap ∘ₗ
    exteriorPower.map k (P.h1Map.baseChange ℂ)
  have hinv : P.h1Inv.baseChange ℂ ∘ₗ P.h1Map.baseChange ℂ = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, spec_g2_h1Inv_comp_h1Map_aux, LinearMap.baseChange_id]
  have hsurjC : Function.Surjective (P.h1Map.baseChange ℂ) := fun y =>
    ⟨P.h1Inv.baseChange ℂ y, by
      rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, spec_g2_h1Map_comp_h1Inv_aux,
        LinearMap.baseChange_id, LinearMap.id_apply]⟩
  have hinj : Function.Injective G :=
    CC.injective.comp ((exteriorBaseChange (V := HQ Y 1) k).symm.injective.comp
      (exteriorPower.map_injective _ hinv))
  have hsurj : Function.Surjective G :=
    CC.surjective.comp ((exteriorBaseChange (V := HQ Y 1) k).symm.surjective.comp
      (exteriorPower.map_surjective hsurjC))
  have hle : ∀ pq, (exteriorHodge (cohomologyHodgePiece A 1) r k pq).map G ≤
      cohomologyHodgePiece Y k pq := by
    intro pq
    rw [exteriorHodge, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨ps, x, u, hx, hps, rfl⟩, rfl⟩
    have hy : ∀ i, P.h1Map.baseChange ℂ ((powerBaseChange r).symm (x i ⊗ₜ[ℂ] u i)) ∈
        (cohomologyHodgeStructure (finiteBetti_abelian Y) (spec_bettiDeRhamIso_abelian Y)
          (hodgeDecomposition_of_abelian Y) 1).H (ps i) := fun i => by
      change _ ∈ cohomologyHodgePiece Y 1 (ps i)
      rw [← spec_g2_h1Map_hodgePiece_aux P (ps i)]
      exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨x i, hx i, u i, rfl⟩)
    have hw := HodgeBlocks.WeilAction.exteriorPower_ιMulti_mem_exteriorPowerH_map
      (cohomologyHodgeStructure (finiteBetti_abelian Y) (spec_bettiDeRhamIso_abelian Y)
        (hodgeDecomposition_of_abelian Y) 1) k pq ps _
      (by simpa [HodgeBlocks.totalBidegree, prod_mk_sum] using hps) hy
    have hw' := (Submodule.mem_map_equiv _).mp hw
    have hc := exteriorPowerH_le_comap_cohomologyHodgePiece (finiteBetti_abelian Y)
      (spec_bettiDeRhamIso_abelian Y) (hodgeDecomposition_of_abelian Y)
      (torusCohomology_cupProductOf Y) (cupFiltered_cupProductOf_of_abelian Y) k pq hw'
    simp only [G, LinearMap.comp_apply, LinearEquiv.coe_coe, exteriorPower.map_apply_ιMulti,
      Function.comp_def]
    exact hc
  refine le_antisymm (hle pq) fun y hy => ?_
  obtain ⟨x, rfl⟩ := hsurj y
  exact Submodule.mem_map_of_mem (mem_of_map_mem_of_iSupIndep_of_map_le
    (iSup_exteriorHodge _ (abelianWeightOneHodgeStructure A).isInternal r k)
    (cohomologyHodgeStructure (finiteBetti_abelian Y) (spec_bettiDeRhamIso_abelian Y)
      (hodgeDecomposition_of_abelian Y) k).isInternal.submodule_iSupIndep
    (g := id) Function.injective_id hinj hle hy)

theorem spec_g2_mem_rationalExteriorHodge_iff_aux (P : AbelianPowerData A Y r) (p : ℕ)
    (v : ⋀[ℚ]^(2 * p) (HQ A 1 ⊗[ℚ] (Fin r → ℚ))) :
    letI := (finiteBetti_abelian A).finite 1
    v ∈ rationalExteriorHodge (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal r (2 * p) ↔
      (P.cohomologyMap (2 * p) v : H^(2 * p)(Y; ℚ)) ∈ Hdg^p(Y; ℚ) := by
  let := (finiteBetti_abelian A).finite 1
  let e : ⋀[ℚ]^(2 * p) (HQ A 1 ⊗[ℚ] (Fin r → ℚ)) ≃ₗ[ℚ] HQ Y (2 * p) :=
    LinearEquiv.ofBijective _ (spec_g2_cohomologyMap_bijective_aux P (2 * p))
  let F := (exteriorBaseChange (V := HQ A 1 ⊗[ℚ] (Fin r → ℚ)) (2 * p)).symm.trans
    (e.baseChange ℚ ℂ _ _)
  have hF : F.toLinearMap = (P.cohomologyMap (2 * p)).baseChange ℂ ∘ₗ
      (exteriorBaseChange (V := HQ A 1 ⊗[ℚ] (Fin r → ℚ)) (2 * p)).symm.toLinearMap := rfl
  have hc : F (exteriorComplexify (2 * p) v) = (1 : ℂ) ⊗ₜ[ℚ] P.cohomologyMap (2 * p) v := by
    have h : exteriorComplexify (2 * p) v = exteriorBaseChange (2 * p) ((1 : ℂ) ⊗ₜ[ℚ] v) := by
      change _ = (exteriorBaseChange _).toLinearMap _
      rw [exteriorBaseChange_eq_lift, LinearMap.liftBaseChange_tmul, one_smul]
    rw [h, ← LinearEquiv.coe_toLinearMap, hF, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, LinearMap.baseChange_tmul]
  have hm : (⨆ q : ℤ, exteriorHodge (cohomologyHodgePiece A 1) r (2 * p) (q, q)).map
      F.toLinearMap = cohomologyHodgePiece Y (2 * p) ((p : ℤ), (p : ℤ)) := by
    rw [Submodule.map_iSup, hF]
    simp_rw [spec_g2_cohomologyMap_hodgePiece_aux P (2 * p)]
    apply le_antisymm
    · refine iSup_le fun q => ?_
      by_cases h : q = p
      · subst q; exact le_rfl
      · rw [cohomologyHodgePiece, ite_eq_right (by push_cast; omega)]
        exact bot_le
    · exact le_iSup (fun q : ℤ => cohomologyHodgePiece Y (2 * p) (q, q)) (p : ℤ)
  rw [mem_rationalExteriorHodge_iff, mem_hodgeClasses_iff_tmul_mem, ← hm, ← hc,
    Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]
  rfl

theorem spec_g2_rationalExteriorHodge_map_eq_aux (P : AbelianPowerData A Y r) (p : ℕ) :
    letI := (finiteBetti_abelian A).finite 1
    (rationalExteriorHodge (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal r (2 * p)).map (P.cohomologyMap (2 * p)) =
      Hdg^p(Y; ℚ) := by
  let := (finiteBetti_abelian A).finite 1
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    exact (spec_g2_mem_rationalExteriorHodge_iff_aux P p v).mp hv
  · intro y hy
    obtain ⟨v, rfl⟩ := (spec_g2_cohomologyMap_bijective_aux P (2 * p)).2 y
    exact ⟨v, (spec_g2_mem_rationalExteriorHodge_iff_aux P p v).mpr hy, rfl⟩

theorem spec_g2_cohomologyMap_zero_aux (P : AbelianPowerData A Y r) :
    P.cohomologyMap 0 (exteriorPower.ιMulti ℚ 0 Fin.elim0) = cupUnit Y := by
  rw [AbelianPowerData.cohomologyMap, LinearMap.comp_apply, exteriorPower.map_apply_ιMulti,
    LinearEquiv.coe_coe, TorusCohomology.cupWedgeEquiv_apply, CupProduct.cupWedgeMap_ιMulti,
    CupProduct.cupMulti_zero]
  rfl

theorem spec_g2_hodgeClasses_eq_bot_of_lt_aux (P : AbelianPowerData A Y r) (p : ℕ)
    (hp : r * dim A.left < p) : Hdg^p(Y; ℚ) = ⊥ := by
  have hT := torusCohomology_cupProductOf Y
  let := hT.finite
  have hdim := spec_g2_dim_eq_aux P
  have hsub : Subsingleton (⋀[ℚ]^(2 * p) (HQ Y 1)) :=
    exteriorPower.subsingleton_of_span_eq_top_of_card_lt (Module.finBasis ℚ (HQ Y 1))
      (Module.finBasis ℚ (HQ Y 1)).span_eq (2 * p) (by
        rw [Nat.card_eq_fintype_card, Fintype.card_fin, hT.finrank_eq, hdim]
        omega)
  have hs : Subsingleton (HQ Y (2 * p)) := (hT.cupWedgeEquiv (2 * p)).symm.toEquiv.subsingleton
  exact eq_bot_iff.2 fun x _ => (Submodule.mem_bot ℚ).2 (@Subsingleton.elim _ hs x 0)

variable [IsCommMonObj A] {L : Type*} [Field L] [Algebra ℚ L]

theorem spec_g2_homPullback_pwSumMap_aux (P : AbelianPowerData A Y r)
    (θ : L →ₐ[ℚ] AbelianEnd0 A) (a : Fin r → pwOrder A θ) :
    homPullback (P.pwSumMap θ a) 1 = P.h1Map ∘ₗ pwPowerPullback A θ (fun i => (a i : L)) := by
  apply LinearMap.ext
  intro x
  simp only [AbelianPowerData.pwSumMap, spec_g4_homPullback_sumMap,
    spec_g4_abelianEndAction_pwOrderEnd, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.sum_apply, pwPowerPullback, cmPowerPullback, map_sum,
    AbelianPowerData.h1Map, LinearMap.flip_apply, TensorProduct.mk_apply,
    LinearMap.lTensor_tmul, LinearMap.proj_apply, LinearEquiv.coe_coe,
    TensorProduct.rid_tmul, Pi.single_apply, ite_smul, one_smul, zero_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i (fun j _ hj => by rw [ite_eq_right hj, map_zero])
    (fun h => absurd (Finset.mem_univ i) h), ite_eq_left rfl]

theorem spec_g2_homPullback_pwSumMap_degree_aux (P : AbelianPowerData A Y r)
    (θ : L →ₐ[ℚ] AbelianEnd0 A) (a : Fin r → pwOrder A θ) (k : ℕ) :
    homPullback (P.pwSumMap θ a) k ∘ₗ
        ((torusCohomology_cupProductOf A).cupWedgeEquiv k).toLinearMap =
      P.cohomologyMap k ∘ₗ exteriorPower.map k (pwPowerPullback A θ (fun i => (a i : L))) := by
  rw [spec_homPullback_eq_cupWedgeEquiv, spec_g2_homPullback_pwSumMap_aux, AbelianPowerData.cohomologyMap,
    exteriorPower.map_comp]
  apply LinearMap.ext
  intro w
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]

end Power

variable (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom]
  [IsProjective A.hom]

theorem spec_g2_h1Map_one_aux : (AbelianPowerData.one A).h1Map = powerOneFlatten A := by
  apply TensorProduct.ext'
  intro x c
  simp only [AbelianPowerData.h1Map, Fin.sum_univ_one, LinearMap.comp_apply,
    LinearEquiv.coe_coe, TensorProduct.rid_tmul, LinearMap.lTensor_tmul,
    LinearMap.proj_apply, powerOneFlatten]
  rw [show (AbelianPowerData.one A).proj 0 = 𝟙 A from rfl, spec_homPullback_id,
    LinearMap.id_apply]
  simp

omit [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom] in
theorem spec_g2_not_isMonHom_const_aux (Y : Over (Spec ↧ℂ)) [GrpObj Y]
    (x : 𝟙_ (Over (Spec ↧ℂ)) ⟶ A) (hx : x ≠ η[A]) : ¬ IsMonHom (toUnit Y ≫ x) := by
  intro h
  apply hx
  calc
    x = 𝟙 _ ≫ x := (Category.id_comp x).symm
    _ = (η[Y] ≫ toUnit Y) ≫ x := by rw [toUnit_unique (η[Y] ≫ toUnit Y) (𝟙 _)]
    _ = η[Y] ≫ (toUnit Y ≫ x) := Category.assoc _ _ _
    _ = η[A] := h.one_hom

end HodgeLean.Adapters
