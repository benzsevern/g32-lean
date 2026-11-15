import HodgeLean.Adapters.AbelianCMDataDefs
import HodgeLean.Adapters.AbelianHomPullback
import HodgeLean.Adapters.AbelianEndomorphisms3
import HodgeLean.Adapters.HodgeDegreeOneAbelian
import HodgeLean.Adapters.PowersVocabulary

/-! # CM data from endomorphisms, stage G4: proof obligations

One `_aux` theorem per statement of `AbelianCMData.lean`, all open. HC no distance; AV milestone
no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open scoped CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.WeilPower

namespace HodgeLean.Adapters

variable (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A] [IsIntegral A.left]
  [Smooth A.hom] [IsProjective A.hom]

theorem spec_g4_abelianEnd0Action_tmul_aux (q : ℚ) (f : AbelianEnd A) :
    abelianEnd0Action A (q ⊗ₜ[ℤ] f) = MulOpposite.op (q • abelianEndAction A f) := by
  rw [abelianEnd0Action, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply,
    RingHom.toIntAlgHom_apply, ← Algebra.smul_def, MulOpposite.op_smul]
  rfl

theorem spec_g4_abelianEnd0Action_injective_aux : Function.Injective (abelianEnd0Action A) := by
  obtain ⟨ρ, hρ, hinj⟩ := spec_abelianEnd0Action A
  have h : ∀ x, ρ x = abelianEnd0Action A x := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul q f =>
      have hq : q ⊗ₜ[ℤ] f = q • ((1 : ℚ) ⊗ₜ[ℤ] f) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hq, map_smul, map_smul, hρ, spec_g4_abelianEnd0Action_tmul_aux, one_smul]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have : (ρ : AbelianEnd0 A → _) = abelianEnd0Action A := funext h
  rw [← this]
  exact hinj

theorem spec_g4_abelianEnd0Action_mem_hodgeEndH1_aux (x : AbelianEnd0 A) :
    (abelianEnd0Action A x).unop ∈ hodgeEndH1 A := by
  induction x using TensorProduct.inductionOn with
  | tmul q f =>
    rw [spec_g4_abelianEnd0Action_tmul_aux, MulOpposite.unop_op]
    exact Subalgebra.smul_mem _ (spec_abelianEndAction_hodge A f) q
  | add x y hx hy =>
    rw [map_add, MulOpposite.unop_add]
    exact Subalgebra.add_mem _ hx hy

omit [IsCommMonObj A] in
theorem spec_g4_cohomologyHodgePiece_one_eq_aux :
    cohomologyHodgePiece A 1 = latticeHodgePieces A := by
  have hinj : Function.Injective (bettiDeRhamHQ A 1) :=
    (spec_bettiDeRhamIso_abelian A).bijective 1 |>.1
  have hbot : (⊥ : Submodule ℂ H_dR^((1 : ℕ) : ℤ)(A)).comap (bettiDeRhamHQ A 1) = ⊥ := by
    rw [Submodule.comap_bot, LinearMap.ker_eq_bot.mpr hinj]
  have hF1 := spec_comap_hodgeFiltration_one_eq A
  have hC1 := spec_comap_conjHodgeFiltration_one_eq_of_eq A hF1
  funext ⟨p, q⟩
  unfold cohomologyHodgePiece latticeHodgePieces
  by_cases hpq : p + q = ((1 : ℕ) : ℤ)
  · simp only [hpq, ↓reduceIte]
    simp only [Nat.cast_one] at hpq
    by_cases h10 : (p, q) = ((1 : ℤ), (0 : ℤ))
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h10
      simp only [↓reduceIte]
      rw [hodgePiece, conjHodgeFiltrationComplexSubmodule,
        hodgeFiltration_eq_top_of_nonpos A le_rfl, Submodule.comap_top, inf_top_eq]
      exact hF1
    · simp only [h10, ↓reduceIte]
      by_cases h01 : (p, q) = ((0 : ℤ), (1 : ℤ))
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h01
        simp only [↓reduceIte]
        rw [hodgePiece, hodgeFiltration_eq_top_of_nonpos A le_rfl, top_inf_eq]
        exact hC1
      · simp only [h01, ↓reduceIte]
        rcases le_or_gt p 0 with hp | hp
        · have hq : ((1 : ℕ) : ℤ) < q := by
            rcases hp.lt_or_eq with hp | rfl
            · simp only [Nat.cast_one]; lia
            · exact absurd (by simp only [zero_add] at hpq; rw [hpq]) h01
          rw [hodgePiece, conjHodgeFiltration_eq_bot_of_lt A hq, inf_bot_eq, hbot]
        · have hp' : ((1 : ℕ) : ℤ) < p := by
            rcases (Int.add_one_le_iff.mpr hp).lt_or_eq with hp | hp
            · simp only [Nat.cast_one]; lia
            · exact absurd (by
                have : p = 1 := by lia
                subst this; have : q = 0 := by lia
                rw [this]) h10
          rw [hodgePiece, hodgeFiltration_eq_bot_of_lt A hp', bot_inf_eq, hbot]
  · simp only [hpq, ↓reduceIte]
    have h10 : (p, q) ≠ ((1 : ℤ), (0 : ℤ)) := by
      rintro h; obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact hpq (by simp)
    have h01 : (p, q) ≠ ((0 : ℤ), (1 : ℤ)) := by
      rintro h; obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact hpq (by simp)
    simp only [h10, h01, ↓reduceIte]

variable {L : Type*} [Field L] [Algebra ℚ L]

theorem spec_g4_pwAction_map_le_aux (θ : L →ₐ[ℚ] AbelianEnd0 A) (x : L) (pq : ℤ × ℤ) :
    (cohomologyHodgePiece A 1 pq).map ((pwAction A θ x).baseChange ℂ) ≤
      cohomologyHodgePiece A 1 pq := by
  have hx := spec_g4_abelianEnd0Action_mem_hodgeEndH1_aux A (θ x)
  rw [spec_g4_cohomologyHodgePiece_one_eq_aux]
  unfold latticeHodgePieces
  split_ifs
  · exact hx.1
  · exact hx.2
  · rw [Submodule.map_bot]

theorem spec_g4_tmul_eq_iff_pwOrderEnd_aux (θ : L →ₐ[ℚ] AbelianEnd0 A) (a : pwOrder A θ)
    (f : AbelianEnd A) : (1 : ℚ) ⊗ₜ[ℤ] f = θ a ↔ f = pwOrderEnd A θ a := by
  refine ⟨fun h => ?_, fun h => h ▸ (a.2.choose_spec : (1 : ℚ) ⊗ₜ[ℤ] pwOrderEnd A θ a = θ a)⟩
  have h' : (1 : ℚ) ⊗ₜ[ℤ] f = (1 : ℚ) ⊗ₜ[ℤ] pwOrderEnd A θ a :=
    h.trans (a.2.choose_spec : (1 : ℚ) ⊗ₜ[ℤ] pwOrderEnd A θ a = θ a).symm
  have h'' := congrArg (abelianEnd0Action A) h'
  rw [spec_g4_abelianEnd0Action_tmul_aux, spec_g4_abelianEnd0Action_tmul_aux, one_smul,
    one_smul] at h''
  exact spec_abelianEndAction_injective A (MulOpposite.op_injective h'')

theorem spec_g4_abelianEndAction_pwOrderEnd_aux (θ : L →ₐ[ℚ] AbelianEnd0 A) (a : pwOrder A θ) :
    abelianEndAction A (pwOrderEnd A θ a) = pwAction A θ a := by
  change _ = (abelianEnd0Action A (θ a)).unop
  rw [← (a.2.choose_spec : (1 : ℚ) ⊗ₜ[ℤ] pwOrderEnd A θ a = θ a),
    spec_g4_abelianEnd0Action_tmul_aux, one_smul, MulOpposite.unop_op]
  rfl

set_option linter.unusedSectionVars false in
theorem spec_g4_exists_nat_mul_mem_pwOrder_aux (θ : L →ₐ[ℚ] AbelianEnd0 A) (a : L) :
    ∃ N : ℕ, 0 < N ∧ (N : L) * a ∈ pwOrder A θ := by
  let j := TensorProduct.mk ℤ ℚ (AbelianEnd A) 1
  have : IsLocalizedModule (nonZeroDivisors ℤ) j :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors ℤ) ℚ j).mpr
      (TensorProduct.isBaseChange ℤ (AbelianEnd A) ℚ)
  obtain ⟨⟨m, s⟩, hms⟩ := IsLocalizedModule.mk'_surjective (nonZeroDivisors ℤ) j (θ a)
  have hcancel := IsLocalizedModule.mk'_cancel' j m s
  have hs : (s : ℤ) * a ∈ pwOrder A θ := by
    refine ⟨m, ?_⟩
    change j m = _
    rw [← hcancel, Submonoid.smul_def]
    simp only [Function.uncurry_apply_pair] at hms
    rw [hms, ← map_zsmul, zsmul_eq_mul]
  have hs0 : (s : ℤ) ≠ 0 := nonZeroDivisors.coe_ne_zero s
  refine ⟨(s : ℤ).natAbs, Int.natAbs_pos.mpr hs0, ?_⟩
  rcases Int.natAbs_eq (s : ℤ) with h | h
  · rw [h, Int.cast_natCast] at hs
    exact hs
  · rw [h, Int.cast_neg, Int.cast_natCast, neg_mul] at hs
    simpa using (pwOrder A θ).neg_mem hs

theorem spec_g4_pwOrder_eq_top_of_dim_eq_zero_aux (θ : L →ₐ[ℚ] AbelianEnd0 A)
    (h0 : dim A.left = 0) : pwOrder A θ = ⊤ := by
  have := (finiteBetti_abelian A).finite 1
  obtain ⟨hHol, hAnti⟩ := spec_complexH1_dimension A
  rw [h0] at hHol hAnti
  have hsplit := (spec_complexH1_split A).1
  rw [Submodule.finrank_eq_zero.mp hHol, Submodule.finrank_eq_zero.mp hAnti, bot_sup_eq] at hsplit
  have hC : Subsingleton (ℂ ⊗[ℚ] HQ A 1) :=
    (Submodule.subsingleton_iff ℂ).mp (subsingleton_of_bot_eq_top hsplit)
  have hQ : Subsingleton (HQ A 1) := by
    have h1 := Module.finrank_baseChange (R := ℂ) (S := ℚ) (M' := HQ A 1)
    rw [Module.finrank_zero_of_subsingleton] at h1
    exact Module.finrank_zero_iff.mp h1.symm
  have hE : Subsingleton (Module.End ℚ (HQ A 1))ᵐᵒᵖ := inferInstance
  refine eq_top_iff.mpr fun a _ => ⟨0, ?_⟩
  exact spec_g4_abelianEnd0Action_injective_aux A (Subsingleton.elim _ _)

section Power

variable {A} {Y : Over (Spec ↧ℂ)} [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left]
  [Smooth Y.hom] [IsProjective Y.hom] {r : ℕ}

omit [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom] [IsIntegral Y.left] [Smooth Y.hom]
  [IsProjective Y.hom] in
theorem spec_g4_isMonHom_sumMap_aux (P : AbelianPowerData A Y r) (a : Fin r → AbelianEnd A) :
    IsMonHom (P.sumMap a) := by
  unfold AbelianPowerData.sumMap
  induction (Finset.univ : Finset (Fin r)) using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Hom.one_def]; infer_instance
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Hom.mul_def]
    have := P.proj_isMonHom i
    infer_instance

theorem spec_g4_homPullback_sumMap_aux (P : AbelianPowerData A Y r) (a : Fin r → AbelianEnd A) :
    homPullback (P.sumMap a) 1 = ∑ i, homPullback (P.proj i) 1 ∘ₗ abelianEndAction A (a i) := by
  unfold AbelianPowerData.sumMap
  induction (Finset.univ : Finset (Fin r)) using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.sum_empty, spec_homPullback_one]
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, spec_homPullback_mul, ih,
      spec_homPullback_comp]
    exact congrArg (· + _) rfl

set_option linter.unusedSectionVars false in
omit [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom] in
theorem spec_g4_eq_zero_of_powerData_zero_aux (P : AbelianPowerData A Y 0) (y : HQ Y 1) :
    y = 0 := by
  have h := P.sum_proj_incl
  rw [Finset.univ_eq_empty, Finset.prod_empty] at h
  have h1 := spec_homPullback_id (X := Y) 1
  rw [← h, spec_homPullback_one] at h1
  simpa using (LinearMap.congr_fun h1 y).symm

end Power

/-- `pwPowerPullback` on a vector, as a sum over the basis of `ℚ^r`. -/
theorem g4_pwPowerPullback_apply (θ : L →ₐ[ℚ] AbelianEnd0 A) {r : ℕ} (a : Fin r → L)
    (x : HQ A 1) :
    pwPowerPullback A θ a x = ∑ i, pwAction A θ (a i) x ⊗ₜ[ℚ] (Pi.single i 1 : Fin r → ℚ) := by
  simp [pwPowerPullback, cmPowerPullback]

/-- Scaling the coefficients by `N : ℕ` scales `pwPowerPullback` by `N`. -/
theorem g4_pwPowerPullback_natCast_mul (θ : L →ₐ[ℚ] AbelianEnd0 A) {r : ℕ} (a : Fin r → L)
    (N : ℕ) : pwPowerPullback A θ (fun i => (N : L) * a i) = (N : ℚ) • pwPowerPullback A θ a := by
  ext x
  rw [LinearMap.smul_apply, g4_pwPowerPullback_apply, g4_pwPowerPullback_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_natCast, Module.End.mul_apply, Module.End.natCast_apply, ← TensorProduct.smul_tmul',
    Nat.cast_smul_eq_nsmul]

/-- `⋀^n (c • f) = c ^ n • ⋀^n f`. -/
theorem g4_exteriorPower_map_smul {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W]
    [Module ℚ W] (n : ℕ) (c : ℚ) (f : V →ₗ[ℚ] W) :
    exteriorPower.map n (c • f) = c ^ n • exteriorPower.map n f := by
  ext m
  simp only [LinearMap.compAlternatingMap_apply, exteriorPower.map_apply_ιMulti,
    LinearMap.smul_apply]
  have : (c • f) ∘ m = fun i => c • f (m i) := rfl
  rw [this, AlternatingMap.map_smul_univ (exteriorPower.ιMulti ℚ n) (fun _ => c), Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  rfl

theorem spec_g4_span_pwOrder_eq_aux (θ : L →ₐ[ℚ] AbelianEnd0 A) (r : ℕ) {n : ℕ}
    (W : Submodule ℚ (⋀[ℚ]^n (HQ A 1))) :
    Submodule.span ℚ {y | ∃ a : Fin r → L, (∀ i, a i ∈ pwOrder A θ) ∧
        ∃ w ∈ W, exteriorPower.map n (pwPowerPullback A θ a) w = y} =
      Submodule.span ℚ {y | ∃ a : Fin r → L,
        ∃ w ∈ W, exteriorPower.map n (pwPowerPullback A θ a) w = y} := by
  refine le_antisymm (Submodule.span_mono fun y ⟨a, _, hy⟩ => ⟨a, hy⟩) ?_
  rw [Submodule.span_le]
  rintro y ⟨a, w, hw, rfl⟩
  choose M hM0 hM using fun i => spec_g4_exists_nat_mul_mem_pwOrder_aux A θ (a i)
  set N := ∏ i, M i with hN
  have hN0 : 0 < N := Finset.prod_pos fun i _ => hM0 i
  have hmem : ∀ i, (N : L) * a i ∈ pwOrder A θ := by
    intro i
    have hd : M i ∣ N := Finset.dvd_prod_of_mem M (Finset.mem_univ i)
    obtain ⟨k, hk⟩ := hd
    rw [hk, Nat.cast_mul, mul_comm (M i : L), mul_assoc]
    exact Subring.mul_mem _ (natCast_mem _ k) (hM i)
  have hsub : exteriorPower.map n (pwPowerPullback A θ fun i => (N : L) * a i) w ∈
      Submodule.span ℚ {y | ∃ a : Fin r → L, (∀ i, a i ∈ pwOrder A θ) ∧
        ∃ w ∈ W, exteriorPower.map n (pwPowerPullback A θ a) w = y} :=
    Submodule.subset_span ⟨_, hmem, w, hw, rfl⟩
  rw [g4_pwPowerPullback_natCast_mul, g4_exteriorPower_map_smul, LinearMap.smul_apply] at hsub
  have hc : ((N : ℚ) ^ n) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hN0.ne')
  have := Submodule.smul_mem _ ((N : ℚ) ^ n)⁻¹ hsub
  rwa [inv_smul_smul₀ hc] at this

theorem spec_g4_pwPowerPullback_eq_weilPowerPullback_aux (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
    {r : ℕ} (p s : Fin r → ℚ) :
    pwPowerPullback A θ (fun i => algebraMap ℚ L (p i) + algebraMap ℚ L (s i) * u) =
      weilPowerPullback (pwAction A θ u) p s := by
  ext x
  rw [g4_pwPowerPullback_apply]
  change _ = x ⊗ₜ[ℚ] p + pwAction A θ u x ⊗ₜ[ℚ] s
  conv_rhs => rw [← Finset.univ_sum_single p, ← Finset.univ_sum_single s,
    TensorProduct.tmul_sum, TensorProduct.tmul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hsingle : ∀ c : ℚ, (Pi.single i c : Fin r → ℚ) = c • Pi.single i 1 := fun c => by
    rw [← Pi.single_smul', smul_eq_mul, mul_one]
  rw [map_add, map_mul, AlgHom.commutes, AlgHom.commutes, LinearMap.add_apply,
    Module.End.mul_apply, Module.algebraMap_end_apply, Module.algebraMap_end_apply,
    TensorProduct.add_tmul, hsingle (p i), hsingle (s i), TensorProduct.tmul_smul,
    TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul']

theorem spec_g4_pwActionRange_eq_adjoin_aux (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
    (hu : Algebra.adjoin ℚ {u} = ⊤) :
    pwActionRange A θ = Algebra.adjoin ℚ {pwAction A θ u} := by
  rw [pwActionRange, ← AlgHom.map_adjoin_singleton, hu, Algebra.map_top]

end HodgeLean.Adapters
