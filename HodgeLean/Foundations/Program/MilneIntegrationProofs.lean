import HodgeLean.Foundations.Program.MilneTensor
import HodgeLean.Foundations.Program.MilneDivisors
import HodgeLean.Foundations.Program.MilneIntegrationChecks

/-! # Auxiliary statements for Milne M3 -/

noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 200000
open scoped TensorProduct CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.Symplectic

namespace HodgeLean.Foundations.Program

theorem m3_wedgeQuotient_map {V : Type*} [AddCommGroup V] [Module ℂ V]
    (n : ℕ) (u : Module.End ℂ V) (t : ⨂[ℂ]^n V) :
    InvariantsExterior.wedgeQuotient n (SchurWeyl.tensorPow (Fin n) u t) =
      exteriorPower.map n u (InvariantsExterior.wedgeQuotient n t) := by
  induction t using PiTensorProduct.induction_on with
  | smul_tprod c v =>
    simp only [map_smul, SchurWeyl.tensorPow_tprod,
      InvariantsExterior.wedgeQuotient_tprod, exteriorPower.map_apply_ιMulti, Function.comp_def]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem m3_wedgeQuotient_permRep {V : Type*} [AddCommGroup V] [Module ℂ V]
    (n : ℕ) (σ : Equiv.Perm (Fin n)) (t : ⨂[ℂ]^n V) :
    InvariantsExterior.wedgeQuotient n (SchurWeyl.permRep ℂ V (Fin n) σ t) =
      (Equiv.Perm.sign σ : ℤ) • InvariantsExterior.wedgeQuotient n t := by
  suffices h : (InvariantsExterior.wedgeQuotient (K := ℂ) (M := V) n).comp
      (SchurWeyl.permRep ℂ V (Fin n) σ) =
      (Equiv.Perm.sign σ : ℤ) •
        (InvariantsExterior.wedgeQuotient (K := ℂ) (M := V) n) from
    LinearMap.congr_fun h t
  ext v
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
    SchurWeyl.permRep_tprod, InvariantsExterior.wedgeQuotient_tprod,
    LinearMap.smul_apply]
  simp only [← Function.comp_def, AlternatingMap.map_perm, Equiv.Perm.sign_symm,
    Units.smul_def]

theorem m3_power_cup_aux (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (r i j : ℕ)
    (v : ⋀[ℂ]^i (Fin r → ℂ ⊗[ℚ] HQ J 1))
    (w : ⋀[ℂ]^j (Fin r → ℂ ⊗[ℚ] HQ J 1)) :
    g32p_powerClass J r (i + j)
      (exteriorPower.wedge ℂ (Fin r → ℂ ⊗[ℚ] HQ J 1) i j v w) =
    (cupProductOf (g3_power J r)).cupC rfl
      (g32p_powerClass J r i v) (g32p_powerClass J r j w) := by
  have hm : exteriorPower.map (i + j) (g32p_powerOne J r)
      (exteriorPower.wedge ℂ _ i j v w) =
      exteriorPower.wedge ℂ _ i j
        (exteriorPower.map i (g32p_powerOne J r) v)
        (exteriorPower.map j (g32p_powerOne J r) w) := by
    apply Subtype.ext
    simp only [exteriorPower.coe_map, Symplectic.coe_wedge, map_mul]
  simp only [g32p_powerClass, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [hm]
  simpa only [f1575ExteriorCohomology_eq_baseChange] using (f1575ExteriorCohomology_wedge
    (torusCohomology_cupProductOf (g3_power J r)) i j _ _)

theorem m3_power_unit_aux (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (r : ℕ) :
    g32p_powerClass J r 0 (exteriorPower.ιMulti ℂ 0 Fin.elim0) =
      (1 : ℂ) ⊗ₜ[ℚ] unitClass (g3_power J r) := by
  let := (torusCohomology_cupProductOf (g3_power J r)).finite
  have he : (HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv 0).symm
      (exteriorPower.ιMulti ℂ 0 (Fin.elim0 : Fin 0 → ℂ ⊗[ℚ] HQ (g3_power J r) 1)) =
      (1 : ℂ) ⊗ₜ[ℚ] exteriorPower.ιMulti ℚ 0 Fin.elim0 := by
    apply (HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv 0).injective
    rw [LinearEquiv.apply_symm_apply,
      HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv_tmul,
      HodgeBlocks.complexifyWedge_ιMulti]
    congr 1
    exact Subsingleton.elim _ _
  simp only [g32p_powerClass, LinearMap.comp_apply, LinearEquiv.coe_coe, exteriorPower.map_apply_ιMulti]
  rw [show g32p_powerOne J r ∘ Fin.elim0 = Fin.elim0 from Subsingleton.elim _ _, he,
    LinearMap.baseChange_tmul, CupProduct.cupWedgeMap_zero]
  rfl

theorem m3_exterior_products_aux (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol))
    (hpos : PolarizationPositive (finiteBetti_abelian J) (spec_bettiDeRhamIso_abelian J)
      (hodgeDecomposition_of_abelian J) (torusCohomology_cupProductOf J) hη) (r n : ℕ) :
    (⨅ u ∈ g32p_lefschetz J pol,
      LinearMap.eqLocus (exteriorPower.map n (g32p_diag J u r)) LinearMap.id) =
    (m1b_products (m1b_fixed ((fun u => g32p_diag J u r) '' g32p_lefschetz J pol) 2) n).map (InvariantsExterior.wedgeQuotient n) := by
  rw [← m1b_centralizer_tensors J pol hη hpos r n]
  ext v
  simp only [Submodule.mem_iInf, LinearMap.mem_eqLocus, LinearMap.id_apply,
    Submodule.mem_map]
  constructor
  · intro hv
    refine ⟨m0_tensorLift J r n v, ?_, ?_⟩
    · simp only [m1b_fixed, Submodule.mem_iInf, LinearMap.mem_ker,
        LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
      rintro _ ⟨u, hu, rfl⟩
      exact (m0_tensor_lift_fixed J pol r n v).mp hv u hu
    · simp only [m0_tensorLift, LinearMap.smul_apply, map_smul,
        InvariantsExterior.wedgeQuotient_toTensorPower, smul_smul]
      rw [inv_mul_cancel₀ (by exact_mod_cast n.factorial_ne_zero), one_smul]
  · rintro ⟨t, ht, rfl⟩ u hu
    simp only [m1b_fixed, Submodule.mem_iInf, LinearMap.mem_ker,
      LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at ht
    rw [← m3_wedgeQuotient_map, ht _ ⟨u, hu, rfl⟩]

theorem m3_quadratic_image_aux (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol))
    (hpos : PolarizationPositive (finiteBetti_abelian J) (spec_bettiDeRhamIso_abelian J)
      (hodgeDecomposition_of_abelian J) (torusCohomology_cupProductOf J) hη) (r : ℕ) :
    ((m1b_fixed ((fun u => g32p_diag J u r) '' g32p_lefschetz J pol) 2)).map
      ((g32p_powerClass J r 2).comp (InvariantsExterior.wedgeQuotient 2)) ≤
      (algebraicCycleClassSpan (g3_power J r) 1).baseChange ℂ := by
  rw [← m2_power_divisors J pol hη hpos r]
  rintro x ⟨t, ht, rfl⟩
  refine ⟨InvariantsExterior.wedgeQuotient 2 t, ?_, rfl⟩
  change InvariantsExterior.wedgeQuotient 2 t ∈
    ⨅ u ∈ g32p_lefschetz J pol,
      LinearMap.eqLocus (exteriorPower.map 2 (g32p_diag J u r)) LinearMap.id
  simp only [Submodule.mem_iInf, LinearMap.mem_eqLocus, LinearMap.id_apply]
  change t ∈ m1b_fixed ((fun u => g32p_diag J u r) '' g32p_lefschetz J pol) 2 at ht
  simp only [m1b_fixed, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at ht
  intro u hu
  rw [← m3_wedgeQuotient_map, ht _ ⟨u, hu, rfl⟩]

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
theorem m3_products_algebraic_aux (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol))
    (hpos : PolarizationPositive (finiteBetti_abelian J) (spec_bettiDeRhamIso_abelian J)
      (hodgeDecomposition_of_abelian J) (torusCohomology_cupProductOf J) hη) (r p : ℕ) :
    (m1b_products (m1b_fixed ((fun u => g32p_diag J u r) '' g32p_lefschetz J pol) 2) (2 * p)).map
      ((g32p_powerClass J r (2 * p)).comp (InvariantsExterior.wedgeQuotient (2 * p))) ≤
      (algebraicCycleClassSpan (g3_power J r) p).baseChange ℂ := by
  induction p with
  | zero =>
    rw [algebraicCycleClassSpan_zero_eq_top_unconditional, Submodule.baseChange_top]
    exact le_top
  | succ p ih =>
    rintro x ⟨t, ht, rfl⟩
    simp only [LinearMap.comp_apply]
    change t ∈ Submodule.span ℂ _ at ht
    induction ht using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨σ, a, b, ha, hb, rfl⟩ := ht
      erw [m3_wedgeQuotient_permRep, map_zsmul,
        InvariantsExterior.wedgeQuotient_tensorAppend, m3_power_cup_aux]
      erw [← Int.cast_smul_eq_zsmul ℂ]
      apply Submodule.smul_mem
      have ha' : g32p_powerClass J r (2 * p)
          (InvariantsExterior.wedgeQuotient (2 * p) a) ∈
          (algebraicCycleClassSpan (g3_power J r) p).baseChange ℂ := by
        apply ih
        exact Submodule.mem_map.mpr ⟨a, ha, rfl⟩
      have hb' : g32p_powerClass J r 2 (InvariantsExterior.wedgeQuotient 2 b) ∈
          (algebraicCycleClassSpan (g3_power J r) 1).baseChange ℂ := by
        apply m3_quadratic_image_aux J pol hη hpos r
        exact Submodule.mem_map.mpr ⟨b, hb, rfl⟩
      have hmul := g32c_cupC_span (g3_power J r) p 1 (p + 1) rfl _ _ ha' hb'
      convert hmul using 1
    | zero =>
      rw [map_zero, map_zero]
      exact Submodule.zero_mem _
    | add a b ha hb hia hib =>
      rw [map_add, map_add]
      exact Submodule.add_mem _ hia hib
    | smul c a ha hia =>
      rw [map_smul, map_smul]
      exact Submodule.smul_mem _ c hia

theorem m3_milne_invariance_aux (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol))
    (hpos : PolarizationPositive (finiteBetti_abelian J) (spec_bettiDeRhamIso_abelian J)
      (hodgeDecomposition_of_abelian J) (torusCohomology_cupProductOf J) hη) :
    g32p_MilneInvariance J pol hη hpos := by
  refine ⟨fun r p => ?_⟩
  unfold g32p_invariants
  rw [m3_exterior_products_aux J pol hη hpos r (2 * p), ← Submodule.map_comp]
  exact m3_products_algebraic_aux J pol hη hpos r p

end HodgeLean.Foundations.Program
