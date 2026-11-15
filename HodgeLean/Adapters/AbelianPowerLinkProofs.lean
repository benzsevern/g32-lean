import HodgeLean.Adapters.PWTheorem42Eisenstein
import HodgeLean.Foundations.GeometricIntegralityC
import HodgeLean.Foundations.SegreProjective

/-! # The Powers flagship, G3 link: proof obligations

One `_aux` theorem per statement of `AbelianPowerLink.lean`, all open. The scope instances of
`A^r = g3_power A r` are found by instance search: `g3_grpObj`, `spec_g3_isCommMonObj_power`,
`spec_g3b_isIntegral_power`, `spec_g3_smooth_power`, `spec_g3c_isProjective_power`. HC no
distance; AV milestone no distance.
-/

noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open scoped CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.WeilPower
open HodgeLean.Foundations.Symplectic

namespace HodgeLean.Adapters

variable (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A] [IsIntegral A.left]
  [Smooth A.hom] [IsProjective A.hom]

/-! ### G2 at `A^r` -/

theorem spec_g3link_cohomologyMap_bijective_aux (r k : ℕ) :
    Function.Bijective ((g3_powerData A r).cohomologyMap k) := by
  exact spec_g2_cohomologyMap_bijective (g3_powerData A r) k

theorem spec_g3link_dim_eq_aux (r : ℕ) : dim (g3_power A r).left = r * dim A.left := by
  exact spec_g2_dim_eq (g3_powerData A r)

theorem spec_g3link_mem_rationalExteriorHodge_iff_aux (r p : ℕ)
    (v : ⋀[ℚ]^(2 * p) (HQ A 1 ⊗[ℚ] (Fin r → ℚ))) :
    letI := (finiteBetti_abelian A).finite 1
    v ∈ rationalExteriorHodge (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal r (2 * p) ↔
      ((g3_powerData A r).cohomologyMap (2 * p) v : H^(2 * p)(g3_power A r; ℚ)) ∈
        Hdg^p(g3_power A r; ℚ) := by
  exact spec_g2_mem_rationalExteriorHodge_iff (g3_powerData A r) p v

theorem spec_g3link_rationalExteriorHodge_map_eq_aux (r p : ℕ) :
    letI := (finiteBetti_abelian A).finite 1
    (rationalExteriorHodge (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal r (2 * p)).map
          ((g3_powerData A r).cohomologyMap (2 * p)) =
      Hdg^p(g3_power A r; ℚ) := by
  exact spec_g2_rationalExteriorHodge_map_eq (g3_powerData A r) p

theorem spec_g3link_cohomologyMap_zero_aux (r : ℕ) :
    (g3_powerData A r).cohomologyMap 0 (exteriorPower.ιMulti ℚ 0 Fin.elim0) =
      cupUnit (g3_power A r) := by
  exact spec_g2_cohomologyMap_zero (g3_powerData A r)

theorem spec_g3link_hodgeClasses_eq_bot_of_lt_aux (r p : ℕ) (hp : r * dim A.left < p) :
    Hdg^p(g3_power A r; ℚ) = ⊥ := by
  exact spec_g2_hodgeClasses_eq_bot_of_lt (g3_powerData A r) p hp

theorem spec_g3link_homPullback_pwSumMap_degree_aux {L : Type*} [Field L] [Algebra ℚ L] (r : ℕ)
    (θ : L →ₐ[ℚ] AbelianEnd0 A) (a : Fin r → pwOrder A θ) (k : ℕ) :
    homPullback ((g3_powerData A r).pwSumMap θ a) k ∘ₗ
        ((torusCohomology_cupProductOf A).cupWedgeEquiv k).toLinearMap =
      (g3_powerData A r).cohomologyMap k ∘ₗ
        exteriorPower.map k (pwPowerPullback A θ (fun i => (a i : L))) := by
  exact spec_g2_homPullback_pwSumMap_degree (g3_powerData A r) θ a k

/-! ### `r = 1`: agreement with `AbelianPowerData.one A` -/

theorem spec_g3link_h1Map_one_aux :
    (g3_powerData A 1).h1Map = homPullback (g3_proj A 1 0) 1 ∘ₗ powerOneFlatten A := by
  apply TensorProduct.ext'
  intro x c
  simp only [AbelianPowerData.h1Map, Fin.sum_univ_one, LinearMap.comp_apply,
    LinearEquiv.coe_coe, TensorProduct.rid_tmul, LinearMap.lTensor_tmul,
    LinearMap.proj_apply, powerOneFlatten]
  rw [show (g3_powerData A 1).proj 0 = g3_proj A 1 0 from rfl]
  simp

theorem spec_g3link_cohomologyMap_one_aux (k : ℕ) :
    (g3_powerData A 1).cohomologyMap k =
      homPullback (g3_proj A 1 0) k ∘ₗ (AbelianPowerData.one A).cohomologyMap k := by
  rw [AbelianPowerData.cohomologyMap, AbelianPowerData.cohomologyMap,
    spec_g3link_h1Map_one_aux, spec_g2_h1Map_one, exteriorPower.map_comp]
  conv_rhs => rw [spec_homPullback_eq_cupWedgeEquiv]
  apply LinearMap.ext
  intro w
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]

theorem spec_g3link_hodgeClasses_one_aux (p : ℕ) :
    (Hdg^p(A; ℚ)).map (homPullback (g3_proj A 1 0) (2 * p)) = Hdg^p(g3_power A 1; ℚ) := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    letI := spec_g3_isMonHom_proj A 1 0
    exact spec_homPullback_hodgeClasses (g3_proj A 1 0) p x hx
  · intro y hy
    letI := spec_g3_isMonHom_incl A 1 0
    refine ⟨homPullback (g3_incl A 1 0) (2 * p) y,
      spec_homPullback_hodgeClasses (g3_incl A 1 0) p y hy, ?_⟩
    have h : g3_proj A 1 0 ≫ g3_incl A 1 0 = 𝟙 (g3_power A 1) := by
      rw [(spec_g3_proj_incl_one A).1, (spec_g3_proj_incl_one A).2]
      exact Iso.hom_inv_id _
    rw [← LinearMap.comp_apply, ← spec_homPullback_comp, h, spec_homPullback_id,
      LinearMap.id_apply]

/-! ### F1 at `A^r` -/

variable {L : Type*} [Field L] [Algebra ℚ L]

theorem spec_g3link_generation_aux (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
    (hu : u ^ 2 = -algebraMap ℚ L 3) (hL : Algebra.adjoin ℚ {u} = ⊤) (pol : HQ A 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
    (hRos : IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf A) pol) (pwAction A θ u))
    (hGk : letI := (finiteBetti_abelian A).finite 1
      HodgeLieIsGk (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal
        (polarizationForm (torusCohomology_cupProductOf A) hη) (pwActionRange A θ)
        (pwAction A θ u))
    (r : ℕ) :
    letI := (finiteBetti_abelian A).finite 1
    ∀ p : ℕ, Hdg^p(g3_power A r; ℚ) = pwPowerSpan A θ u 3 hu
      (isWeilType_of_hodgeLieIsGk (by norm_num) (f1_weilAction A θ u 3 hu)
        (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
          (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ _ hGk)
      (g3_powerData A r) p := by
  exact pw_thm_4_2_generation A θ u hu hL pol hη hRos hGk (g3_powerData A r)

theorem spec_g3link_generation_cup_aux (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
    (hu : u ^ 2 = -algebraMap ℚ L 3) (hL : Algebra.adjoin ℚ {u} = ⊤) (pol : HQ A 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
    (hRos : IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf A) pol) (pwAction A θ u))
    (hGk : letI := (finiteBetti_abelian A).finite 1
      HodgeLieIsGk (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal
        (polarizationForm (torusCohomology_cupProductOf A) hη) (pwActionRange A θ)
        (pwAction A θ u))
    (r : ℕ) :
    letI := (finiteBetti_abelian A).finite 1
    ∀ p : ℕ, Hdg^p(g3_power A r; ℚ) = f1_pulledWeilCupSpan A θ u 3 hu
      (isWeilType_of_hodgeLieIsGk (by norm_num) (f1_weilAction A θ u 3 hu)
        (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
          (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ _ hGk)
      (g3_powerData A r) Hdg^1(g3_power A r; ℚ) p := by
  exact pw_thm_4_2_generation_cup A θ u hu hL pol hη hRos hGk (g3_powerData A r)

theorem spec_g3link_hdg_le_pulledWeilCupSpan_divisor_aux (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
    (hu : u ^ 2 = -algebraMap ℚ L 3) (hL : Algebra.adjoin ℚ {u} = ⊤) (pol : HQ A 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
    (hRos : IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf A) pol) (pwAction A θ u))
    (hGk : letI := (finiteBetti_abelian A).finite 1
      HodgeLieIsGk (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal
        (polarizationForm (torusCohomology_cupProductOf A) hη) (pwActionRange A θ)
        (pwAction A θ u))
    (h11 : LefschetzOneOneHyp) (r : ℕ) :
    letI := (finiteBetti_abelian A).finite 1
    ∀ p : ℕ, Hdg^p(g3_power A r; ℚ) ≤ f1_pulledWeilCupSpan A θ u 3 hu
      (isWeilType_of_hodgeLieIsGk (by norm_num) (f1_weilAction A θ u 3 hu)
        (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
          (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ _ hGk)
      (g3_powerData A r) (algebraicCycleClassSpan (g3_power A r) 1) p := by
  exact f1_hdg_le_pulledWeilCupSpan_divisor A θ u hu hL pol hη hRos hGk h11 (g3_powerData A r)

theorem spec_g3link_hc_aux (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L)
    (hu : u ^ 2 = -algebraMap ℚ L 3) (hL : Algebra.adjoin ℚ {u} = ⊤) (pol : HQ A 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
    (hRos : IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf A) pol) (pwAction A θ u))
    (hGk : letI := (finiteBetti_abelian A).finite 1
      HodgeLieIsGk (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal
        (polarizationForm (torusCohomology_cupProductOf A) hη) (pwActionRange A θ)
        (pwAction A θ u))
    (hWA : letI := (finiteBetti_abelian A).finite 1
      WeilClassesAlgebraic (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)
      (f1_weilAction A θ u 3 hu)
      (isWeilType_of_hodgeLieIsGk (by norm_num) (f1_weilAction A θ u 3 hu)
        (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
          (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)) _ _ hGk))
    (r : ℕ)
    (hPull : ∀ (a : Fin r → pwOrder A θ) (q : ℕ),
      (algebraicCycleClassSpan A q).map (homPullback ((g3_powerData A r).pwSumMap θ a) (2 * q)) ≤
        algebraicCycleClassSpan (g3_power A r) q)
    (hC9 : CycleClassMultiplicative (cupProductOf (g3_power A r))) (h11 : LefschetzOneOneHyp) :
    ∀ p : ℕ, Hdg^p(g3_power A r; ℚ) ≤ algebraicCycleClassSpan (g3_power A r) p := by
  exact pw_thm_4_2_hc A θ u hu hL pol hη hRos hGk hWA (g3_powerData A r) hPull hC9 h11

end HodgeLean.Adapters
