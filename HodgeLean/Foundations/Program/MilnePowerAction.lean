import HodgeLean.Foundations.Program.MilnePowerBlocks
import HodgeLean.Foundations.Program.MilnePowerGrading
import HodgeLean.Foundations.Program.MilneDivisorsGroup
import HodgeLean.Foundations.Program.MilneDivisorsPowers

noncomputable section
set_option maxHeartbeats 200000
open scoped TensorProduct CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.Symplectic
namespace HodgeLean.Foundations.Program

def m2_powerAction (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (r : ℕ)
    (u : Module.End ℂ (ℂ ⊗[ℚ] HQ J 1)) :
    Module.End ℂ (ℂ ⊗[ℚ] HQ (g3_power J r) 1) :=
  g32p_powerOne J r ∘ₗ g32p_diag J u r ∘ₗ m2_powerOneInv J r

theorem m2_powerAction_comp_powerOne (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (r : ℕ)
    (u : Module.End ℂ (ℂ ⊗[ℚ] HQ J 1)) :
    m2_powerAction J r u ∘ₗ g32p_powerOne J r =
      g32p_powerOne J r ∘ₗ g32p_diag J u r := by
  simp only [m2_powerAction, LinearMap.comp_assoc, m2_powerOneInv_comp, LinearMap.comp_id]

theorem m2_powerAction_incl (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (r : ℕ)
    (u : Module.End ℂ (ℂ ⊗[ℚ] HQ J 1)) (i : Fin r)
    (x : ℂ ⊗[ℚ] HQ (g3_power J r) 1) :
    (homPullback (g3_incl J r i) 1).baseChange ℂ (m2_powerAction J r u x) =
      u ((homPullback (g3_incl J r i) 1).baseChange ℂ x) := by
  have h : m2_powerOneInv J r ∘ₗ m2_powerAction J r u =
      g32p_diag J u r ∘ₗ m2_powerOneInv J r := by
    simp only [m2_powerAction, ← LinearMap.comp_assoc, m2_powerOneInv_comp, LinearMap.id_comp]
  exact congrArg (fun v => v i) (LinearMap.congr_fun h x)


theorem m2_powerAction_grading (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (r : ℕ) :
    m2_powerAction J r (m2_hodgeGrading J) = m2_hodgeGrading (g3_power J r) := by
  apply LinearMap.ext
  intro x
  obtain ⟨v, rfl⟩ := (m2_powerOne_bijective J r).2 x
  have h := LinearMap.congr_fun (m2_powerAction_comp_powerOne J r (m2_hodgeGrading J)) v
  exact h.trans (LinearMap.congr_fun (m2_powerOne_grading J r) v)


theorem m2_powerOne_single (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (r : ℕ) (i : Fin r)
    (x : ℂ ⊗[ℚ] HQ J 1) :
    g32p_powerOne J r (Pi.single i x) = (homPullback (g3_proj J r i) 1).baseChange ℂ x := by
  classical
  simp [g32p_powerOne, Pi.single_apply, apply_ite]


theorem m2_powerClass_eq_rational_iff (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (r : ℕ)
    (d : HQ (g3_power J r) 2)
    (v : ⋀[ℂ]^2 (Fin r → ℂ ⊗[ℚ] HQ J 1)) :
    g32p_powerClass J r 2 v = (1 : ℂ) ⊗ₜ[ℚ] d ↔
      exteriorPower.map 2 (g32p_powerOne J r) v = HodgeBlocks.complexifyWedge 2
        (polarizationVec (torusCohomology_cupProductOf (g3_power J r)) d) := by
  let hT := torusCohomology_cupProductOf (g3_power J r)
  letI := hT.finite
  let q := ((cupProductOf (g3_power J r)).cupWedgeMap 2).baseChange ℂ ∘ₗ
    (HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv 2).symm.toLinearMap
  have hq : Function.Injective q :=
    ((hT.cupWedgeEquiv 2).baseChange ℚ ℂ _ _).injective.comp
      (HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv 2).symm.injective
  have he : q (HodgeBlocks.complexifyWedge 2 (polarizationVec hT d)) =
      (1 : ℂ) ⊗ₜ[ℚ] d := by
    change ((cupProductOf (g3_power J r)).cupWedgeMap 2).baseChange ℂ
      ((HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv 2).symm
        (HodgeBlocks.complexifyWedge 2 (polarizationVec hT d))) = _
    rw [← HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv_tmul,
      LinearEquiv.symm_apply_apply, LinearMap.baseChange_tmul,
      cupWedgeMap_polarizationVec]
  constructor
  · intro h
    apply hq
    exact h.trans he.symm
  · intro h
    change q (exteriorPower.map 2 (g32p_powerOne J r) v) = _
    rw [h]
    exact he


theorem m2_rational_invariants_iff_power_fixed (J : Over (Spec ↧ℂ)) [GrpObj J]
    [IsCommMonObj J] [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    (pol : HQ J 2) (r : ℕ) (d : HQ (g3_power J r) 2) :
    (1 : ℂ) ⊗ₜ[ℚ] d ∈ g32p_invariants J pol r 2 ↔
      ∀ u ∈ g32p_lefschetz J pol, exteriorPower.map 2 (m2_powerAction J r u)
        (HodgeBlocks.complexifyWedge 2
          (polarizationVec (torusCohomology_cupProductOf (g3_power J r)) d)) =
        HodgeBlocks.complexifyWedge 2
          (polarizationVec (torusCohomology_cupProductOf (g3_power J r)) d) := by
  let F := exteriorPower.map 2 (g32p_powerOne J r)
  let z := HodgeBlocks.complexifyWedge 2
    (polarizationVec (torusCohomology_cupProductOf (g3_power J r)) d)
  have hF : Function.Bijective F :=
    ⟨exteriorPower.map_injective_field (m2_powerOne_bijective J r).1,
      exteriorPower.map_surjective (m2_powerOne_bijective J r).2⟩
  have he (u : Module.End ℂ (ℂ ⊗[ℚ] HQ J 1)) :
      exteriorPower.map 2 (m2_powerAction J r u) ∘ₗ F =
        F ∘ₗ exteriorPower.map 2 (g32p_diag J u r) := by
    dsimp only [F]
    simp only [← exteriorPower.map_comp, m2_powerAction_comp_powerOne]
  constructor
  · rintro ⟨v, hv, hc⟩ u hu
    have hz : F v = z := (m2_powerClass_eq_rational_iff J r d v).1 hc
    have hvu : exteriorPower.map 2 (g32p_diag J u r) v = v := by
      exact (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp hv u) hu
    calc
      _ = exteriorPower.map 2 (m2_powerAction J r u) (F v) := congrArg _ hz.symm
      _ = F (exteriorPower.map 2 (g32p_diag J u r) v) := LinearMap.congr_fun (he u) v
      _ = z := (congrArg F hvu).trans hz
  · intro h
    obtain ⟨v, hv⟩ := hF.2 z
    refine ⟨v, ?_, (m2_powerClass_eq_rational_iff J r d v).2 hv⟩
    refine (Submodule.mem_iInf _).mpr (fun u => (Submodule.mem_iInf _).mpr (fun hu => ?_))
    change exteriorPower.map 2 (g32p_diag J u r) v = v
    apply hF.1
    have hc := LinearMap.congr_fun (he u) v
    change exteriorPower.map 2 (m2_powerAction J r u) (F v) =
      F (exteriorPower.map 2 (g32p_diag J u r) v) at hc
    rw [hv, h u hu] at hc
    exact hc.symm.trans hv.symm


theorem m2_powerAction_centralizer (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol)) (r : ℕ)
    (u : Module.End ℂ (ℂ ⊗[ℚ] HQ J 1)) (hu : u ∈ g32p_lefschetz J pol) :
    m2_powerAction J r u ∈ m0_endCentralizer (g3_power J r) := by
  have hcJ := (m0_centralizer_integral J u).1
    ((m0_mem_lefschetz_iff J pol hη u).1 hu).2.1
  apply (m0_centralizer_integral (g3_power J r) _).2
  intro f hf
  letI : IsMonHom f := hf
  let F := m2_powerOneInv J r ∘ₗ (homPullback f 1).baseChange ℂ ∘ₗ g32p_powerOne J r
  have hent (i j : Fin r) :
      LinearMap.proj i ∘ₗ F ∘ₗ LinearMap.single ℂ (fun _ : Fin r => ℂ ⊗[ℚ] HQ J 1) j =
        (homPullback (g3_incl J r i ≫ f ≫ g3_proj J r j) 1).baseChange ℂ := by
    apply LinearMap.ext
    intro x
    change (homPullback (g3_incl J r i) 1).baseChange ℂ
      ((homPullback f 1).baseChange ℂ (g32p_powerOne J r (Pi.single j x))) = _
    rw [m2_powerOne_single]
    simp only [spec_homPullback_comp, LinearMap.baseChange_comp, LinearMap.comp_apply]
  have hdiag : g32p_diag J u r ∘ₗ F = F ∘ₗ g32p_diag J u r := by
    apply m2_diagonal_commutes_of_entries
    intro i j
    rw [hent]
    letI : IsMonHom (g3_incl J r i) := spec_g3_isMonHom_incl J r i
    letI : IsMonHom (g3_proj J r j) := spec_g3_isMonHom_proj J r j
    exact hcJ _ inferInstance
  apply LinearMap.ext
  intro x
  obtain ⟨v, rfl⟩ := (m2_powerOne_bijective J r).2 x
  calc
    _ = g32p_powerOne J r (g32p_diag J u r (F v)) := rfl
    _ = g32p_powerOne J r (F (g32p_diag J u r v)) :=
      congrArg (g32p_powerOne J r) (LinearMap.congr_fun hdiag v)
    _ = (homPullback f 1).baseChange ℂ (g32p_powerOne J r (g32p_diag J u r v)) :=
      LinearMap.congr_fun (m2_powerOne_compInv J r) _
    _ = _ := congrArg ((homPullback f 1).baseChange ℂ)
      (LinearMap.congr_fun (m2_powerAction_comp_powerOne J r u) v).symm


end HodgeLean.Foundations.Program
