import HodgeLean.Foundations.Program.G32Native.TypeIIIOrbitWeilCast
import HodgeLean.Foundations.Program.G32Native.QuaternionWeilOrbit

noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj Quaternion
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.Program.QuaternionGraph
namespace HodgeLean.Foundations.Program.TypeIIIPaper
variable (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
  [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
  (W : letI := (torusCohomology_cupProductOf A).finite
    HodgeBlocks.WeilAction
      (abelianVarietyCohomologyOf (finiteBetti_abelian A)
        (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
        (torusCohomology_cupProductOf A)).weight1 3)
  (pol : HQ A 2)
  (hM : IsMemberOfM (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
    (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) W pol)

/-- The sixfold quaternionic orbit rank from the general rational exterior-orbit calculation. -/
theorem quaternionic_weil_finrank (P : GeneralPELMember A W pol hM) :
    Module.finrank ℚ (quaternionicSpan A (weilSix A W pol hM)) = 7 := by
  classical
  letI := (torusCohomology_cupProductOf A).finite
  let k := Module.finrank ℂ ↥(W.Vs ⊓
    (abelianVarietyCohomologyOf (finiteBetti_abelian A)
      (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
      (torusCohomology_cupProductOf A)).weight1.H (1,0))
  have hk : k = 3 := hM.finrank_eq_three
  have hn : k+k = 2*3 := by omega
  let L := W.weilClasses (h10_sup_h01_eq_top (finiteBetti_abelian A)
    (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
    (torusCohomology_cupProductOf A)) hM.isWeilType
  let e := ((torusCohomology_cupProductOf A).cupWedgeEquiv (k+k)).trans (HQ.castEquiv A hn)
  let ρ := (abelianEnd0Action A).comp P.end0.toAlgHom
  let qmap : ℍ[ℚ,-3,0,P.b]ˣ → (AbelianEnd0 A)ˣ := Units.map P.end0.toMonoidHom
  have hsur : Function.Surjective qmap := by
    intro d
    refine ⟨Units.map P.end0.symm.toMonoidHom d, ?_⟩
    ext
    exact P.end0.apply_symm_apply d.val
  have hClass : weilSix A W pol hM = L.map e.toLinearMap :=
    weilSix_eq_map_topCast A W pol hM hn
  have hI : W.J = quaternionAction ρ (quaternionI (-3) P.b) := P.eisenstein
  have hr := quaternion_weil_orbit_finrank W
    (h10_sup_h01_eq_top (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A))
    hM.isWeilType (by norm_num : (0 : ℚ) < 3) ρ P.b_neg hI
  let F : ℍ[ℚ,-3,0,P.b]ˣ → Module.End ℚ (⋀[ℚ]^(k+k) (HQ A 1)) :=
    fun q => exteriorPower.map (k+k) (quaternionAction ρ q)
  let G : ℍ[ℚ,-3,0,P.b]ˣ → Module.End ℚ (HQ A (2*3)) :=
    fun q => rationalPullback A (qmap q : AbelianEnd0 A) (2*3)
  have hInter (q : ℍ[ℚ,-3,0,P.b]ˣ) : (G q).comp e.toLinearMap = e.toLinearMap.comp (F q) :=
    rationalPullback_cast_cup A (qmap q : AbelianEnd0 A) hn
  have hMap := orbit_map_intertwine e L F G hInter
  rw [← hClass] at hMap
  have hSup : (⨆ q, (weilSix A W pol hM).map (G q)) =
      quaternionicSpan A (weilSix A W pol hM) := by
    apply le_antisymm
    · apply iSup_le
      intro q
      exact le_iSup (fun d : (AbelianEnd0 A)ˣ =>
        (weilSix A W pol hM).map (rationalPullback A d (2*3))) (qmap q)
    · apply iSup_le
      intro d
      obtain ⟨q, hq⟩ := hsur d
      have h := le_iSup (fun q => (weilSix A W pol hM).map (G q)) q
      simpa only [G, hq] using h
  rw [hSup] at hMap
  calc
    Module.finrank ℚ (quaternionicSpan A (weilSix A W pol hM)) =
        Module.finrank ℚ ((exteriorOrbit (fun q : ℍ[ℚ,-3,0,P.b]ˣ => quaternionAction ρ q) L).map e.toLinearMap) :=
      congrArg (fun U : Submodule ℚ (HQ A (2*3)) => Module.finrank ℚ U) hMap.symm
    _ = Module.finrank ℚ (exteriorOrbit (fun q : ℍ[ℚ,-3,0,P.b]ˣ => quaternionAction ρ q) L) :=
      LinearEquiv.finrank_map_eq e _
    _ = k+k+1 := hr
    _ = 7 := by rw [hk]

#print axioms quaternionic_weil_finrank
end HodgeLean.Foundations.Program.TypeIIIPaper
