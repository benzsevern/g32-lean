import HodgeLean.Foundations.Program.SchoenCycleC2ConormalChartFrameHelpers
import HodgeLean.Foundations.Program.SchoenCycleC2ConormalChartIsoHelpers
import HodgeLean.Foundations.Program.SchoenCycleC2OpenConormalRestrictionHelpers
import HodgeLean.Foundations.Program.SchoenCycleC2LocalFrameTransportHelpers

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A closed immersion between smooth complex schemes of relative
dimensions `n` and `n + k` has actual local conormal frames of rank `k`. -/
theorem s2e_smooth_closedImmersion_conormal_frames
    (Q W : Over (Spec ↧ℂ)) (n k : ℕ)
    [SmoothOfRelativeDimension n Q.hom] [SmoothOfRelativeDimension (n + k) W.hom]
    (ι : Q ⟶ W) [IsClosedImmersion ι.left] (x : Q.left) :
    ∃ U : Q.left.Opens, x ∈ U ∧ Nonempty
      (Scheme.Modules.restrict (s2c_conormal ι.left) U.ι ≅
        (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin k) : U.toScheme.Modules)) := by
  obtain ⟨V, hV, hxV, hP, hW, hQ⟩ :=
    s2e_closedImmersion_simultaneous_standardSmooth_charts Q W n (n + k) ι x
  let U := ι.left ⁻¹ᵁ V
  letI : Nonempty U := ⟨⟨x, hxV⟩⟩
  let p : PrimeSpectrum Γ(Q.left, U) := hP.isoSpec.hom ⟨x, hxV⟩
  obtain ⟨f, hf, ⟨b⟩⟩ := s2e_immersion_chart_localization_frame Q W ι V hV n k hW hQ p
  let S := Γ(Q.left, U)
  let T := CommRingCat.of (Localization.Away f)
  let l : Spec T ⟶ Spec S := Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away f)))
  let a : Spec T ⟶ Q.left := (l ≫ hP.isoSpec.inv) ≫ U.ι
  letI : IsOpenImmersion a := by
    dsimp only [a, l]
    infer_instance
  let eU : (Scheme.Modules.pullback U.ι).obj (s2c_conormal ι.left) ≅
      s2c_conormal (ι.left ∣_ V) :=
    (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm.app (s2c_conormal ι.left) ≪≫
      s2e_conormal_restrict_ambient_open_iso ι.left V
  let eC := s2e_immersion_affine_chart_conormal_iso ι.left V hV
  have ba : (Scheme.Modules.pullback a).obj (s2c_conormal ι.left) ≅
      (SheafOfModules.free (R := (Spec T).ringCatSheaf) (Fin k) : (Spec T).Modules) :=
    (Scheme.Modules.pullbackComp (l ≫ hP.isoSpec.inv) U.ι).symm.app
        (s2c_conormal ι.left) ≪≫
      (Scheme.Modules.pullback (l ≫ hP.isoSpec.inv)).mapIso eU ≪≫
      (Scheme.Modules.pullbackComp l hP.isoSpec.inv).symm.app (s2c_conormal (ι.left ∣_ V)) ≪≫
      (Scheme.Modules.pullback l).mapIso eC ≪≫ b
  have hp : p ∈ Set.range l := by
    change p ∈ Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away f)))
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away f) f]
    exact hf
  obtain ⟨z, hz⟩ := hp
  apply s2e_openImmersion_frame_neighbourhood a (s2c_conormal ι.left) k ba x
  refine ⟨z, ?_⟩
  change U.ι (hP.isoSpec.inv (l z)) = x
  rw [hz]
  change U.ι (hP.isoSpec.inv (hP.isoSpec.hom ⟨x, hxV⟩)) = x
  exact congrArg (fun q : U.toScheme => U.ι q)
    (congrArg (fun g : U.toScheme ⟶ U.toScheme => g (⟨x, hxV⟩ : U.toScheme))
      hP.isoSpec.hom_inv_id)

end HodgeLean.Foundations.Program
