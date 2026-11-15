import HodgeLean.Foundations.Program.SchoenGenericPointMorphisms
import HodgeLean.Foundations.Program.SchoenCycleC1NormalizationOpenHelpers

/-! # The retained field source over a nonempty base open -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A dominant retained field point factors through every nonempty base
open, with the finiteness-of-cover conditions needed for normalization. -/
theorem s2e_c1_generic_source_lift_to_open
    {K : Type} [Field K] (X : Scheme) [IsIntegral X]
    (f : Spec (CommRingCat.of K) ⟶ X) [QuasiCompact f] [QuasiSeparated f] [IsDominant f]
    (U : X.Opens) (hU : (U : Set X).Nonempty) :
    ∃ g : Spec (CommRingCat.of K) ⟶ U.toScheme,
      QuasiCompact g ∧ QuasiSeparated g ∧ g ≫ U.ι = f := by
  have hr : Set.range f ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨t, rfl⟩
    rw [Subsingleton.elim t (genericPoint (Spec (CommRingCat.of K))), s2_dominant_genericPoint f]
    exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr
      (by simpa only [Set.univ_inter] using hU)
  let g := IsOpenImmersion.lift U.ι f hr
  have hg : g ≫ U.ι = f := IsOpenImmersion.lift_fac _ _ _
  haveI : QuasiCompact (g ≫ U.ι) := by rw [hg]; infer_instance
  haveI : QuasiCompact g := QuasiCompact.of_comp g U.ι
  haveI : QuasiSeparated g := inferInstance
  exact ⟨g, inferInstance, inferInstance, hg⟩

end HodgeLean.Foundations.Program
