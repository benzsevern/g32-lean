import HodgeLean.Foundations.Program.G32Native.PairedConormalHyperplaneFrames
import HodgeLean.Foundations.Program.G32Native.PairedConormalHyperplaneIdealIso
import HodgeLean.Foundations.Program.G32Native.PairedConormalModuleFibres
import HodgeLean.Ported.NYLL.SchemeTheory.ProjectiveSpace.TwistingSheafCocycle
import HodgeLean.Foundations.Program.G32Native.PairedConormalNativeHyperplaneRegular

/-! # Specified frames of the actual native hyperplane ideal module -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Foundations.Curves.Picard.LineBundles
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program.G32Native

/-- The native hyperplane chart image is the original standard open. -/
theorem paired_nativeHyperplaneChartOpen_eq (k : ℕ) (i : Fin (k + 1)) :
    (paired_nativeHyperplaneChartOpen k i).1 = ProjSpace.standardOpen ℂ k i := by
  change Proj.awayι _ _ _ _ ''ᵁ ⊤ = _
  rw [Scheme.Hom.image_top_eq_opensRange, Proj.opensRange_awayι]

/-- The specified regular coordinate ratio gives an actual frame of the
hyperplane kernel module on its native chart image. -/
def paired_nativeHyperplaneIdeal_chartFrame (k : ℕ) (i : Fin (k + 1)) :
    SheafOfModules.free (R := (paired_nativeHyperplaneChartOpen k i).1.toScheme.ringCatSheaf)
      PUnit ≅ (Scheme.Modules.pullback (paired_nativeHyperplaneChartOpen k i).1.ι).obj
        (Conormal.idealModule (paired_nativeHyperplaneIdeal k).subschemeι) := by
  let U := paired_nativeHyperplaneChartOpen k i
  let a := (paired_nativeHyperplaneChartEquiv k i).symm (ProjSpace.ratio ℂ k i 0)
  let eUnit : SheafOfModules.free (R := U.1.toScheme.ringCatSheaf) PUnit ≅
      SheafOfModules.unit U.1.toScheme.ringCatSheaf :=
    coproductUniqueIso (fun _ : PUnit => SheafOfModules.unit U.1.toScheme.ringCatSheaf)
  exact eUnit ≪≫ (idealLocalGeneratorIso (paired_nativeHyperplaneIdeal k) U a
    (paired_nativeHyperplaneChart_regular k i) (paired_nativeHyperplaneChart_principal k i)).symm ≪≫
      (Scheme.Modules.restrictFunctorIsoPullback U.1.ι).app
        (Conormal.idealModule (paired_nativeHyperplaneIdeal k).subschemeι)


open HodgeLean.Foundations.Curves.Picard.LineBundles HodgeLean.Foundations.Program
/-- The original Cartier frames transport through the specified polynomial ideal
isomorphism to actual frames of the native reduced hyperplane ideal. -/
theorem conormal_native_hyperplane_ideal_frames (k : ℕ)
    (y : Proj (MvPolynomial.homogeneousSubmodule (Fin (k + 1)) ℂ)) :
    ∃ U : (Proj (MvPolynomial.homogeneousSubmodule (Fin (k + 1)) ℂ)).Opens,
      y ∈ U ∧ Nonempty
        (SheafOfModules.free (R := U.toScheme.ringCatSheaf) PUnit ≅
          (Scheme.Modules.pullback U.ι).obj
            (idealModule (conormalNativeHyperplaneIdeal ℂ k))) := by
  let f := (s2_polynomialProjectiveSpaceIso ℂ (Fin (k + 1))).hom
  obtain ⟨U, hy, ⟨c⟩⟩ := paired_hyperplane_ideal_frames k (f y)
  let W := f ⁻¹ᵁ U
  exact ⟨W, hy, ⟨paired_module_framePullbackIso f
    (idealModule (s2e_hyperplaneIdeal k)) U PUnit c ≪≫
      (Scheme.Modules.pullback W.ι).mapIso (conormalHyperplanePolynomialIdealIso k)⟩⟩


end HodgeLean.Foundations.Program.G32Native
