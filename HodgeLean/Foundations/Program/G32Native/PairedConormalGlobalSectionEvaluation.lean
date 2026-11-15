import HodgeLean.Foundations.BundleThom.ConormalFrameCoefficientHelpers
import HodgeLean.Foundations.BundleThom.ConormalFrameRestrictionHelpers
import HodgeLean.Foundations.BundleThom.ConormalSectionAlgebraHelpers
import HodgeLean.Foundations.BundleThom.DualCoordinateEvaluationHelpers
import HodgeLean.Foundations.BundleThom.FreePointProjectionHelpers
import HodgeLean.Foundations.BundleThom.FreeSectionSpecializationHelpers
import HodgeLean.Foundations.BundleThom.InverseFrameContinuityHelpers
import HodgeLean.Foundations.BundleThom.InverseFrameEvaluationHelpers
import HodgeLean.Foundations.BundleThom.LocalSectionRestrictionHelpers
import HodgeLean.Foundations.BundleThom.ModuleSectionPullbackHelpers
import HodgeLean.Foundations.BundleThom.ModuleSectionTransportHelpers
import HodgeLean.Foundations.BundleThom.UnitCompositionHelpers
import HodgeLean.Foundations.BundleThom.UnitSpecializationHelpers
import HodgeLean.Foundations.BundleThom.AnalyticNormalTopologyHelpers
/-! # Global algebraic sections as continuous normal-bundle observations -/

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Bundle
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.BundleThom

/-- Canonical pullback of a section retains the comparison for equal scheme maps. -/
theorem paired_moduleSectionPullback_congr {X Y : Scheme.{0}}
    (f g : X ⟶ Y) (h : f = g) (M : Y.Modules)
    (s : SheafOfModules.unit Y.ringCatSheaf ⟶ M) :
    i1_moduleSectionPullback f M s ≫ (Scheme.Modules.pullbackCongr h).hom.app M =
      i1_moduleSectionPullback g M s := by
  cases h
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom,
    NatTrans.id_app, Category.comp_id]

/-- Restricting a supplied global section and specializing it at an actual
point gives the original point pullback of that same section. -/
theorem paired_globalSection_specialization {Q : Over (Spec ↧ℂ)}
    (M : Q.left.Modules) (U : Q.left.Opens)
    (s : SheafOfModules.unit Q.left.ringCatSheaf ⟶ M)
    (x : ComplexPoint Q) (hx : x ∈ Point.overOpen U) :
    i1_localModuleSectionSpecialization M U (i1_moduleSectionPullback U.ι M s) x hx =
      i1_moduleSectionPullback x.left M s := by
  rw [i1_localModuleSectionSpecialization_transport]
  rw [← Category.assoc, i1_moduleSectionPullback_composition]
  exact paired_moduleSectionPullback_congr _ _ (ComplexPoint.liftToOpen_fac Q U x hx) M s

/-- The value of the supplied global section in its actual complex-point fibre. -/
def pairedGlobalSectionValue {Q : Over (Spec ↧ℂ)} (M : Q.left.Modules)
    (s : SheafOfModules.unit Q.left.ringCatSheaf ⟶ M) (x : ComplexPoint Q) :
    (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).obj
      ((Scheme.Modules.pullback x.left).obj M) :=
  (moduleSpecΓFunctor (R := CommRingCat.of ℂ)).map
    (i1_moduleSectionPullback x.left M s) (1 : Γ(Spec ↧ℂ, ⊤))

/-- Local section values retain the same actual value of a restricted global section. -/
theorem paired_globalSection_value {Q : Over (Spec ↧ℂ)}
    (M : Q.left.Modules) (U : Q.left.Opens)
    (s : SheafOfModules.unit Q.left.ringCatSheaf ⟶ M)
    (x : ComplexPoint Q) (hx : x ∈ Point.overOpen U) :
    i1_localModuleSectionValue M U (i1_moduleSectionPullback U.ι M s) x hx =
      pairedGlobalSectionValue M s x := by
  unfold i1_localModuleSectionValue
  rw [paired_globalSection_specialization]
  rfl

/-- Evaluation of a supplied global conormal section is continuous on the
actual normal total space, before selecting any bundle chart. -/
theorem paired_normalGlobalEvaluation_continuous
    {Q : Over (Spec ↧ℂ)} {V : Scheme} (j : Q.left ⟶ V) (k : ℕ)
    (s : SheafOfModules.unit Q.left.ringCatSheaf ⟶ Conormal.sheaf j) :
    letI := i1_normalTotalTopology j k
    Continuous (fun z : TotalSpace (Fin k → ℂ) (i1_normalFibre j) =>
      z.2 (pairedGlobalSectionValue (Conormal.sheaf j) s z.proj)) := by
  letI := i1_normalTotalTopology j k
  let U : Q.left.Opens := ⊤
  let t := i1_moduleSectionPullback U.ι (Conormal.sheaf j) s
  have htop (z : TotalSpace (Fin k → ℂ) (i1_normalFibre j)) :
      z.proj ∈ Point.overOpen U := by trivial
  have hc : Continuous (fun z : TotalSpace (Fin k → ℂ) (i1_normalFibre j) =>
      (⟨z, htop z⟩ : {z : TotalSpace (Fin k → ℂ) (i1_normalFibre j) |
        z.proj ∈ Point.overOpen U})) := continuous_id.subtype_mk _
  have h := (i1_normalLocalEvaluation_continuous j k U t).comp hc
  apply h.congr
  intro z
  change z.2 (i1_localModuleSectionValue (Conormal.sheaf j) U t z.proj (htop z)) = _
  rw [paired_globalSection_value]

/-- The original ordered global sections define actual linear observations
on each dual conormal fibre. -/
def pairedNormalGlobalObservations
    {Q : Over (Spec ↧ℂ)} {V : Scheme} (j : Q.left ⟶ V) (n : ℕ)
    (s : Fin n → (SheafOfModules.unit Q.left.ringCatSheaf ⟶ Conormal.sheaf j))
    (x : ComplexPoint Q) : i1_normalFibre j x →ₗ[ℂ] (Fin n → ℂ) where
  toFun ψ i := ψ (pairedGlobalSectionValue (Conormal.sheaf j) (s i) x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Every coordinate of the actual global-section observation map is
continuous in the base and normal vector simultaneously. -/
theorem paired_normalGlobalObservations_continuous
    {Q : Over (Spec ↧ℂ)} {V : Scheme} (j : Q.left ⟶ V) (k n : ℕ)
    (s : Fin n → (SheafOfModules.unit Q.left.ringCatSheaf ⟶ Conormal.sheaf j)) :
    letI := i1_normalTotalTopology j k
    Continuous (fun z : TotalSpace (Fin k → ℂ) (i1_normalFibre j) =>
      pairedNormalGlobalObservations j n s z.proj z.2) := by
  letI := i1_normalTotalTopology j k
  exact continuous_pi (fun i => paired_normalGlobalEvaluation_continuous j k (s i))

#print axioms paired_moduleSectionPullback_congr
#print axioms paired_globalSection_specialization
#print axioms paired_globalSection_value
#print axioms paired_normalGlobalEvaluation_continuous
#print axioms pairedNormalGlobalObservations
#print axioms paired_normalGlobalObservations_continuous
end HodgeLean.Foundations.Program.G32Native
