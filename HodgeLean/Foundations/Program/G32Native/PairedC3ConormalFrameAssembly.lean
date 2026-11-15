import HodgeLean.Foundations.Program.G32Native.PairedC3ConormalFrameCoordinates
import HodgeLean.Foundations.Program.G32Native.PairedC3CoordinateConormalRank
import HodgeLean.Foundations.Program.G32Native.PairedC3SplitBundleCoproduct
import HodgeLean.Foundations.Program.G32Native.PairedC3FreeSectionCoordinates
import HodgeLean.Foundations.Program.G32Native.PairedC3LocalModuleIso

/-! # Bundle assembly retaining the canonical normal generator frames -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program
attribute [local instance] Classical.propDecidable

/-- An actual module isomorphism supplies natural comparisons on any specified cover. -/
def pairedC3ComparisonOfIso {X : Scheme.{0}} {M N : X.Modules}
    (e : M ≅ N) {ι : Type} (U : ι → X.Opens) :
    PairedC3LocalModuleComparison M N U where
  equiv _ V _ := pairedC3ModuleIsoSectionEquiv X e V
  restrict _ _ _ h _ s := PresheafOfModules.naturality_apply e.hom.val (homOfLE h).op s
  agree _ _ _ _ _ _ := rfl

/-- Canonical free normal frames and their checked transitions identify the
actual polynomial inclusion conormal with the specified recursive split bundle. -/
def pairedC3PolynomialConormalGeneratorIso {n k : ℕ}
    (e : Fin (k + 1) ↪ Fin (n + 1))
    (hframe : ∀ (i : Fin (k + 1)) (V : (pairedC3Proj k).Opens)
      (hi : V ≤ ProjSpace.standardOpen ℂ k i),
      Function.Bijective (pairedC3FiniteFrameSynthesis
        (fun j : {j : Fin (n + 1) // j ∉ Set.range e} =>
          pairedC3ConormalStandardGenerator e i j.val j.property) V hi)) :
    s2c_conormal (pairedC3PolynomialCoordinateInclusion (A := ℂ) e) ≅
      pairedC3SplitBundle k 0 (n - k) := by
  classical
  let D := pairedC3ConormalComparisonOfGeneratorFrames e hframe
  let P := fun _ : {j : Fin (n + 1) // j ∉ Set.range e} => pairedC3NegativeLine k
  letI : HasFiniteBiproducts (pairedC3Proj k).Modules :=
    HasFiniteBiproducts.of_hasFiniteProducts
  have hc : ⨆ i, ProjSpace.standardOpen ℂ k i = ⊤ := by
    apply top_unique
    rw [← ProjSpace.iSup_twistingCover ℂ k]
    exact iSup_le (fun i => le_iSup (fun j => ProjSpace.standardOpen ℂ k j) i.down)
  let E := Fintype.equivFinOfCardEq (paired_c3_coordinate_normal_card e)
  exact pairedC3LocalModuleIso D hc ≪≫
    (biproduct.isoProduct P).symm ≪≫ biproduct.isoCoproduct P ≪≫
    Sigma.reindex E (fun _ : Fin (n - k) => pairedC3NegativeLine k) ≪≫
    (pairedC3SplitBundleCoproduct k (n - k)).symm

#print axioms pairedC3ComparisonOfIso
#print axioms pairedC3PolynomialConormalGeneratorIso
end HodgeLean.Foundations.Program.G32Native
