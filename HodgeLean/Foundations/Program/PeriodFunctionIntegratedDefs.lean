import HodgeLean.Foundations.Program.RelativeFrameAssembly
import HodgeLean.Foundations.Program.PeriodFunctionChecks
import HodgeLean.Foundations.Program.PrymFamilyExists

/-! # Period data on one retained marked family
Implication from shared geometry and an H7 marking to period coordinates.
HC no distance; AV milestone no distance.
-/
noncomputable section
open Set Manifold Filter Topology HodgeLean.Papers
open scoped ContDiff TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold
attribute [local instance] rf8_SharedFamily.topC rf8_SharedFamily.chartC
  rf8_SharedFamily.manC rf8_SharedFamily.t2C rf8_SharedFamily.compactC
  rf8_SharedFamily.connectedC rf8_SharedFamily.actionC rf8_SharedFamily.totalChart
  rf8_SharedFamily.totalMan rf8_SharedFamily.fibreChart rf8_SharedFamily.fibreMan
  rf8_SharedFamily.fibreT2 rf8_SharedFamily.fibreCompact rf8_SharedFamily.fibreConnected
  rf8_SharedFamily.fibreFaithful

/-- Projection of the retained atlas and integral fields to the period-family input.
Source: `docs/specs/RelativeFrameAssembly.md`, integration review. -/
def b64i_rootFamily (R : rf8_SharedFamily) : b64c_RootFamily where
  C := R.C
  topC := R.topC
  chartC := R.chartC
  manC := R.manC
  t2C := R.t2C
  compactC := R.compactC
  connectedC := R.connectedC
  actionC := R.actionC
  hC := R.hC
  totalChart := R.totalChart
  totalMan := R.totalMan
  fibreChart := R.fibreChart
  fibreMan := R.fibreMan
  fibreT2 := R.fibreT2
  fibreCompact := R.fibreCompact
  fibreConnected := R.fibreConnected
  fibreFaithful := R.fibreFaithful
  hincl := R.hincl
  hG := R.hG
  hk := R.hk
  hsurj := R.hsurj
  hgal := R.hgal
  hbranch := R.hbranch
  hrot := R.hrot
  Q₀ := R.Q₀
  hQ₀ := R.hQ₀
  Q := R.Q
  hQ := R.hQ
  P := R.P
  hP := R.hP
  A := R.A
  hA := R.hA
  f := R.atlas.f
  hf := R.atlas.hf
  hs := R.atlas.hsurj
  hAt := fun q ↦ ⟨R.atlas.A q, (R.atlas.hA q).2, (R.atlas.hA q).1, R.atlas.hparam q⟩

example (R : rf8_SharedFamily) : (b64i_rootFamily R).f = R.atlas.f := rfl

/-- Period coordinates of the shared family in a supplied rational marking.
Source: `b64c_geomPeriod`; Griffiths, Periods I, §1. -/
def b64i_period (R : rf8_SharedFamily) (s : b6t_polydisc mr_base)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice)) :
    (Fin 10 → ℂ) → Fin 9 → ℂ :=
  b64c_geomPeriod mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _) R.P s m

example (R : rf8_SharedFamily) (s : b6t_polydisc mr_base)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice)) :
    b64i_period R s m = b64c_geomPeriod mr_base R.C R.hC
      (b6t_polydisc mr_base) (Subset.refl _) R.P s m := rfl

end HodgeLean.Foundations.Program
