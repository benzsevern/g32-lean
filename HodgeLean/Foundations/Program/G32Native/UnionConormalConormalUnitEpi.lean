import HodgeLean.Foundations.Program.G32Native.UnionConormalUnitOpenCover
import HodgeLean.Foundations.Program.G32Native.UnionConormalUnitObjectIso
import HodgeLean.Foundations.Program.G32Native.UnionConormalAffineConormalUnitEpi
import HodgeLean.Foundations.Program.SchoenCycleC2OpenConormalRestrictionHelpers

/-! # Epic units on the actual conormal of an immersion -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- The pullback unit on an actual conormal is epic along a supplied immersion. -/
lemma unionConormal_conormalUnit_epi
    {Q W S : Scheme.{0}} (i : Q ⟶ W) [IsClosedImmersion i]
    (f : S ⟶ Q) [IsClosedImmersion f] :
    Epi ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (s2c_conormal i)) := by
  apply unionConormal_unit_epi_of_open_neighborhoods
  intro q
  obtain ⟨U, hU, hq, _⟩ := exists_isAffineOpen_mem_and_subset (X := W)
    (U := ⊤) (x := i q) (show i q ∈ (⊤ : W.Opens) from trivial)
  let V := i ⁻¹ᵁ U
  haveI : IsAffine U.toScheme := hU
  haveI : IsAffine V.toScheme := hU.preimage i
  haveI := unionConormal_affineConormalUnit_epi (i ∣_ U) (f ∣_ V)
  refine ⟨V, hq, ?_⟩
  exact unionConormal_unit_epi_of_iso
    (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ V))
    (s2e_conormal_restrict_ambient_open_iso i U)

end HodgeLean.Foundations.Program.G32Native
