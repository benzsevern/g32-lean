import HodgeLean.Foundations.Program.G32Native.PairedC3OpenPullbackReduced
import HodgeLean.Foundations.Program.G32Native.PairedC3TrivialRegions

/-! # Gluing the direct chart union across the complementary regions -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- An affine open avoiding an ideal's actual support has unit section
ideal, including when the affine open is empty.
Source: Hartshorne, Algebraic Geometry, II.5. -/
theorem paired_c3_ideal_top_of_avoid
    {X : Scheme.{0}} (I : X.IdealSheafData) (V : X.affineOpens)
    (hV : ∀ x ∈ V.1, x ∉ I.support) : I.ideal V = ⊤ := by
  apply PrimeSpectrum.zeroLocus_empty_iff_eq_top.mp
  rw [← s2v_l1b_fromSpec_support I V]
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  have hzV := Set.mem_range_self (f := V.2.fromSpec) z
  rw [V.2.range_fromSpec] at hzV
  exact hV _ hzV hz

#print axioms paired_c3_ideal_top_of_avoid
end HodgeLean.Foundations.Program.G32Native
