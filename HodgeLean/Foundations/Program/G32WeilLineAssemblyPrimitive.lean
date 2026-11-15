import HodgeLean.Foundations.Program.G32RepTransport
import HodgeLean.Foundations.Program.G32WeilLineAssemblySimple

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
set_option Elab.async false
open scoped TensorProduct
open HodgeLean.RealDefs HodgeLean.Papers HodgeLean.Foundations
namespace HodgeLean.Foundations.Program

theorem g32c_primitive_ne_bot_of_eigen (A : g32t_Sixfold) (X : g32p_Cover A)
    (S : g32p_Supplier)
    (hpos : 0 < Module.finrank ℂ (rfd_eigen (g32rep_rep X) S.H (g32rep_chi S))) :
    g32p_primitive X.aut S ≠ ⊥ := by
  have hroot : IsPrimitiveRoot (g32p_root S.m ^ (1 : ℤ)) S.m := by
    simpa only [zpow_one] using g32rep_root_prim S.m (NeZero.ne S.m)
  have hle : rfd_eigen (g32rep_rep X) S.H (g32rep_chi S) ≤
      (g32p_primitive X.aut S).baseChange ℂ := by
    simpa only [zpow_one] using
      g32rep_eigen_le_primC X S (g32rep_chi S) (g32rep_chi_apply S) 1 hroot
  intro hb
  rw [hb, Submodule.baseChange_bot] at hle
  have he := le_bot_iff.mp hle
  rw [he, finrank_bot] at hpos
  omega

end HodgeLean.Foundations.Program
