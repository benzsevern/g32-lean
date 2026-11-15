import HodgeLean.Foundations.Program.RelativeFrameEllipticCoker

noncomputable section
open Set Manifold Filter Topology
open scoped ContDiff
namespace HodgeLean.Foundations.Program

theorem rfw_holForm_finrank_aux : Module.finrank ℂ (b3_HolForm ℂ rfw_E) = 1 :=
  rfw_finrank_holForm

theorem rfw_dz_mem_holForm_aux : rfw_dz ∈ b3_HolForm ℂ rfw_E :=
  rfw_dz_mem

theorem rfw_glue_kdz_aux : rf4_glue rfw_plumbing rfw_kdz = rfw_dz :=
  rfw_glue_kdz_rfw

theorem rfw_fibre_glue_kdz_aux (b : Fin 10 → ℂ) (t : b6t_polydisc b) :
    rf4_glue (rfw_plumbingAt b t) rfw_kdz = rfw_fibreDz b t :=
  rfw_fibre_glue_kdz_rfw b t

theorem rfw_delta_coker_finrank_aux :
    Module.finrank ℂ (rf4_Tgt rfw_outer ⧸ (rf4_delta rfw_outer (fun _ ↦ 0)).range) = 1 :=
  rfw_coker_finrank

end HodgeLean.Foundations.Program
