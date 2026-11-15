import HodgeLean.Foundations.Program.SchoenSelectedGeometryBranchIndex
import HodgeLean.Foundations.Program.SchoenSelectedGeometryLabelEnumeration
import HodgeLean.Foundations.Program.G32SelectedRealizationFamilyAges

noncomputable section
set_option maxHeartbeats 400000
open Manifold HodgeLean.Papers
open scoped ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.fibreChart
  b65z_SharedFamily.fibreMan b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact
  b65z_SharedFamily.fibreConnected b65z_SharedFamily.fibreFaithful
  b65z_SharedFamily.totalChart b65z_SharedFamily.totalMan

/-- The finite branch indices can be ordered by the literal supplier exponent list. -/
theorem s0_branch_ordering {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c)
    (hg : g32h_Nielsen (fun j ↦ b4b_toMatrix (g j))) (S : g32p_Supplier) :
    ∃ e : Fin (g32p_exponents S).length ≃ s0_BranchIndex S.H S.χ g,
      ∀ i, s0_branchLabel S.H S.χ g (e i) = ((g32p_exponents S)[i] : ZMod S.m) := by
  classical
  letI : NeZero S.m := ⟨by have := S.three_le; omega⟩
  letI := Fintype.ofFinite (s0_BranchIndex S.H S.χ g)
  let l := (g32p_exponents S).map (fun a : ℕ ↦ (a : ZMod S.m))
  have hv (a : s0_BranchIndex S.H S.χ g) : s0_branchLabel S.H S.χ g a ≠ 0 := a.property
  have hl (b : ZMod S.m) (hb : b ∈ l) : b ≠ 0 := by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
    change a ∈ (papersExpsList S.H S.χ g32p_classList) at ha
    rw [papersExpsList, Multiset.mem_toList] at ha
    obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp ha
    simpa only [ZMod.natCast_zmod_val] using papersExpsTuple_ne_zero S.H S.χ g32p_classList z hz
  have hs (w : ZMod S.m → ℝ) (hw : w 0 = 0) :
      ∑ a : s0_BranchIndex S.H S.χ g, w (s0_branchLabel S.H S.χ g a) = (l.map w).sum := by
    rw [s0_branchIndex_weight S.H S.χ g w hw]
    choose r hr using (fun x : b65z_fibre c D.C t ↦
      b4_exists_rotGen (Module.finrank_self ℂ) (fun h : S.H ↦ D.hG t h) x)
    choose x hx hrot using D.hrot t
    have hh := g32y_nielsen_exponent_weights (D.hG t) S.H S.χ w hw r hr g hg x hrot
    simpa only [l, g32p_exponents, List.map_map, Function.comp_def] using hh
  obtain ⟨e, he⟩ := s0_label_enumeration (s0_branchLabel S.H S.χ g) l hv hl hs
  let d : Fin (g32p_exponents S).length ≃ Fin l.length := finCongr (List.length_map ..).symm
  refine ⟨d.trans e, fun i ↦ ?_⟩
  have hh := he (d i)
  simpa [l, d] using hh

#print axioms s0_branch_ordering
end HodgeLean.Foundations.Program
