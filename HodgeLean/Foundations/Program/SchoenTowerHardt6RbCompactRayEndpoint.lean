import HodgeLean.Foundations.Program.SchoenTowerHardt6RbIntrinsicExtension
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Tactic.Module

/-! Every non-apex point of a compact carrier lies on a segment to its intrinsic boundary. -/
namespace HodgeLean.Foundations.Program
open Topology

theorem s2v_hardt6rb_compact_ray_endpoint {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : Set E) (hC : IsCompact C) (a : E) (ha : a ∈ C)
    (x : E) (hx : x ∈ C) (hxa : x ≠ a) :
    ∃ y ∈ C \ intrinsicInterior ℝ C, ∃ t ∈ Set.Icc (0 : ℝ) 1,
      AffineMap.lineMap a y t = x := by
  let L : ℝ → E := AffineMap.lineMap a x
  have he : IsClosedEmbedding L := by
    convert (Homeomorph.addRight a).isClosedEmbedding.comp
      (isClosedEmbedding_smul_left (𝕜 := ℝ) (sub_ne_zero.mpr hxa)) using 1
    funext t
    rfl
  have h1 : (1 : ℝ) ∈ L ⁻¹' C := by simpa only [L, Set.mem_preimage, AffineMap.lineMap_apply_one] using hx
  obtain ⟨T, hT, hmax⟩ := (he.isCompact_preimage hC).exists_isMaxOn ⟨1, h1⟩ continuous_id.continuousOn
  have hT1 : 1 ≤ T := hmax h1
  have hTp : 0 < T := lt_of_lt_of_le zero_lt_one hT1
  have hboundary : L T ∉ intrinsicInterior ℝ C := by
    intro hinner
    obtain ⟨d, hd, hz⟩ := s2v_hardt6rb_intrinsicInterior_extend C hinner ha
    have hm : (1 + d) * T ∈ L ⁻¹' C := by
      change L ((1 + d) * T) ∈ C
      convert hz using 1
      dsimp only [L]
      simp only [AffineMap.lineMap_apply_module']
      module
    have hh : (1 + d) * T ≤ T := hmax hm
    nlinarith
  refine ⟨L T, ⟨hT, hboundary⟩, 1 / T, ⟨by positivity, (div_le_one hTp).mpr hT1⟩, ?_⟩
  simp only [L, AffineMap.lineMap_lineMap_right, one_div, inv_mul_cancel₀ (ne_of_gt hTp),
    AffineMap.lineMap_apply_one]

end HodgeLean.Foundations.Program
