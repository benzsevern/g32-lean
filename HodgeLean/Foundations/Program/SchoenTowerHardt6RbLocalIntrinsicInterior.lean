import Mathlib.Analysis.Convex.Intrinsic

/-! Intrinsic interior membership from agreement with a larger carrier on an open neighborhood. -/
namespace HodgeLean.Foundations.Program
open Topology

theorem s2v_hardt6rb_local_intrinsicInterior {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S T O : Set E) (hST : S ⊆ T) (hO : IsOpen O) (hlocal : O ∩ T ⊆ S)
    {x : E} (hx : x ∈ intrinsicInterior ℝ T) (hxO : x ∈ O) :
    x ∈ intrinsicInterior ℝ S := by
  obtain ⟨y, hy, hyx⟩ := mem_intrinsicInterior.mp hx
  have hxS : x ∈ S := hlocal ⟨hxO, intrinsicInterior_subset hx⟩
  let z : affineSpan ℝ S := ⟨x, subset_affineSpan ℝ S hxS⟩
  let f : affineSpan ℝ S → affineSpan ℝ T := fun p =>
    ⟨p.val, (affineSpan_mono ℝ hST) p.property⟩
  have hf : Continuous f := continuous_subtype_val.subtype_mk _
  have hfz : f z = y := Subtype.ext hyx.symm
  have hn : f ⁻¹' interior ((↑) ⁻¹' T : Set (affineSpan ℝ T)) ∈ 𝓝 z :=
    (hf.tendsto z).eventually (isOpen_interior.mem_nhds (hfz.symm ▸ hy))
  have ho : ((↑) ⁻¹' O : Set (affineSpan ℝ S)) ∈ 𝓝 z :=
    (hO.preimage continuous_subtype_val).mem_nhds hxO
  refine mem_intrinsicInterior.mpr ⟨z, mem_interior_iff_mem_nhds.mpr ?_, rfl⟩
  filter_upwards [hn, ho] with p hp hpO
  have hpT : f p ∈ ((↑) ⁻¹' T : Set (affineSpan ℝ T)) := interior_subset hp
  exact hlocal ⟨hpO, hpT⟩

end HodgeLean.Foundations.Program
