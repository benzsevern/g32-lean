import HodgeLean.Foundations.Semialgebraic.SchoenCyclePairBarycentricInverse
import HodgeLean.Foundations.Semialgebraic.SchoenCyclePairSimplexInterpolation

/-! The normalized straight-line path stays in the positive-mass part of a geometric carrier.
HC no distance; AV milestone no distance. -/
noncomputable section
open HodgeLean.Foundations.Program
namespace Semialgebraic.CompatibleTriangulation.Helpers

/-- Interpolation within a face preserves the carrier and positive selected mass. -/
theorem s2e_pair_positive_mass_path {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
    (K : Geometry.SimplicialComplex ℝ E) (V : Finset E)
    (W : C(K.space, stdSimplex ℝ V))
    (hW : ∀ (s : Finset E) (hs : s ∈ K.faces) (u : stdSimplex ℝ s)
      (x : K.space), (∑ i, u.val i • i.val) = x.val →
      ∀ a : V, (W x).val a = if ha : a.val ∈ s then u.val ⟨a.val, ha⟩ else 0)
    (s : Finset E) (hs : s ∈ K.faces) (hsV : s ⊆ V)
    (w : stdSimplex ℝ V) (hsupport : ∀ a : V, a.val ∉ s → w.val a = 0)
    (S : Finset V) (hw : 0 < ∑ a ∈ S, w.val a) (t : unitInterval) :
    ∃ y : K.space,
      y.val = (1 - (t : ℝ)) • (∑ a : V, w.val a • a.val) +
        (t : ℝ) • (∑ a : V, (s2e_pair_faceNormalize S w hw).val a • a.val) ∧
      0 < ∑ a ∈ S, (W y).val a := by
  classical
  let n := s2e_pair_faceNormalize S w hw
  let z := s2e_pair_simplexInterpolate w n t
  have hn (a : V) (ha : a.val ∉ s) : n.val a = 0 := by
    change (if a ∈ S then w.val a / (∑ b ∈ S, w.val b) else 0) = 0
    rw [hsupport a ha, zero_div]
    split_ifs <;> rfl
  have hz (a : V) (ha : a.val ∉ s) : z.val a = 0 := by
    change (1 - (t : ℝ)) * w.val a + (t : ℝ) * n.val a = 0
    rw [hsupport a ha, hn a ha, mul_zero, mul_zero, add_zero]
  obtain ⟨y, hy, hWy⟩ := s2e_pair_barycentric_inverse_on_face K V W hW s hs hsV z hz
  refine ⟨y, ?_, ?_⟩
  · rw [hy]
    change (∑ a : V, ((1 - (t : ℝ)) * w.val a + (t : ℝ) * n.val a) • a.val) = _
    simp only [add_smul, mul_smul, Finset.sum_add_distrib, Finset.smul_sum]
    rfl
  · rw [hWy]
    exact s2e_pair_faceNormalize_segment_mass_pos S w hw t

end Semialgebraic.CompatibleTriangulation.Helpers
