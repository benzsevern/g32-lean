import HodgeLean.Foundations.Semialgebraic.SchoenCyclePairBarycentricInverse
import HodgeLean.Foundations.Semialgebraic.SchoenCyclePairFullWeightedPoint
import HodgeLean.Foundations.Semialgebraic.SchoenCyclePairFaceNormalization

/-! Normalized marked coordinates land in the full subcomplex and retain their coordinates.
HC no distance; AV milestone no distance. -/
noncomputable section
open HodgeLean.Foundations.Program
namespace Semialgebraic.CompatibleTriangulation.Helpers

/-- Normalization within a face reconstructs a marked point with the prescribed global weights. -/
theorem s2e_pair_normalized_point {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
    (K D : Geometry.SimplicialComplex ℝ E) (V : Finset E)
    (W : C(K.space, stdSimplex ℝ V))
    (hW : ∀ (s : Finset E) (hs : s ∈ K.faces) (u : stdSimplex ℝ s)
      (x : K.space), (∑ i, u.val i • i.val) = x.val →
      ∀ a : V, (W x).val a = if ha : a.val ∈ s then u.val ⟨a.val, ha⟩ else 0)
    (hfull : ∀ s ∈ K.faces, (∀ a ∈ s, a ∈ D.vertices) → s ∈ D.faces)
    (S : Finset V) (hS : ∀ a : V, a ∈ S ↔ a.val ∈ D.vertices)
    (s : Finset E) (hs : s ∈ K.faces) (hsV : s ⊆ V)
    (w : stdSimplex ℝ V) (hsupport : ∀ a : V, a.val ∉ s → w.val a = 0)
    (hw : 0 < ∑ a ∈ S, w.val a) :
    ∃ y : K.space,
      y.val = (∑ a : V, (s2e_pair_faceNormalize S w hw).val a • a.val) ∧
      W y = s2e_pair_faceNormalize S w hw ∧ y.val ∈ D.space := by
  classical
  let n := s2e_pair_faceNormalize S w hw
  have hn (a : V) (ha : a.val ∉ s) : n.val a = 0 := by
    change (if a ∈ S then w.val a / (∑ b ∈ S, w.val b) else 0) = 0
    rw [hsupport a ha, zero_div]
    split_ifs <;> rfl
  have hmarked : (∑ a : V, n.val a • a.val) ∈ D.space := by
    apply s2e_pair_full_subcomplex_weighted_point K D hfull s hs
      (fun a : V => a.val) n
    intro a ha
    constructor
    · by_contra has
      exact ha (hn a has)
    · apply (hS a).mp
      by_contra has
      exact ha (s2e_pair_faceNormalize_outside S w hw a has)
  obtain ⟨y, hy, hWy⟩ := s2e_pair_barycentric_inverse_on_face K V W hW s hs hsV n hn
  exact ⟨y, hy, hWy, hy.symm ▸ hmarked⟩

end Semialgebraic.CompatibleTriangulation.Helpers
