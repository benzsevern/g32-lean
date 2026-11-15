import HodgeLean.Foundations.Semialgebraic.SchoenCyclePairBarycentricMap
import HodgeLean.Foundations.Semialgebraic.SchoenCyclePairRestrictWeights
import HodgeLean.Foundations.Semialgebraic.SchoenCyclePairZeroExtensionSum
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbSupportedHull

/-! Reconstruction and coordinates are inverse on each supported simplex.
HC no distance; AV milestone no distance. -/
noncomputable section
open HodgeLean.Foundations.Program
namespace Semialgebraic.CompatibleTriangulation.Helpers

/-- Every simplex-supported weight vector is recovered by the global coordinate map. -/
theorem s2e_pair_barycentric_inverse_on_face {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
    (K : Geometry.SimplicialComplex ℝ E) (V : Finset E)
    (W : C(K.space, stdSimplex ℝ V))
    (hW : ∀ (s : Finset E) (hs : s ∈ K.faces) (u : stdSimplex ℝ s)
      (x : K.space), (∑ i, u.val i • i.val) = x.val →
      ∀ a : V, (W x).val a = if ha : a.val ∈ s then u.val ⟨a.val, ha⟩ else 0)
    (s : Finset E) (hs : s ∈ K.faces) (hsV : s ⊆ V) (w : stdSimplex ℝ V)
    (hsupport : ∀ a : V, a.val ∉ s → w.val a = 0) :
    ∃ x : K.space, x.val = (∑ a : V, w.val a • a.val) ∧ W x = w := by
  classical
  obtain ⟨u, hu⟩ := s2e_pair_restrict_weights V s hsV w hsupport
  have hp : (∑ a : V, w.val a • a.val) ∈ K.space := by
    apply K.convexHull_subset_space hs
    apply s2v_hardt6rb_supported_convexHull (fun a : V => a.val) w (↑s : Set E)
    intro a ha
    by_contra has
    exact ha (hsupport a has)
  let x : K.space := ⟨_, hp⟩
  have hpoint : (∑ i : s, u.val i • i.val) = x.val :=
    (s2e_pair_zero_extension_sum V s hsV w.val u.val hu
      (fun a t => t • a) (fun _ => zero_smul ℝ _)).symm
  refine ⟨x, rfl, ?_⟩
  apply Subtype.ext
  funext a
  exact (hW s hs u x hpoint a).trans (hu a).symm

end Semialgebraic.CompatibleTriangulation.Helpers
