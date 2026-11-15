import HodgeLean.Foundations.Program.SchoenTowerT11bCompactComponentFormula
import Mathlib.Topology.Connected.LocallyConnected

/-! Connected open neighborhoods in actual Boolean polynomial realizations.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Boolean restrictions inside the original realization subtype have finitely many actual connected components.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, relative finite component step. -/
theorem s2v_t11b_relative_formula_finite_components {n : ℕ}
    (f g : s2v_t11b_Formula n) :
    Finite (ConnectedComponents {x : f.realize | x.val ∈ g.realize}) := by
  let F : (s2v_t11b_Formula.inter f g).realize → {x : f.realize | x.val ∈ g.realize} :=
    fun y => ⟨⟨y.val, y.property.1⟩, y.property.2⟩
  have hF : Continuous F := (continuous_subtype_val.subtype_mk _).subtype_mk _
  have hs : Function.Surjective F := by
    rintro ⟨⟨x, hx⟩, hg⟩
    exact ⟨⟨x, hx, hg⟩, rfl⟩
  letI := s2v_t11b_formula_finite_components (.inter f g)
  exact Finite.of_surjective hF.connectedComponentsMap (hF.connectedComponentsMap_surjective hs)

/-- Every positive-radius ball in an actual Boolean realization has finitely many connected components.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, finite local component step. -/
theorem s2v_t11b_relative_ball_finite_components {n : ℕ}
    (f : s2v_t11b_Formula n) (x : f.realize) (r : ℝ) (hr : 0 < r) :
    Finite (ConnectedComponents (Metric.ball x r)) := by
  obtain ⟨g, hg⟩ := s2v_t11b_ball_formula x.val r hr
  have he : Metric.ball x r = {y : f.realize | y.val ∈ g.realize} := by
    ext y
    rw [hg]
    rfl
  rw [he]
  exact s2v_t11b_relative_formula_finite_components f g

/-- Every actual Boolean polynomial realization is locally connected, with its original Euclidean subtype topology.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, connected local neighborhood basis step. -/
theorem s2v_t11b_formula_locally_connected {n : ℕ} (f : s2v_t11b_Formula n) :
    LocallyConnectedSpace f.realize := by
  rw [locallyConnectedSpace_iff_subsets_isOpen_isConnected]
  intro x U hU
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hU
  let W := Metric.ball x r
  let a : W := ⟨x, Metric.mem_ball_self hr⟩
  letI := s2v_t11b_relative_ball_finite_components f x r hr
  let V : Set f.realize := Subtype.val '' connectedComponent a
  refine ⟨V, ?_, ?_, ?_, ?_⟩
  · rintro y ⟨z, hz, rfl⟩
    exact hball z.property
  · exact Metric.isOpen_ball.isOpenMap_subtype_val _
      (s2v_t11b_component_clopen_of_finite a).isOpen
  · exact ⟨a, mem_connectedComponent, rfl⟩
  · exact isConnected_connectedComponent.image _ continuous_subtype_val.continuousOn

end HodgeLean.Foundations.Program
