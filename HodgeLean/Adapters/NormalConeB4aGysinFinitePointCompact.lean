import HodgeLean.Adapters.NormalConeB4aGysinFiniteEvaluationBound
import HodgeLean.Adapters.NormalConeB4aGysinAlgebraHomClosed
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas

noncomputable section
namespace HodgeLean.Adapters

/-- The complex evaluation map of a finite algebra has compact inverse
images of compact sets of base evaluations. -/
theorem a3b4a_gysin_finite_evaluation_compact_preimage
    {B T : Type} [CommRing B] [CommRing T] [Algebra ℂ B] [Algebra ℂ T]
    [Algebra B T] [IsScalarTower ℂ B T] [Module.Finite B T]
    (K : Set (B →ₐ[ℂ] ℂ)) (hK : IsCompact K) :
    IsCompact {w : T →ₐ[ℂ] ℂ | w.comp (IsScalarTower.toAlgHom ℂ B T) ∈ K} := by
  classical
  choose F hF using fun t : T => a3b4a_gysin_finite_evaluation_bound (B := B) t
  have hbnd (t : T) : ∃ b : ℝ, ∀ u ∈ K, F t u ≤ b := by
    obtain ⟨b, hb⟩ := (hK.image (F t).continuous).bddAbove
    exact ⟨b, fun u hu => hb ⟨u, hu, rfl⟩⟩
  choose b hb using hbnd
  let π := fun w : T →ₐ[ℂ] ℂ => w.comp (IsScalarTower.toAlgHom ℂ B T)
  have hπ : Continuous π := by
    apply continuous_induced_rng.mpr
    exact continuous_pi fun c =>
      AlgebraicGeometry.ComplexPoint.continuous_affineAlgebraHom_apply T (algebraMap B T c)
  let E := fun w : T →ₐ[ℂ] ℂ => (w : T → ℂ)
  have hE := a3b4a_gysin_algHom_isClosedEmbedding T
  letI : T2Space (B →ₐ[ℂ] ℂ) :=
    (a3b4a_gysin_algHom_isClosedEmbedding B).isEmbedding.t2Space
  have hclosed : IsClosed (π ⁻¹' K) := hK.isClosed.preimage hπ
  have himage : IsClosed (E '' (π ⁻¹' K)) := hE.isClosedMap _ hclosed
  have hbox : IsCompact {f : T → ℂ | ∀ t, f t ∈ Metric.closedBall (0 : ℂ) (b t)} :=
    isCompact_pi_infinite fun t => isCompact_closedBall (0 : ℂ) (b t)
  apply hE.isEmbedding.isCompact_iff.mpr
  apply hbox.of_isClosed_subset himage
  rintro f ⟨w, hw, rfl⟩
  intro t
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (hF t w).trans (hb t (π w) hw)

end HodgeLean.Adapters
