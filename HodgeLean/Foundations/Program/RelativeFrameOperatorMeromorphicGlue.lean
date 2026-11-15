import HodgeLean.Foundations.Program.RelativeFrameOperatorPole

set_option maxHeartbeats 400000
noncomputable section
open Set Manifold Filter Topology
open scoped ContDiff BoundedContinuousFunction
namespace HodgeLean.Foundations.Program

def rf4_localGlue {X I : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (e : I → OpenPartialHomeomorph X ℂ) (U : I → Set ℂ)
    (hcover : ∀ p : X, ∃ i, p ∈ (e i).source ∧ e i p ∈ U i)
    (f : I → ℂ → ℂ) (q : TangentBundle 𝓘(ℂ, ℂ) X) : ℂ :=
  let i := Classical.choose (hcover q.1)
  f i (e i q.1) * (show ℂ from mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (e i) q.1 q.2)

theorem rf4_localGlue_eq {X I : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] (e : I → OpenPartialHomeomorph X ℂ) (U : I → Set ℂ)
    (he : ∀ i, e i ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω X)
    (hcover : ∀ p : X, ∃ i, p ∈ (e i).source ∧ e i p ∈ U i) (f : I → ℂ → ℂ)
    (hcompat : ∀ i j z, z ∈ U i → ∀ w, w ∈ U j → (e i).symm z = (e j).symm w →
      f i z = f j w * deriv (e j ∘ (e i).symm) z)
    (i : I) (p : X) (hp : p ∈ (e i).source) (hU : e i p ∈ U i)
    (v : TangentSpace 𝓘(ℂ, ℂ) p) :
    rf4_localGlue e U hcover f ⟨p, v⟩ =
      f i (e i p) * (show ℂ from mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (e i) p v) := by
  let j := Classical.choose (hcover p)
  have hj : p ∈ (e j).source ∧ e j p ∈ U j := Classical.choose_spec (hcover p)
  have hbase := hcompat i j (e i p) hU (e j p) hj.2
    (by rw [(e i).left_inv hp, (e j).left_inv hj.1])
  exact (rf4_chartForm_transition (e i) (e j) (he i) (he j) p hp hj.1 v
    (f i (e i p)) (f j (e j p)) hbase).symm

theorem rf4_localGlue_fibre {X I : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (e : I → OpenPartialHomeomorph X ℂ) (U : I → Set ℂ)
    (hcover : ∀ p : X, ∃ i, p ∈ (e i).source ∧ e i p ∈ U i) (f : I → ℂ → ℂ) :
    HurwitzPrymRR_IsLinear (rf4_localGlue e U hcover f) := by
  intro p c v w
  let i := Classical.choose (hcover p)
  let B : ℂ →L[ℂ] ℂ := mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (e i) p
  have hnum (A : ℂ →L[ℂ] ℂ) (b c u t : ℂ) :
      b * A (c * u + t) = c * (b * A u) + b * A t := by
    rw [map_add, ← smul_eq_mul c u, map_smul]
    simp only [smul_eq_mul]
    ring
  exact hnum B (f i (e i p)) c v w

theorem rf4_localGlue_eq_of_agree {X I : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    (e : I → OpenPartialHomeomorph X ℂ) (U : I → Set ℂ)
    (hcover : ∀ p : X, ∃ i, p ∈ (e i).source ∧ e i p ∈ U i) (f : I → ℂ → ℂ)
    (hag : ∀ i j p, p ∈ (e i).source → e i p ∈ U i → p ∈ (e j).source → e j p ∈ U j →
      ∀ v : TangentSpace 𝓘(ℂ, ℂ) p,
      f i (e i p) * (show ℂ from mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (e i) p v) =
        f j (e j p) * (show ℂ from mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (e j) p v))
    (i : I) (p : X) (hp : p ∈ (e i).source) (hU : e i p ∈ U i)
    (v : TangentSpace 𝓘(ℂ, ℂ) p) :
    rf4_localGlue e U hcover f ⟨p, v⟩ =
      f i (e i p) * (show ℂ from mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (e i) p v) := by
  let j := Classical.choose (hcover p)
  have hj : p ∈ (e j).source ∧ e j p ∈ U j := Classical.choose_spec (hcover p)
  exact hag j i p hj.1 hj.2 hp hU v

end HodgeLean.Foundations.Program
