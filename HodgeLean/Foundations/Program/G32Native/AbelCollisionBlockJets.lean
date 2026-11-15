import HodgeLean.Foundations.Program.G32Native.AbelCollisionBlocks
import HodgeLean.Foundations.Program.G32Native.AbelCollisionTraceJets

/-! # The full jet in an indexed family of collision blocks -/
noncomputable section
set_option maxHeartbeats 400000
open Filter
open scoped BigOperators Topology
namespace HodgeLean.Foundations.Program.G32Native
variable {A : Type} [Fintype A] [DecidableEq A] (m : A → ℕ)

/-- Restricting a literal trace to one block retains all other contributions as constants. -/
theorem collisionBlockInsert_trace (a : A) (u : Fin (m a) → ℂ) (H : A → ℂ → ℂ) :
    (∑ s : Σ b, Fin (m b), H s.1 (collisionBlockInsert m a u s)) =
      (∑ j, H a (u j)) + ∑ b ∈ Finset.univ.erase a, (m b : ℂ) * H b 0 := by
  rw [Fintype.sum_sigma]
  rw [← Finset.add_sum_erase Finset.univ
    (fun b => ∑ j : Fin (m b), H b (collisionBlockInsert m a u ⟨b, j⟩)) (Finset.mem_univ a)]
  simp only [collisionBlockInsert_self]
  congr 1
  apply Finset.sum_congr rfl
  intro b hb
  have hba : b ≠ a := (Finset.mem_erase.mp hb).1
  simp only [collisionBlockInsert_other m hba, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]

/-- All block restrictions detect the original coefficient functional. -/
theorem collision_block_functional_zero_iff
    (L : ((Σ b, Fin (m b)) → ℂ) →L[ℂ] ℂ) :
    L = 0 ↔ ∀ a, L.comp (collisionBlockInsertion m a).toContinuousLinearMap = 0 := by
  classical
  constructor
  · intro h a
    rw [h]
    rfl
  · intro h
    have hl : L.toLinearMap = (0 : ((Σ b, Fin (m b)) → ℂ) →ₗ[ℂ] ℂ) := by
      apply (Pi.basisFun ℂ (Σ b, Fin (m b))).ext
      intro ⟨a, j⟩
      change L ((Pi.basisFun ℂ (Σ b, Fin (m b))) ⟨a, j⟩) = 0
      rw [Pi.basisFun_apply]
      have hv := congrArg (fun K : (Fin (m a) → ℂ) →L[ℂ] ℂ => K (Pi.single j 1)) (h a)
      change L (collisionBlockInsert m a (Pi.single j 1)) = 0 at hv
      rwa [collisionBlockInsert_single] at hv
    ext v
    exact congrArg (fun K : ((Σ b, Fin (m b)) → ℂ) →ₗ[ℂ] ℂ => K v) hl

/-- The original derivative vanishes exactly when every collision block has its full differential jet. -/
theorem collision_block_trace_jet_kernel
    (f : ((Σ b, Fin (m b)) → ℂ) → ℂ) (H : A → ℂ → ℂ)
    (p : A → FormalMultilinearSeries ℂ ℂ ℂ)
    (hf : DifferentiableAt ℂ f 0) (hp : ∀ a, HasFPowerSeriesAt (H a) (p a) 0)
    (c : ℂ) (he : ∀ᶠ z in 𝓝 (0 : (Σ b, Fin (m b)) → ℂ),
      f (collisionBlockCoefficients m z) = (∑ s : Σ b, Fin (m b), H s.1 (z s)) + c) :
    fderiv ℂ f 0 = 0 ↔ ∀ a, (m a : ℕ∞) ≤ analyticOrderAt (deriv (H a)) 0 := by
  rw [collision_block_functional_zero_iff]
  apply forall_congr'
  intro a
  let I := (collisionBlockInsertion m a).toContinuousLinearMap
  have hdf : HasFDerivAt f (fderiv ℂ f 0) (I 0) := by
    rw [map_zero]
    exact hf.hasFDerivAt
  have hcomp := hdf.comp 0 I.hasFDerivAt
  have hi : Tendsto I (𝓝 0) (𝓝 0) := by
    simpa only [map_zero] using I.continuous.continuousAt.tendsto (x := 0)
  let cₐ := (∑ b ∈ Finset.univ.erase a, (m b : ℂ) * H b 0) + c
  have heₐ : ∀ᶠ u in 𝓝 (0 : Fin (m a) → ℂ),
      f (I (collisionMonicCoefficients u)) = (∑ j, H a (u j)) + cₐ := by
    filter_upwards [hi.eventually he] with u hu
    change f (collisionBlockCoefficients m (collisionBlockInsert m a u)) =
      (∑ s : Σ b, Fin (m b), H s.1 (collisionBlockInsert m a u s)) + c at hu
    rw [collisionBlockCoefficients_insert, collisionBlockInsert_trace] at hu
    exact hu.trans (by ring)
  have hj := collision_descended_trace_jet_kernel (fun u => f (I u)) (H a) (p a)
    hcomp.differentiableAt (hp a) cₐ heₐ
  change fderiv ℂ (f ∘ I) 0 = 0 ↔ (m a : ℕ∞) ≤ analyticOrderAt (deriv (H a)) 0 at hj
  rw [hcomp.fderiv] at hj
  exact hj

#print axioms collisionBlockInsert_trace
#print axioms collision_block_functional_zero_iff
#print axioms collision_block_trace_jet_kernel
end HodgeLean.Foundations.Program.G32Native
