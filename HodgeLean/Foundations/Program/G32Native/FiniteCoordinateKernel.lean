import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Kernel control through finite normal evaluation coordinates -/
noncomputable section
set_option maxHeartbeats 200000
namespace HodgeLean.Foundations.Program.G32Native

/-- A surjective coordinate map of the expected normal dimension detects
all vectors in the normal kernel, and hence every linear factor of that kernel. -/
theorem ker_le_of_surjective_normal_coordinates
    {K V N E F : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup N] [Module K N]
    [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]
    [FiniteDimensional K N] [FiniteDimensional K E]
    (P : V →ₗ[K] N) (T : N →ₗ[K] E) (R : V →ₗ[K] V)
    (B : V →ₗ[K] E) (Q : V →ₗ[K] F) (D : V →ₗ[K] F)
    (hB : B = T.comp (P.comp R)) (hD : D = Q.comp R)
    (hdim : Module.finrank K N = Module.finrank K E)
    (hsurj : Function.Surjective B) (hker : LinearMap.ker P ≤ LinearMap.ker Q) :
    LinearMap.ker B ≤ LinearMap.ker D := by
  have hTs : Function.Surjective T := by
    intro e
    obtain ⟨v, hv⟩ := hsurj e
    exact ⟨P (R v), by simpa only [hB, LinearMap.comp_apply] using hv⟩
  have hTi := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hTs
  intro v hv
  have hP : P (R v) = 0 := by
    apply hTi
    rw [map_zero]
    simpa only [hB, LinearMap.comp_apply] using (show B v = 0 from hv)
  have hQ : Q (R v) = 0 := hker hP
  change D v = 0
  simpa only [hD, LinearMap.comp_apply] using hQ

#print axioms ker_le_of_surjective_normal_coordinates
end HodgeLean.Foundations.Program.G32Native
