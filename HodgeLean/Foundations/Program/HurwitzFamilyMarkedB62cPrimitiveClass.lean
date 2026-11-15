import Mathlib.LinearAlgebra.Span.Basic

noncomputable section
namespace HodgeLean.Foundations.Program

theorem b6m_span_eq_top_of_rank_one_detector
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (e : M ≃ₗ[R] R) (l : M →ₗ[R] R) (x : M) (hx : l x = 1) :
    Submodule.span R {x} = ⊤ := by
  rw [Submodule.span_singleton_eq_top_iff]
  intro y
  let u := e.symm 1
  have hux : e x • u = x := by
    apply e.injective
    simp [u]
  have hunit : e x * l u = 1 := by
    calc
      _ = l (e x • u) := (map_smul l (e x) u).symm
      _ = 1 := by rw [hux, hx]
  refine ⟨e y * l u, ?_⟩
  apply e.injective
  simp only [map_smul, smul_eq_mul]
  calc
    (e y * l u) * e x = e y * (e x * l u) := by rw [mul_assoc, mul_comm (l u) (e x)]
    _ = e y := by rw [hunit, mul_one]

theorem b6m_smul_bijective_of_span_rank_one
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (e : M ≃ₗ[R] R) (x : M) (hx : Submodule.span R {x} = ⊤) :
    Function.Bijective (fun r : R => r • x) := by
  have hsurj := (Submodule.span_singleton_eq_top_iff R x).mp hx
  obtain ⟨s, hs⟩ := hsurj (e.symm 1)
  have hunit : s * e x = 1 := by
    simpa only [map_smul, smul_eq_mul, LinearEquiv.apply_symm_apply] using congrArg e hs
  have hleft (r : R) : s * e (r • x) = r := by
    simp only [map_smul, smul_eq_mul]
    rw [mul_left_comm, hunit, mul_one]
  refine ⟨?_, hsurj⟩
  intro a b hab
  simpa only [hleft] using congrArg (fun z => s * e z) hab

end HodgeLean.Foundations.Program
