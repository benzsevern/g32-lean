import HodgeLean.Foundations.Program.MilneTensorCopyGeneration
import HodgeLean.Foundations.Program.MilneTensorTransport

noncomputable section
namespace HodgeLean.Foundations.Program
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem m1b_copies_one_conj (S : Set (Module.End ℂ V)) :
    (LinearEquiv.funUnique (Fin 1) ℂ V).conj '' (m1b_copies 1 '' S) = S := by
  have hconj (u : Module.End ℂ V) :
      (LinearEquiv.funUnique (Fin 1) ℂ V).conj (m1b_copies 1 u) = u := by
    apply LinearMap.ext
    intro v
    rfl
  ext u
  constructor
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    rwa [hconj]
  · intro hu
    exact ⟨m1b_copies 1 u, ⟨u, hu, rfl⟩, hconj u⟩

theorem m1b_generation_of_copies_one (S : Set (Module.End ℂ V)) (n : ℕ)
    (hgen : m1b_fixed (m1b_copies 1 '' S) n =
      m1b_products (m1b_fixed (m1b_copies 1 '' S) 2) n) :
    m1b_fixed S n = m1b_products (m1b_fixed S 2) n := by
  have h := (m1b_generation_conj_iff (LinearEquiv.funUnique (Fin 1) ℂ V) _ n).mp hgen
  rwa [m1b_copies_one_conj] at h

end HodgeLean.Foundations.Program
