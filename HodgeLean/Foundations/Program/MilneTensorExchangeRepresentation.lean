import HodgeLean.Foundations.Program.MilneTensorPairRepresentation
import HodgeLean.Foundations.Program.MilneTensorExchangeGeneration
import HodgeLean.Foundations.Program.MilneTensorNormOneTransport

noncomputable section
namespace HodgeLean.Foundations.Program

theorem m1b_exchange_representation_tensors {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (d : ℕ) (hd : 0 < d)
    (ρ : (Matrix (Fin d) (Fin d) ℂ × Matrix (Fin d) (Fin d) ℂ) →ₐ[ℂ] Module.End ℂ V)
    (r n : ℕ) :
    m1b_fixed (m1b_copies r '' (ρ '' {X | m1_exchange d X * X = 1})) n =
      m1b_products (m1b_fixed (m1b_copies r ''
        (ρ '' {X | m1_exchange d X * X = 1})) 2) n := by
  obtain ⟨a, b, E, hE⟩ := m1b_matrix_pair_coordinates d hd ρ
  have hconj (X) : E.conj (ρ X) = m1b_exchangeMultiplicityAction d a b X := by
    apply LinearMap.ext
    intro v
    simpa only [LinearEquiv.conj_apply_apply, E.apply_symm_apply] using hE X (E.symm v)
  have hset : E.conj '' (ρ '' {X | m1_exchange d X * X = 1}) =
      m1b_exchangeMultiplicityAction d a b '' {X | m1_exchange d X * X = 1} := by
    rw [Set.image_image]
    congr 1
    funext X
    exact hconj X
  apply (m1b_generation_conj_iff (m1b_copiesEquiv E r) _ n).mpr
  rw [m1b_copies_conj_image, hset]
  exact m1b_exchange_norm_one_tensors d a b r n

end HodgeLean.Foundations.Program
