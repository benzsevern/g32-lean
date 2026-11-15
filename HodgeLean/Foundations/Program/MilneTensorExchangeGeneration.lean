import HodgeLean.Foundations.Program.MilneTensorExchangeNormOne

noncomputable section
namespace HodgeLean.Foundations.Program

theorem m1b_exchange_norm_one_tensors (d a b r n : ℕ) :
    m1b_fixed (m1b_copies r '' (m1b_exchangeMultiplicityAction d a b ''
      {X | m1_exchange d X * X = 1})) n =
      m1b_products (m1b_fixed (m1b_copies r '' (m1b_exchangeMultiplicityAction d a b ''
        {X | m1_exchange d X * X = 1})) 2) n := by
  apply m1b_copies_generation
  apply (m1b_generation_conj_iff (m1b_exchangeModuleEquiv d a b) _ n).mpr
  rw [m1b_exchange_norm_one_image]
  exact m1b_vectorDualMultiplicity_generation a b n

end HodgeLean.Foundations.Program
