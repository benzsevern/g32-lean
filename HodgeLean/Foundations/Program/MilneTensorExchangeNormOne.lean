import HodgeLean.Foundations.Program.MilneTensorExchangeAction
import HodgeLean.Foundations.Program.MilneFactors

noncomputable section
namespace HodgeLean.Foundations.Program

theorem m1b_exchange_norm_one_image (d a b : ℕ) :
    (m1b_exchangeModuleEquiv d a b).conj ''
      (m1b_exchangeMultiplicityAction d a b '' {X | m1_exchange d X * X = 1}) =
      Set.range (m1b_vectorDualMultiplicityAction (W := Fin d → ℂ) a b) := by
  let e : Matrix (Fin d) (Fin d) ℂ ≃ₐ[ℂ] Module.End ℂ (Fin d → ℂ) := Matrix.toLinAlgEquiv'
  ext u
  constructor
  · rintro ⟨_, ⟨X, hX, rfl⟩, rfl⟩
    obtain ⟨U, rfl⟩ := (m1_exchange_norm_one d X).mp hX
    exact ⟨Units.map e.toMonoidHom U, (m1b_exchangeMultiplicity_conj d a b U).symm⟩
  · rintro ⟨g, rfl⟩
    obtain ⟨U, hU⟩ := (Units.mapEquiv e.toMulEquiv).surjective g
    have hU' : Units.map e.toMonoidHom U = g := hU
    refine ⟨m1b_exchangeMultiplicityAction d a b (U.val, U.inv.transpose),
      ⟨(U.val, U.inv.transpose), ?_, rfl⟩, ?_⟩
    · exact (m1_exchange_norm_one d _).mpr ⟨U, rfl⟩
    · rw [m1b_exchangeMultiplicity_conj, hU']

end HodgeLean.Foundations.Program
