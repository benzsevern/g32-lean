import HodgeLean.Foundations.Program.G32Native.RegularQuotientIndependent
import HodgeLean.Foundations.Program.G32Native.IndependentParameters

/-! Retain labelled equations among a regular system of local parameters. -/
noncomputable section
set_option maxHeartbeats 400000
open IsLocalRing
namespace HodgeLean.Foundations.Program

/-- Equations of a regular quotient with expected codimension extend to labelled parameters. -/
theorem g32l4_regular_quotient_labelled_parameters
    {R : Type*} [CommRing R] [IsRegularLocalRing R]
    (I : Ideal R) [IsRegularLocalRing (R ⧸ I)]
    {ι : Type*} [Fintype ι] (f : ι → R)
    (hf : ∀ i, f i ∈ maximalIdeal R)
    (hgen : Ideal.span (Set.range f) = I)
    (hcodim : ringKrullDim (R ⧸ I) + Fintype.card ι = ringKrullDim R) :
    ∃ (n : ℕ) (z : Fin n → R) (c : ι ↪ Fin n),
      IsRegularSystemOfParameters z ∧ ∀ i, z (c i) = f i := by
  exact g32l4_extend_independent_parameters f hf
    (g32l4_regular_quotient_equations_independent I f hf hgen hcodim)

end HodgeLean.Foundations.Program
