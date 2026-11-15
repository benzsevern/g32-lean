import HodgeLean.Foundations.AnalyticSubset
import HodgeLean.Foundations.AutomorphyLineBundleDefs

/-! # Definitions for the analytic divisor spec (Chow/GAGA, first stage)

The divisor of a theta function, as a subset of the complex torus `V ⧸ Λ`: the image of the zero
set of `θ` under the projection `V → V ⧸ Λ`. No closedness, analyticity or algebraicity is built
in; those are statements of `HodgeLean.Foundations.AnalyticDivisorAlgebraic`.
HC no distance; AV milestone no distance.
-/

noncomputable section

namespace HodgeLean.Foundations.AnalyticDivisorAlgebraic

open AppellHumbert AutomorphyLineBundle

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

/-- The (set-theoretic) divisor of a function `θ : V → ℂ` on the torus of an Appell--Humbert
datum: the image in `V ⧸ Λ` of the zero set of `θ`. For a theta function `θ ∈ sections D` this
is the support of the divisor of the corresponding section of the line bundle `L(H, χ)`.

Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §4.1 (the divisor `(θ)` of a
theta function, and the divisor of a section of `L(H, χ)`). -/
def thetaDivisor (D : Datum (V := V)) (θ : V → ℂ) : Set (Torus D.lattice) :=
  proj D.lattice '' {v | θ v = 0}

example (D : Datum (V := V)) (θ : V → ℂ) (v : V) (hv : θ v = 0) :
    proj D.lattice v ∈ thetaDivisor D θ :=
  ⟨v, hv, rfl⟩

end HodgeLean.Foundations.AnalyticDivisorAlgebraic
