import HodgeLean.Foundations.AppellHumbertDefs

/-! # The Riemann relations, `H` from `E`: definitions (FROZEN)

The Gaussian lattice points `ℤ[i]² ⊆ ℂ²`, used by the falsification statement of
`RiemannFormHermitian`. HC no distance; AV milestone no distance.
-/

noncomputable section

namespace HodgeLean.Adapters

/-- The point `(n₀ + n₁ i, n₂ + n₃ i)` of the Gaussian lattice `ℤ[i]² ⊆ ℂ²`, a full lattice of
rank `4` with `ℤ`-basis `(1,0), (i,0), (0,1), (0,i)`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.1 (lattices in `ℂ^g`). -/
def gaussPoint (n : Fin 4 → ℤ) : Fin 2 → ℂ :=
  ![(n 0 : ℂ) + (n 1 : ℂ) * Complex.I, (n 2 : ℂ) + (n 3 : ℂ) * Complex.I]

example (n : Fin 4 → ℤ) :
    gaussPoint n 0 = (n 0 : ℂ) + (n 1 : ℂ) * Complex.I ∧
      gaussPoint n 1 = (n 2 : ℂ) + (n 3 : ℂ) * Complex.I := ⟨rfl, rfl⟩

end HodgeLean.Adapters
