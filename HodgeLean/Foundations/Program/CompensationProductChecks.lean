import HodgeLean.Foundations.Program.CompensationProduct
import HodgeLean.Foundations.Curves.CubicS13Defs

/-! # Positive-dimensional checks for the compensation product -/

noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

open CategoryTheory AlgebraicGeometry MonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters

namespace HodgeLean.Foundations.Program

/-- The scheme witness in the product definitions is a surface.
Source: `cp_product_dim`, `Curves.E_dim`. -/
theorem cp_cubic_surface_dim :
    TopologicalSpace.dim (Curves.E ⊗ Curves.E).left = 2 := by
  rw [cp_product_dim, Curves.E_dim]

/-- The surface witness has four independent degree-one rational classes.
Source: `TorusCohomology.finrank_eq`, `cp_cubic_surface_dim`. -/
theorem cp_cubic_surface_finrank_H1 :
    Module.finrank ℚ (HQ (Curves.E ⊗ Curves.E) 1) = 4 := by
  rw [(torusCohomology_cupProductOf (Curves.E ⊗ Curves.E)).finrank_eq,
    cp_cubic_surface_dim]

end HodgeLean.Foundations.Program
