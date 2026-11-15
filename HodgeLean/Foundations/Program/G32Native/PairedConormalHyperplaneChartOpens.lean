import HodgeLean.Foundations.Program.G32Native.PairedConormalHyperplaneFrames
import HodgeLean.Foundations.Program.G32Native.PairedConormalPolynomialOpens

/-! # The actual Cartier charts retain their homogeneous coordinate opens -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexProjectiveSpace MvPolynomial
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- The normalized Cartier chart image is exactly its specified homogeneous basic open. -/
theorem conormal_hyperplane_chartOpen_eq_coordinate (k : ℕ) (i : Fin (k + 1)) :
    (paired_hyperplaneChartOpen k i).1 = projectiveSpaceBasicOpen k (X i) := by
  change s2e_s2b_chart i ''ᵁ ⊤ = _
  rw [Scheme.Hom.image_top_eq_opensRange]
  apply TopologicalSpace.Opens.ext
  simpa only [Scheme.Hom.coe_opensRange] using s2e_chart_range i

end HodgeLean.Foundations.Program.G32Native
