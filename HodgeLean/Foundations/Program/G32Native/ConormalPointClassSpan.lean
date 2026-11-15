import HodgeLean.Foundations.Program.G32Native.ConormalPointSectionsExt
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Original local ideal classes span the actual conormal point fibre -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Foundations.Curves.Picard.LineBundles
namespace HodgeLean.Foundations.Program.G32Native

/-- Original local ideal classes on a containing actual affine open span
the entire original conormal point fibre over the original complex scalars. -/
theorem conormalLocalClasses_span {Q W : Over (Spec ↧ℂ)} (i : Q ⟶ W)
    [IsClosedImmersion i.left] (d : ℕ) [SmoothOfRelativeDimension d W.hom]
    (x : ComplexPoint Q) (U : W.left.Opens) (hU : IsAffineOpen U)
    (hx : Point.map i x ∈ Point.overOpen U) :
    Submodule.span ℂ (Set.range (fun s : unit U.toScheme ⟶
      (Scheme.Modules.pullback U.ι).obj (Conormal.idealModule i.left) =>
        conormalLocalClass i U s x hx)) = ⊤ := by
  apply Submodule.dualAnnihilator_eq_bot_iff.mp
  rw [Submodule.eq_bot_iff]
  intro ν hν
  change ν = 0
  apply conormalLocalClasses_ext i d x U hU hx ν 0
  intro s
  change ν (conormalLocalClass i U s x hx) = 0
  rw [Submodule.mem_dualAnnihilator] at hν
  exact hν _ (Submodule.subset_span (Set.mem_range_self s))

#print axioms conormalLocalClasses_span
end HodgeLean.Foundations.Program.G32Native
