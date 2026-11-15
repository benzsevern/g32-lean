import HodgeLean.Foundations.Program.G32Native.PELSplitDomain
import HodgeLean.Foundations.Program.FoundationVocabDefs

noncomputable section
set_option maxRecDepth 8000
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj TensorProduct Quaternion
open HodgeLean.Papers HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
namespace HodgeLean.Foundations.Program.GeneralTypeIII

/-- An algebraic realization of the entire retained period component on the
original reference lattice. The total space is a commutative group over a
connected base; the integral order operators extend over that base. The
period and integral marking equations specify the fibres. No Hodge-group
comparison or exactness of the fibre End⁰ action is a field.
Source: Abdulali, Annals 155 (2002), §§2.2–2.3;
Shimura, On analytic families of polarized abelian varieties and automorphic
functions, Annals 78 (1963), Propositions 15 and 17; Birkenhake–Lange, §9.6. -/
structure PELSplitFamily (R : PELSplitReference) where
  base : Over (Spec ↧ℂ)
  connected : _root_.IsConnected (Set.univ : Set base.left)
  abelian : RelativeAbelianScheme base.left
  projective : IsProjective abelian.total.hom
  point : PELSplitComponent R → (Over.mk (𝟙 (Spec ↧ℂ)) ⟶ base)
  onto : Function.Surjective point
  fibre : PELSplitComponent R → wtr_Variety 3
  polarized : ∀ z, wtr_PolarizedWeil 3 (fibre z)
  fibreIso : ∀ z, (fibre z).X ≅ (Over.pullback (point z).left).obj abelian.total
  mark : ∀ z, HQ R.B.X 1 ≃ₗ[ℚ] HQ (fibre z).X 1
  integralMark : ∀ z, abelianPeriodLattice R.B.X ≃+ abelianPeriodLattice (fibre z).X
  period_eq : ∀ z x l,
    abelianPeriod (fibre z).X (mark z x) (integralMark z l) = abelianPeriod R.B.X x l
  plane_eq : ∀ z, (pelSplitPlane R z.val).map ((mark z).toLinearMap.baseChange ℂ) =
    complexHolomorphicH1 (fibre z).X
  form_eq : ∀ z x y,
    polarizationForm (torusCohomology_cupProductOf (fibre z).X)
      (polarized z).nondegenerate (mark z x) (mark z y) =
    polarizationForm (torusCohomology_cupProductOf R.B.X) R.polarized.nondegenerate x y
  generator_eq : ∀ z x, mark z (R.B.W.J x) = (fibre z).W.J (mark z x)
  action : ∀ z, ℍ[ℚ, -3, 0, R.b] →ₐ[ℚ] AbelianEnd0 (fibre z).X
  action_eq : ∀ z d x,
    (abelianEnd0Action (fibre z).X (action z d)).unop (mark z x) =
      mark z ((abelianEnd0Action R.B.X (R.end0 d)).unop x)
  integral : ∀ z, R.order →+* AbelianEnd (fibre z).X
  integral_eq : ∀ z a, (1 : ℚ) ⊗ₜ[ℤ] integral z a = action z a.val
  integral_transport : ∀ z a l,
    geometricIntegralOperator (fibre z).X (integral z a) (integralMark z l) =
      integralMark z (R.integralAction a l)
  orderMap : R.order → (abelian.total ⟶ abelian.total)
  order_square : ∀ z a,
    (integral z a).hom.left ≫ (fibreIso z).hom.left ≫ Limits.pullback.fst _ _ =
      (fibreIso z).hom.left ≫ Limits.pullback.fst _ _ ≫ (orderMap a).left

namespace PELSplitFamily
variable {R : PELSplitReference} (F : PELSplitFamily R)

/-- The reference rational basis on each marked fibre. -/
def basis (z : PELSplitComponent R) : Module.Basis (Fin 12) ℚ (HQ (F.fibre z).X 1) :=
  R.basis.map (F.mark z)

/-- The actual Hodge group in the retained reference coordinates.
Source: Mumford, Families of abelian varieties (1966), §1. -/
def hodgeGroup (z : PELSplitComponent R) : Set (Matrix.GeneralLinearGroup (Fin 12) ℂ) :=
  g2_hodgeGroup (latticeHodgePieces (F.fibre z).X)
    (spec_latticeHodgePieces_isInternal (F.fibre z).X) (F.basis z)

/-- The smallest rational algebraic subgroup containing every fibre's Hodge group.
This defines the family group independently of quaternionic isometry equations.
Source: Deligne, Hodge cycles on abelian varieties (1982), §3;
Moonen–Zarhin, Hodge classes on abelian varieties of low dimension (1999), §1. -/
def genericGroup : Set (Matrix.GeneralLinearGroup (Fin 12) ℂ) :=
  ⋂₀ {G | g2_IsRatAlgSubgroup G ∧ ∀ z, F.hodgeGroup z ⊆ G}

/-- Sixfold data on every algebraic fibre. -/
theorem sixfold (z : PELSplitComponent R) :
    SixfoldData (F.fibre z).X (F.fibre z).W (F.fibre z).pol :=
  ⟨(F.polarized z).dim_eq, (F.polarized z).isWeilType,
    (F.polarized z).nondegenerate, (F.polarized z).rosati⟩
end PELSplitFamily

end HodgeLean.Foundations.Program.GeneralTypeIII
