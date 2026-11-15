import HodgeLean.Foundations.Program.G32Native.PairedC3ActualAffineGeneratorOverlap
import HodgeLean.Foundations.Program.G32Native.PairedC3AffineOverlapRefinement
import HodgeLean.Foundations.Program.G32Native.PairedC3SliceQuotientRegular
import HodgeLean.Foundations.Program.G32Native.PairedC3DominantCoefficientRegular

/-! # Affine ratio data retaining the chosen branch equations -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.RamifiedNormalization.StageFour
namespace HodgeLean.Foundations.Program.G32Native

/-- A supplied ratio chart, with its actual branch equations and slice
normalization. No overlap assertion is part of these data.
Source: Hartshorne, Algebraic Geometry, II.7.13. -/
structure PairedC3AffineRatioData {X Q : Scheme} (Y : Over (Spec ↧ℂ))
    (p : Y.left ⟶ X) (i : Q ⟶ X) (D₀ D₁ : X.IdealSheafData) where
  U : X.affineOpens
  V : Y.left.affineOpens
  liesOver : V.1 ≤ p ⁻¹ᵁ U.1
  u : Γ(X, U)
  v : Γ(X, U)
  α : Γ(X, U)
  k : Fin 2
  t : Γ(Y.left, V)
  ideal₀ : D₀.ideal U = Ideal.span {u}
  ideal₁ : D₁.ideal U = Ideal.span {v}
  slice : v - α * u ∈ i.ker.ideal U
  unit : IsUnit (Ideal.Quotient.mk (((D₀ ⊔ D₁) ⊔ i.ker).ideal U) α)
  rees : if k = 0 then (p.appLE U.1 V.1 liesOver).hom u = t * (p.appLE U.1 V.1 liesOver).hom v
    else (p.appLE U.1 V.1 liesOver).hom v = t * (p.appLE U.1 V.1 liesOver).hom u

namespace PairedC3AffineRatioData
variable {X Q : Scheme} {Y : Over (Spec ↧ℂ)} {p : Y.left ⟶ X} {i : Q ⟶ X}
  {D₀ D₁ : X.IdealSheafData}

/-- The actual normalized quotient-ring parameter of a supplied chart. -/
def parameter (A : PairedC3AffineRatioData Y p i D₀ D₁) :
    Γ(Y.left, A.V) ⧸ ((((D₀ ⊔ D₁) ⊔ i.ker).comap p).ideal A.V) :=
  let F := pairedC3AffineResidualCoefficient p ((D₀ ⊔ D₁) ⊔ i.ker) A.U A.V A.liesOver
  let β := Units.map F.toMonoidHom A.unit.unit
  (if A.k = 0 then (β : _) else ↑β⁻¹) *
    Ideal.Quotient.mk ((((D₀ ⊔ D₁) ⊔ i.ker).comap p).ideal A.V) A.t

/-- The map retains the original residual structure morphism. -/
def map (A : PairedC3AffineRatioData Y p i D₀ D₁) :=
  pairedC3ResidualProjectiveMap Y (((D₀ ⊔ D₁) ⊔ i.ker).comap p) A.V A.k A.parameter

/-- Restricting the specified ratio map uses the actual residual quotient
restriction, with its original complex algebra structure. -/
theorem map_restriction (A : PairedC3AffineRatioData Y p i D₀ D₁)
    (W : Y.left.affineOpens) (hWV : W.1 ≤ A.V.1) :
    Spec.map (CommRingCat.ofHom (pairedC3AffineResidualRestriction
      (((D₀ ⊔ D₁) ⊔ i.ker).comap p) A.V W hWV)) ≫ A.map.left =
    (pairedC3ResidualProjectiveMap Y (((D₀ ⊔ D₁) ⊔ i.ker).comap p) W A.k
      (pairedC3AffineResidualRestriction (((D₀ ⊔ D₁) ⊔ i.ker).comap p)
        A.V W hWV A.parameter)).left := by
  exact pairedC3_residual_projective_restriction Y _ A.V W hWV A.k A.parameter

end PairedC3AffineRatioData
#print axioms PairedC3AffineRatioData.map_restriction
end HodgeLean.Foundations.Program.G32Native
