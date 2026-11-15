import HodgeLean.Foundations.QuotientDuality.RetainedCycleExtendedCap
import HodgeLean.Foundations.QuotientDuality.RetainedCycleDerivedOrientation

noncomputable section
open CategoryTheory Limits AlgebraicTopology AlgebraicTopology.Singular CochainComplex.HomComplex
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual ambient cocycle cap action on the integer-indexed chain-sheaf complex. -/
def retainedChainSheafCapShiftHom (X : TopCat.{0}) (p : ℕ)
    (φ : Simplicial.Cochain ℚ (TopCat.toSSet.obj X) p)
    (hφ : Simplicial.coboundary ℚ p φ = 0) :
    singularChainSheafCochainComplex ℚ X ⟶ (singularChainSheafCochainComplex ℚ X)⟦(p : ℤ)⟧ :=
  retainedExtendedCapShiftHom (singularChainSheafComplex ℚ X) p
    (fun q => retainedChainSheafAmbientCap X p q φ) (by
      intro q
      simpa only [singularChainSheafComplex_d] using
        retained_chain_sheaf_ambient_cap_boundary X p q φ hφ)

/-- The actual sheaf shift morphism has the specified original chain cap components. -/
theorem retained_chain_sheaf_cap_shift_component (X : TopCat.{0}) (p q : ℕ)
    (φ : Simplicial.Cochain ℚ (TopCat.toSSet.obj X) p)
    (hφ : Simplicial.coboundary ℚ p φ = 0) :
    ((Cocycle.equivHomShift (retainedChainSheafCapShiftHom X p φ hφ)).1).v
      (-((p + q : ℕ) : ℤ)) (-(q : ℤ)) (by push_cast; omega) =
    ((singularChainSheafComplex ℚ X).extendXIso ComplexShape.embeddingDownNat
      (ComplexShape.embeddingDownNat_f (p + q))).hom ≫
    retainedChainSheafAmbientCap X p q φ ≫
    ((singularChainSheafComplex ℚ X).extendXIso ComplexShape.embeddingDownNat
      (ComplexShape.embeddingDownNat_f q)).inv :=
  retained_extended_cap_shift_hom_component _ p q _ _

local instance (X : TopCat.{0}) : HasDerivedCategory (TopCat.Sheaf AddCommGrpCat X) :=
  HasDerivedCategory.standard _

/-- Localization of the actual shifted chain-sheaf cap morphism. -/
def retainedDerivedCapAction (X : TopCat.{0}) (p : ℕ)
    (φ : Simplicial.Cochain ℚ (TopCat.toSSet.obj X) p)
    (hφ : Simplicial.coboundary ℚ p φ = 0) :
    DerivedCategory.Q.obj (singularChainSheafCochainComplex ℚ X) ⟶
      (DerivedCategory.Q.obj (singularChainSheafCochainComplex ℚ X))⟦(p : ℤ)⟧ :=
  DerivedCategory.Q.map (retainedChainSheafCapShiftHom X p φ hφ) ≫
    (DerivedCategory.Q.commShiftIso (p : ℤ)).hom.app (singularChainSheafCochainComplex ℚ X)

/-- The actual derived cap action transported through the specified normalized orientation. -/
def retainedOrientedDerivedCapAction (X : TopCat.{0}) [T2Space X] (n : ℕ)
    (c : Homology ℚ X n) (ho : ∀ x, Function.Bijective (orientationLine X n c x))
    (hv : ∀ j : ℕ, j ≠ n → ∀ x : X, Subsingleton (orientationGroup X j x))
    (p : ℕ) (φ : Simplicial.Cochain ℚ (TopCat.toSSet.obj X) p)
    (hφ : Simplicial.coboundary ℚ p φ = 0) :
    ((DerivedCategory.singleFunctor (TopCat.Sheaf AddCommGrpCat X) 0).obj 𝓒(X; ℚ))⟦(n : ℤ)⟧ ⟶
      (((DerivedCategory.singleFunctor (TopCat.Sheaf AddCommGrpCat X) 0).obj 𝓒(X; ℚ))⟦(n : ℤ)⟧)⟦(p : ℤ)⟧ :=
  (retainedDerivedOrientationIso X n c ho hv).inv ≫ retainedDerivedCapAction X p φ hφ ≫
    (retainedDerivedOrientationIso X n c ho hv).hom⟦(p : ℤ)⟧'

/-- The constructed oriented action intertwines with the actual chain-model cap action. -/
theorem retained_derived_orientation_cap_intertwines (X : TopCat.{0}) [T2Space X] (n : ℕ)
    (c : Homology ℚ X n) (ho : ∀ x, Function.Bijective (orientationLine X n c x))
    (hv : ∀ j : ℕ, j ≠ n → ∀ x : X, Subsingleton (orientationGroup X j x))
    (p : ℕ) (φ : Simplicial.Cochain ℚ (TopCat.toSSet.obj X) p)
    (hφ : Simplicial.coboundary ℚ p φ = 0) :
    (retainedDerivedOrientationIso X n c ho hv).hom ≫
      retainedOrientedDerivedCapAction X n c ho hv p φ hφ =
    retainedDerivedCapAction X p φ hφ ≫
      (retainedDerivedOrientationIso X n c ho hv).hom⟦(p : ℤ)⟧' := by
  dsimp only [retainedOrientedDerivedCapAction]
  rw [Iso.hom_inv_id_assoc]

end HodgeLean.Foundations.QuotientDuality
