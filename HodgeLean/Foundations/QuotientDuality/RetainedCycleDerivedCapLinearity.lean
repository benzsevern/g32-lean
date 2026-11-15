import HodgeLean.Foundations.QuotientDuality.RetainedCycleCapSheafCoboundary
import HodgeLean.Foundations.QuotientDuality.RetainedCycleRelativeCapLinearity

noncomputable section
open CategoryTheory Limits AlgebraicTopology AlgebraicTopology.Singular TopologicalSpace Opposite
open CochainComplex.HomComplex
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual presheaf cap operation is additive in ambient cochains. -/
theorem retained_chain_presheaf_cap_add (X : TopCat.{0}) (p q : ℕ)
    (φ ψ : Simplicial.Cochain ℚ (TopCat.toSSet.obj X) p) :
    retainedChainPresheafAmbientCap X p q (φ + ψ) =
      retainedChainPresheafAmbientCap X p q φ + retainedChainPresheafAmbientCap X p q ψ := by
  apply NatTrans.ext
  funext U
  have h := congrArg ((forget₂ (ModuleCat ℚ) AddCommGrpCat).map)
    (retained_relative_ambient_cap_add (TopPair.ofSubset (U.unop : Set X)ᶜ) p q φ ψ)
  simp only [Functor.map_add] at h
  exact h

/-- Sheafification retains additivity of actual ambient cap. -/
theorem retained_chain_sheaf_cap_add (X : TopCat.{0}) (p q : ℕ)
    (φ ψ : Simplicial.Cochain ℚ (TopCat.toSSet.obj X) p) :
    retainedChainSheafAmbientCap X p q (φ + ψ) =
      retainedChainSheafAmbientCap X p q φ + retainedChainSheafAmbientCap X p q ψ := by
  let F := presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat
  have h := congrArg F.map (retained_chain_presheaf_cap_add X p q φ ψ)
  simp only [Functor.map_add] at h
  exact h

universe u v

/-- Extension of actual graded cap maps is additive. -/
theorem retained_extended_cap_add {C : Type u} [Category.{v} C] [Preadditive C]
    [HasZeroObject C] (K : ChainComplex C ℕ) (p : ℕ)
    (cap cap' : ∀ q, K.X (p + q) ⟶ K.X q) :
    retainedExtendedCap K p (fun q => cap q + cap' q) =
      retainedExtendedCap K p cap + retainedExtendedCap K p cap' := by
  apply Cochain.ext
  intro i j h
  by_cases hj : j ≤ 0
  · simp only [retainedExtendedCap, Cochain.mk_v, Cochain.add_v, dite_eq_left hj,
      Preadditive.comp_add, Preadditive.add_comp]
  · exact (K.isZero_extend_X ComplexShape.embeddingDownNat j (fun q hq => by
      simp only [ComplexShape.embeddingDownNat_f] at hq
      omega)).eq_of_tgt _ _

/-- The actual shifted cap morphism is additive in ambient cocycles. -/
theorem retained_chain_sheaf_cap_shift_add (X : TopCat.{0}) (p : ℕ)
    (φ ψ : Simplicial.Cochain ℚ (TopCat.toSSet.obj X) p)
    (hφ : Simplicial.coboundary ℚ p φ = 0) (hψ : Simplicial.coboundary ℚ p ψ = 0)
    (hadd : Simplicial.coboundary ℚ p (φ + ψ) = 0) :
    retainedChainSheafCapShiftHom X p (φ + ψ) hadd =
      retainedChainSheafCapShiftHom X p φ hφ + retainedChainSheafCapShiftHom X p ψ hψ := by
  unfold retainedChainSheafCapShiftHom retainedExtendedCapShiftHom
  erw [← map_add]
  congr 1
  apply Subtype.ext
  change retainedExtendedCap (singularChainSheafComplex ℚ X) p
      (fun q => retainedChainSheafAmbientCap X p q (φ + ψ)) =
    retainedExtendedCap (singularChainSheafComplex ℚ X) p
      (fun q => retainedChainSheafAmbientCap X p q φ) +
    retainedExtendedCap (singularChainSheafComplex ℚ X) p
      (fun q => retainedChainSheafAmbientCap X p q ψ)
  rw [← retained_extended_cap_add]
  congr 1
  funext q
  exact retained_chain_sheaf_cap_add X p q φ ψ

/-- The actual derived cap action is additive in ambient cocycles. -/
theorem retained_derived_cap_add (X : TopCat.{0}) (p : ℕ)
    (φ ψ : Simplicial.Cochain ℚ (TopCat.toSSet.obj X) p)
    (hφ : Simplicial.coboundary ℚ p φ = 0) (hψ : Simplicial.coboundary ℚ p ψ = 0)
    (hadd : Simplicial.coboundary ℚ p (φ + ψ) = 0) :
    retainedDerivedCapAction X p (φ + ψ) hadd =
      retainedDerivedCapAction X p φ hφ + retainedDerivedCapAction X p ψ hψ := by
  unfold retainedDerivedCapAction
  rw [retained_chain_sheaf_cap_shift_add X p φ ψ hφ hψ hadd,
    Functor.map_add, Preadditive.add_comp]

/-- Adding an ambient coboundary leaves the actual derived cap action unchanged. -/
theorem retained_derived_cap_eq_of_eq_add_coboundary (X : TopCat.{0}) (p : ℕ)
    (φ ψ : Simplicial.Cochain ℚ (TopCat.toSSet.obj X) (p + 1))
    (hφ : Simplicial.coboundary ℚ (p + 1) φ = 0)
    (hψ : Simplicial.coboundary ℚ (p + 1) ψ = 0)
    (η : Simplicial.Cochain ℚ (TopCat.toSSet.obj X) p)
    (h : φ = ψ + Simplicial.coboundary ℚ p η) :
    retainedDerivedCapAction X (p + 1) φ hφ = retainedDerivedCapAction X (p + 1) ψ hψ := by
  subst φ
  rw [retained_derived_cap_add X (p + 1) ψ (Simplicial.coboundary ℚ p η)
    hψ (Simplicial.coboundary_coboundary ℚ p η) hφ,
    retained_derived_cap_coboundary_zero, add_zero]

/-- The specified orientation transport retains invariance under ambient coboundaries. -/
theorem retained_oriented_derived_cap_eq_of_eq_add_coboundary
    (X : TopCat.{0}) [T2Space X] (n : ℕ) (c : Homology ℚ X n)
    (ho : ∀ x, Function.Bijective (orientationLine X n c x))
    (hv : ∀ j : ℕ, j ≠ n → ∀ x : X, Subsingleton (orientationGroup X j x))
    (p : ℕ) (φ ψ : Simplicial.Cochain ℚ (TopCat.toSSet.obj X) (p + 1))
    (hφ : Simplicial.coboundary ℚ (p + 1) φ = 0)
    (hψ : Simplicial.coboundary ℚ (p + 1) ψ = 0)
    (η : Simplicial.Cochain ℚ (TopCat.toSSet.obj X) p)
    (h : φ = ψ + Simplicial.coboundary ℚ p η) :
    retainedOrientedDerivedCapAction X n c ho hv (p + 1) φ hφ =
      retainedOrientedDerivedCapAction X n c ho hv (p + 1) ψ hψ := by
  unfold retainedOrientedDerivedCapAction
  rw [retained_derived_cap_eq_of_eq_add_coboundary X p φ ψ hφ hψ η h]

end HodgeLean.Foundations.QuotientDuality
