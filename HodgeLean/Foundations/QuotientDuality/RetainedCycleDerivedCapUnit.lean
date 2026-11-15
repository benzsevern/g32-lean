import HodgeLean.Foundations.QuotientDuality.RetainedCycleExtendedCapUnit

noncomputable section
open CategoryTheory Limits AlgebraicTopology AlgebraicTopology.Singular CochainComplex.HomComplex
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual shifted sheaf cap by the constant unit is the canonical zero-shift morphism. -/
theorem retained_chain_sheaf_cap_shift_unit (X : TopCat.{0}) :
    retainedChainSheafCapShiftHom X 0 (HodgeLean.Foundations.Singular.unitCochain X)
      (HodgeLean.Foundations.Singular.coboundary_unitCochain X) =
      (shiftFunctorZero (CochainComplex (TopCat.Sheaf AddCommGrpCat X) ℤ) ℤ).inv.app
        (singularChainSheafCochainComplex ℚ X) := by
  unfold retainedChainSheafCapShiftHom retainedExtendedCapShiftHom
  have he (hd) :
      retainedExtendedCapCocycle (singularChainSheafComplex ℚ X) 0
        (fun q => retainedChainSheafAmbientCap X 0 q (HodgeLean.Foundations.Singular.unitCochain X)) hd =
      Cocycle.ofHom (𝟙 (singularChainSheafCochainComplex ℚ X)) := by
    apply Subtype.ext
    change retainedExtendedCap (singularChainSheafComplex ℚ X) 0
        (fun q => retainedChainSheafAmbientCap X 0 q (HodgeLean.Foundations.Singular.unitCochain X)) =
      Cochain.ofHom (𝟙 (singularChainSheafCochainComplex ℚ X))
    have hc : (fun q => retainedChainSheafAmbientCap X 0 q (HodgeLean.Foundations.Singular.unitCochain X)) =
        (fun q => ((singularChainSheafComplex ℚ X).XIsoOfEq (Nat.zero_add q)).hom) := by
      funext q
      exact retained_chain_sheaf_cap_unit X q
    rw [hc]
    exact retained_extended_cap_unit (singularChainSheafComplex ℚ X)
  erw [he]
  exact retained_identity_cocycle_shift_hom _

local instance (X : TopCat.{0}) : HasDerivedCategory (TopCat.Sheaf AddCommGrpCat X) :=
  HasDerivedCategory.standard _

/-- The actual derived cap by the unit is the canonical zero-shift morphism. -/
theorem retained_derived_cap_unit (X : TopCat.{0}) :
    retainedDerivedCapAction X 0 (HodgeLean.Foundations.Singular.unitCochain X)
      (HodgeLean.Foundations.Singular.coboundary_unitCochain X) =
      (shiftFunctorZero (DerivedCategory (TopCat.Sheaf AddCommGrpCat X)) ℤ).inv.app
        (DerivedCategory.Q.obj (singularChainSheafCochainComplex ℚ X)) := by
  unfold retainedDerivedCapAction
  rw [retained_chain_sheaf_cap_shift_unit]
  erw [Functor.commShiftIso_zero,
    Functor.CommShift.isoZero_hom_app, ← Category.assoc, ← Functor.map_comp]
  simp only [Iso.inv_hom_id_app]
  have hid : DerivedCategory.Q.map (𝟙 (singularChainSheafCochainComplex ℚ X)) =
      𝟙 (DerivedCategory.Q.obj (singularChainSheafCochainComplex ℚ X)) :=
    CategoryTheory.Functor.map_id _ _
  erw [hid]
  exact Category.id_comp _

/-- The actual singular cohomology unit acts by the canonical derived zero-shift map. -/
theorem retained_cohomology_derived_cap_unit (X : TopCat.{0}) :
    retainedCohomologyDerivedCapAction X 0 (HodgeLean.Foundations.Singular.unit X) =
      (shiftFunctorZero (DerivedCategory (TopCat.Sheaf AddCommGrpCat X)) ℤ).inv.app
        (DerivedCategory.Q.obj (singularChainSheafCochainComplex ℚ X)) := by
  change retainedCohomologyDerivedCapAction X 0
    (HodgeLean.Foundations.Singular.cohomologyClass X 0
      ⟨HodgeLean.Foundations.Singular.unitCochain X,
        HodgeLean.Foundations.Singular.coboundary_unitCochain X⟩) = _
  rw [retained_cohomology_derived_cap_on_class]
  exact retained_derived_cap_unit X

/-- Transport through the specified orientation preserves the actual unit normalization. -/
theorem retained_oriented_cohomology_derived_cap_unit
    (X : TopCat.{0}) [T2Space X] (n : ℕ) (c : Homology ℚ X n)
    (ho : ∀ x, Function.Bijective (orientationLine X n c x))
    (hv : ∀ j : ℕ, j ≠ n → ∀ x : X, Subsingleton (orientationGroup X j x)) :
    retainedOrientedCohomologyDerivedCapAction X n c ho hv 0
      (HodgeLean.Foundations.Singular.unit X) =
      (shiftFunctorZero (DerivedCategory (TopCat.Sheaf AddCommGrpCat X)) ℤ).inv.app
        (((DerivedCategory.singleFunctor (TopCat.Sheaf AddCommGrpCat X) 0).obj 𝓒(X; ℚ))⟦(n : ℤ)⟧) := by
  unfold retainedOrientedCohomologyDerivedCapAction
  rw [retained_cohomology_derived_cap_unit]
  have hn := (shiftFunctorZero (DerivedCategory (TopCat.Sheaf AddCommGrpCat X)) ℤ).inv.naturality
    (retainedDerivedOrientationIso X n c ho hv).hom
  erw [← hn]
  exact Iso.inv_hom_id_assoc _ _

end HodgeLean.Foundations.QuotientDuality
