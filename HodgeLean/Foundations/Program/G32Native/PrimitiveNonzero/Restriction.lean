import HodgeLean.Foundations.Program.G32Native.PrimitiveNonzero.Defs
import HodgeLean.Foundations.Program.SchoenCycleC2SupportHelpers
import HodgeConjecture.Lemmas.AlgebraicTopology.Support.RelativeCohomologySheaf

/-! # Restriction away from component support -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicTopology AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Program.G32Native.PrimitiveNonzero

set_option backward.isDefEq.respectTransparency false in
/-- Forgetting support commutes with pullback along a continuous map. -/
theorem pullback_forget {X Y : TopCat.{0}} (f : X ⟶ Y)
    (S : Set Y) (n : ℕ) (c : CohomologyWithSupport ℚ Y S n) :
    cohomologyMap ℚ n f (forgetSupport ℚ Y S n c) =
      forgetSupport ℚ X (f ⁻¹' S) n (cohomologyWithSupportMap ℚ n f S c) := by
  have hdual := congrArg HomologicalComplex.linearDualMap
    (TopPair.Homotopy.relativeChainProjection_naturality (R := ℚ)
      (preimageSupportPairMap f S))
  rw [HomologicalComplex.linearDualMap_comp, HomologicalComplex.linearDualMap_comp] at hdual
  have hhom := congrArg (fun v => HomologicalComplex.homologyMap v n) hdual
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hhom
  exact (ConcreteCategory.congr_hom hhom c).symm

#print axioms pullback_forget
set_option backward.isDefEq.respectTransparency false in
/-- A map missing the support kills the underlying absolute class. -/
theorem pullback_forget_eq_zero {X Y : TopCat.{0}} (f : X ⟶ Y)
    (S : Set Y) (n : ℕ) (h : ∀ x : X, f x ∉ S)
    (c : CohomologyWithSupport ℚ Y S n) :
    cohomologyMap ℚ n f (forgetSupport ℚ Y S n c) = 0 := by
  rw [pullback_forget]
  have he : f ⁻¹' S = ∅ := Set.eq_empty_iff_forall_notMem.mpr h
  have hz : Subsingleton (CohomologyWithSupport ℚ X (f ⁻¹' S) n) := by
    rw [he]
    have hc : CategoryTheory.Limits.IsZero
        ((relativeChainFunctor ℚ).obj (TopPair.ofSubset (X := X) (∅ : Set X)ᶜ)) := by
      have hi : IsIso (TopPair.ofSubset (X := X) (∅ : Set X)ᶜ).map := by
        rw [Set.compl_empty]
        exact (TopCat.isIso_iff_isHomeomorph _).mpr (Homeomorph.Set.univ X).isHomeomorph
      have hchain : IsIso ((chainPairFunctor ℚ).obj
          (TopPair.ofSubset (X := X) (∅ : Set X)ᶜ)).hom := by
        change IsIso (((singularChainComplexFunctor.{0} (ModuleCat.{0} ℚ)).obj
          (ModuleCat.of ℚ ℚ)).map (TopPair.ofSubset (X := X) (∅ : Set X)ᶜ).map)
        infer_instance
      exact CategoryTheory.Limits.isZero_cokernel_of_epi
        ((chainPairFunctor ℚ).obj (TopPair.ofSubset (X := X) (∅ : Set X)ᶜ)).hom
    have hh := (HomologicalComplex.homologyFunctor (ModuleCat ℚ)
      (ComplexShape.down ℕ) n).map_isZero hc
    exact relativeCohomology_subsingleton ℚ _ n (ModuleCat.subsingleton_of_isZero hh)
  let := hz
  rw [Subsingleton.elim (cohomologyWithSupportMap ℚ n f S c) 0, map_zero]

#print axioms pullback_forget_eq_zero
/-- A component class restricts to zero along an immersion with disjoint scheme range. -/
theorem component_class_restrict_eq_zero
    {Q V W : Over (Spec ↧ℂ)} [IsIntegral Q.left]
    (ι : Q ⟶ W) [IsClosedImmersion ι.left] (j : V ⟶ W)
    (hdis : Disjoint (Set.range j.left) (Set.range ι.left))
    (k : ℕ) (c : s2e_supportedClass W (s2e_componentCycle ι ℚ) k) :
    s2e_pullback ℚ j (2 * k) (s2e_classToAbsolute W (s2e_componentCycle ι ℚ) k c) = 0 := by
  apply pullback_forget_eq_zero (TopCat.ofHom (Point.continuousMap j))
    (a3b4_cycleSupport W.hom (s2e_componentCycle ι ℚ)) (2 * k) _ c
  intro x
  rw [s2e_componentCycle_analytic_support]
  exact Set.disjoint_left.mp hdis ⟨x.underlying, rfl⟩

#print axioms component_class_restrict_eq_zero
end HodgeLean.Foundations.Program.G32Native.PrimitiveNonzero
