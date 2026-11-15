import HodgeLean.Foundations.QuotientDuality.PersistenceCollapseNeighbourhood
import HodgeLean.Foundations.QuotientDuality.PersistenceCollapseContraction

/-! Fixed contractions on the actual neighbourhood image in the ambient quotient. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Topology
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual neighbourhood-collapse homeomorphism onto the ambient image. -/
def persistenceCollapseNeighbourhoodHomeomorph
    {X : Type*} [TopologicalSpace X] (A U : Set X) (hA : IsClosed A)
    (hAU : A ⊆ U) :
    Quotient (persistenceCollapseSetoid {u : U | u.val ∈ A}) ≃ₜ
      ((Quotient.mk (persistenceCollapseSetoid A)) '' U) :=
  IsHomeomorph.homeomorph _
    (persistence_collapse_neighbourhood_map_isHomeomorph A U hA hAU)

/-- The neighbourhood deformation descended onto its actual image in the quotient. -/
def persistenceCollapseImageContraction
    {X : Type*} [TopologicalSpace X] (A U : Set X) (hA : IsClosed A)
    (hAU : A ⊆ U) (r : C(U, U))
    (H : ContinuousMap.Homotopy (ContinuousMap.id U) r)
    (hpres : ∀ (t : unitInterval) (u : U), u.val ∈ A → (H (t, u)).val ∈ A)
    (hr : ∀ u : U, (r u).val ∈ A) (a : U) (ha : a.val ∈ A) :
    ContinuousMap.Homotopy
      (ContinuousMap.id ((Quotient.mk (persistenceCollapseSetoid A)) '' U))
      (ContinuousMap.const _ (persistenceCollapseNeighbourhoodProjection A U a)) := by
  let e := persistenceCollapseNeighbourhoodHomeomorph A U hA hAU
  let G := persistenceCollapseContraction {u : U | u.val ∈ A} r H hpres hr a ha
  refine { toFun := fun p => e (G (p.1, e.symm p.2))
           continuous_toFun := e.continuous.comp
             (G.continuous.comp (continuous_fst.prodMk
               (e.symm.continuous.comp continuous_snd)))
           map_zero_left := ?_
           map_one_left := ?_ }
  · intro y
    change e (G (0, e.symm y)) = y
    rw [G.apply_zero]
    exact e.apply_symm_apply y
  · intro y
    change e (G (1, e.symm y)) = _
    rw [G.apply_one]
    rfl

lemma persistence_collapse_image_contraction_fixed
    {X : Type*} [TopologicalSpace X] (A U : Set X) (hA : IsClosed A)
    (hAU : A ⊆ U) (r : C(U, U))
    (H : ContinuousMap.Homotopy (ContinuousMap.id U) r)
    (hpres : ∀ (t : unitInterval) (u : U), u.val ∈ A → (H (t, u)).val ∈ A)
    (hr : ∀ u : U, (r u).val ∈ A) (a : U) (ha : a.val ∈ A) (t : unitInterval) :
    persistenceCollapseImageContraction A U hA hAU r H hpres hr a ha
      (t, persistenceCollapseNeighbourhoodProjection A U a) =
        persistenceCollapseNeighbourhoodProjection A U a := by
  let e := persistenceCollapseNeighbourhoodHomeomorph A U hA hAU
  let G := persistenceCollapseContraction {u : U | u.val ∈ A} r H hpres hr a ha
  change e (G (t, e.symm (e (Quotient.mk _ a)))) = e (Quotient.mk _ a)
  rw [e.symm_apply_apply]
  apply congrArg e
  change Quotient.mk (persistenceCollapseSetoid {u : U | u.val ∈ A}) (H (t, a)) =
    Quotient.mk (persistenceCollapseSetoid {u : U | u.val ∈ A}) a
  exact Quotient.sound (Or.inr ⟨hpres t a ha, ha⟩)

end HodgeLean.Foundations.QuotientDuality
