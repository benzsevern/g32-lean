import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNObjects

/-! # The recursive negative split bundle as a finite coproduct -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- The specified injection of each negative summand into the recursive bundle. -/
def pairedC3NegativeSummand (k : ℕ) :
    (s : ℕ) → Fin s → (pairedC3NegativeLine k ⟶ pairedC3SplitBundle k 0 s)
  | 0, j => Fin.elim0 j
  | s + 1, j => Fin.lastCases biprod.inr
      (fun i => pairedC3NegativeSummand k s i ≫ biprod.inl) j

/-- The cofan retains the original recursive bundle as its point. -/
def pairedC3NegativeCofan (k s : ℕ) : Cofan (fun _ : Fin s => pairedC3NegativeLine k) :=
  Cofan.mk (pairedC3SplitBundle k 0 s) (pairedC3NegativeSummand k s)

/-- The recursive bundle has the finite coproduct universal property. -/
def pairedC3NegativeCofanIsColimit (k : ℕ) :
    (s : ℕ) → IsColimit (pairedC3NegativeCofan k s)
  | 0 => by
    refine Cofan.IsColimit.mk _ (fun _ => 0) ?_ ?_
    · intro c j
      exact Fin.elim0 j
    · intro c m h
      apply (SheafOfModules.freeHomEquiv _ (I := Fin 0)).injective
      funext j
      exact Fin.elim0 j
  | s + 1 => by
    let ih := pairedC3NegativeCofanIsColimit k s
    refine Cofan.IsColimit.mk _
      (fun c => biprod.desc
        (Cofan.IsColimit.desc ih (fun j => c.inj j.castSucc)) (c.inj (Fin.last s))) ?_ ?_
    · intro c j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simp only [pairedC3NegativeCofan, cofan_mk_inj, pairedC3NegativeSummand,
          Fin.lastCases_last]
        exact biprod.inr_desc _ _
      · simp only [pairedC3NegativeCofan, cofan_mk_inj, pairedC3NegativeSummand,
          Fin.lastCases_castSucc]
        rw [Category.assoc, biprod.inl_desc]
        exact Cofan.IsColimit.fac ih (fun j => c.inj j.castSucc) i
    · intro c m h
      change pairedC3SplitBundle k 0 s ⊞ pairedC3NegativeLine k ⟶ c.pt at m
      apply biprod.hom_ext'
      · apply Cofan.IsColimit.hom_ext ih
        intro i
        rw [biprod.inl_desc]
        have hi := h i.castSucc
        simp only [pairedC3NegativeCofan, cofan_mk_inj, pairedC3NegativeSummand,
          Fin.lastCases_castSucc, Category.assoc] at hi
        exact hi.trans (Cofan.IsColimit.fac ih (fun j => c.inj j.castSucc) i).symm
      · rw [biprod.inr_desc]
        simpa only [pairedC3NegativeCofan, cofan_mk_inj, pairedC3NegativeSummand,
          Fin.lastCases_last] using h (Fin.last s)

/-- The finite coproduct notation and the original recursive bundle agree. -/
def pairedC3SplitBundleCoproduct (k s : ℕ) :
    pairedC3SplitBundle k 0 s ≅ ∐ (fun _ : Fin s => pairedC3NegativeLine k) :=
  ((coproductIsCoproduct (fun _ : Fin s => pairedC3NegativeLine k)).coconePointUniqueUpToIso
    (pairedC3NegativeCofanIsColimit k s)).symm

#print axioms pairedC3NegativeCofanIsColimit
#print axioms pairedC3SplitBundleCoproduct
end HodgeLean.Foundations.Program.G32Native
