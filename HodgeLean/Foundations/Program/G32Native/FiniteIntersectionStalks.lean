import HodgeLean.Ported.Hironaka.Scheme.IdealSheaf.StalkLe

/-! Finite branch intersections and their actual stalk ideals. -/
noncomputable section
open AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The stalk of a finite ideal-sheaf sum is the sum of the stalk ideals. -/
theorem g32l4_stalkIdeal_finset_sup {X : Scheme} {ι : Type*}
    (D : ι → X.IdealSheafData) (J : Finset ι) (x : X) :
    (J.sup D).stalkIdeal x = J.sup (fun i => (D i).stalkIdeal x) := by
  simp only [Finset.sup_eq_iSup, Scheme.IdealSheafData.stalkIdeal_iSup']

/-- A point belongs to a finite intersection exactly when it belongs to every labelled branch. -/
theorem g32l4_mem_support_finset_sup {X : Scheme} {ι : Type*}
    (D : ι → X.IdealSheafData) (J : Finset ι) (x : X) :
    x ∈ (J.sup D).support ↔ ∀ i ∈ J, x ∈ (D i).support := by
  simp only [Finset.sup_eq_iSup, Scheme.IdealSheafData.support_iSup,
    TopologicalSpace.Closeds.mem_iInf]

end HodgeLean.Foundations.Program
