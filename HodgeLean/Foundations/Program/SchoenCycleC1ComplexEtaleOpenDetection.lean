import HodgeLean.Foundations.Program.SchoenCycleC1EtaleBaseUnion
import HodgeLean.Foundations.Program.SchoenCycleC1EtaleAffineChartHelpers
import HodgeLean.Foundations.Program.SchoenCycleC1FiniteFibreComplexPoints

/-! # Detection of actual etale base restrictions by complex neighbourhoods -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- Actual etale neighbourhoods of every complex point in a base open give
etaleness over that entire open of a locally finite type complex scheme. -/
theorem s2e_c1_etale_restriction_of_complex_neighbourhoods
    (X : Scheme) (Y : Over (Spec ↧ℂ)) [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y.left) (W : Y.left.Opens)
    (hlocal : ∀ y : ComplexPoint Y, y.underlying ∈ W →
      ∃ U : Y.left.Opens, y.underlying ∈ U ∧ Etale (f ∣_ U)) : Etale (f ∣_ W) := by
  classical
  letI : JacobsonSpace Y.left := LocallyOfFiniteType.jacobsonSpace Y.hom
  let I := {y : ComplexPoint Y // y.underlying ∈ W}
  choose U hU hEt using fun y : I => hlocal y.val y.property
  let O := ⨆ i : I, U i
  have hWO : W ≤ O := by
    intro x hx
    by_contra hno
    obtain ⟨p, hp, hpc⟩ := nonempty_inter_closedPoints
      (show ((W : Set Y.left) ∩ (O : Set Y.left)ᶜ).Nonempty from ⟨x, hx, hno⟩)
      (W.isOpen.isLocallyClosed.inter O.isOpen.isClosed_compl.isLocallyClosed)
    let y : ComplexPoint Y := Over.homMk (pointOfClosedPoint Y.hom p hpc)
      (pointOfClosedPoint_comp Y.hom p hpc)
    have hy : y.underlying = p := pointOfClosedPoint_apply Y.hom p hpc _
    have hw : y.underlying ∈ W := hy.symm ▸ hp.1
    have hm : y.underlying ∈ O := Opens.mem_iSup.mpr ⟨⟨y, hw⟩, hU ⟨y, hw⟩⟩
    exact hp.2 (hy ▸ hm)
  letI : Etale (f ∣_ O) := s2e_c1_etale_base_iSup f U hEt
  exact s2e_c1_etale_restriction_of_le f O W hWO

end HodgeLean.Foundations.Program
