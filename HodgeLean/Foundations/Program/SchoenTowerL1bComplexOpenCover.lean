import HodgeLean.Foundations.Program.SchoenTowerGeometryDefs
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Neighborhoods of every complex point cover a scheme locally of finite type over the complex field. -/
theorem s2v_l1b_complex_open_cover
    (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    {A : Type*} (U : A → X.left.Opens)
    (hU : ∀ x : ComplexPoint X, ∃ a, x.underlying ∈ U a) :
    ⨆ a, U a = ⊤ := by
  letI : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  apply top_unique
  intro x hx
  by_contra hxU
  have hnon : ((⨆ a, U a : X.left.Opens) : Set X.left)ᶜ.Nonempty := ⟨x, hxU⟩
  obtain ⟨y, hy, hyclosed⟩ := nonempty_inter_closedPoints hnon
    (⨆ a, U a : X.left.Opens).isOpen.isClosed_compl.isLocallyClosed
  let p : ComplexPoint X := Over.homMk (pointOfClosedPoint X.hom y hyclosed) (pointOfClosedPoint_comp X.hom y hyclosed)
  obtain ⟨a, ha⟩ := hU p
  have hp : p.underlying = y := pointOfClosedPoint_apply X.hom y hyclosed _
  rw [hp] at ha
  exact hy (TopologicalSpace.Opens.mem_iSup.mpr ⟨a, ha⟩)

end HodgeLean.Foundations.Program
