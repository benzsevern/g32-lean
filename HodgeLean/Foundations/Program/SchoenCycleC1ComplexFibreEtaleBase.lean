import HodgeLean.Foundations.Program.SchoenCycleC1EtaleSourceUnion
import HodgeLean.Foundations.Program.SchoenCycleC1FiniteFibreComplexPoints
import HodgeLean.Foundations.Program.SchoenCycleC1EtaleNeighbourhoodHelpers

/-! # Actual base neighbourhoods from etaleness along a complex fibre -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- Etale source neighbourhoods of every complex point in a finite fibre
supply a base open whose entire inverse image is etale. -/
theorem s2e_c1_etale_base_of_complex_fibre_neighbourhoods
    (X Y : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [IsFinite f.left] (y : ComplexPoint Y)
    (hlocal : ∀ z : ComplexPoint X, Point.map f z = y →
      ∃ V : X.left.Opens, z.underlying ∈ V ∧ Etale (V.ι ≫ f.left)) :
    ∃ U : Y.left.Opens, y.underlying ∈ U ∧ Etale (f.left ∣_ U) := by
  classical
  let F := {x : X.left // f.left x = y.underlying}
  have hloc (x : F) : ∃ V : X.left.Opens, x.val ∈ V ∧ Etale (V.ι ≫ f.left) := by
    obtain ⟨z, hz, hfz⟩ := s2e_c1_finite_fibre_complex_representative X Y f y x.val x.property
    obtain ⟨V, hv, het⟩ := hlocal z hfz
    exact ⟨V, hz ▸ hv, het⟩
  choose V hV hEt using hloc
  let O := ⨆ x : F, V x
  letI : Etale (O.ι ≫ f.left) := s2e_c1_etale_source_iSup f.left V hEt
  have hO : ∀ x, f.left x ∈ Set.range y.left → x ∈ O := by
    intro x hx
    obtain ⟨s, hs⟩ := hx
    have hf : f.left x = y.underlying := hs.symm.trans
      (congrArg y.left (Subsingleton.elim (α := Spec ↧ℂ) s (IsLocalRing.closedPoint ℂ)))
    exact Opens.mem_iSup.mpr ⟨⟨x, hf⟩, hV ⟨x, hf⟩⟩
  obtain ⟨U, hU, het⟩ := s2e_c1_etale_neighbourhood_of_source_open f.left y.left O hO
  exact ⟨U, hU ⟨IsLocalRing.closedPoint ℂ, rfl⟩, het⟩

end HodgeLean.Foundations.Program
