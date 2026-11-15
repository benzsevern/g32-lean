import HodgeLean.Foundations.Curves.AbelTheorem.NormalizedForms

noncomputable section
open HodgeLean.Foundations.Program
open Module Manifold
open scoped ContDiff
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]

theorem exists_normalized_period_frame (h : finrank ℂ E = 1) (p : C) (D : C →₀ ℤ) :
    Nonempty (PeriodFrame (E := E) D) := by
  classical
  obtain ⟨g, b, Q, hQ, hab, haa, hbb⟩ := curve_integral_symplectic_basis (E := E) (C := C) h
  obtain ⟨forms, hnorm⟩ := exists_normalized_holomorphic_basis h b Q hQ haa
  choose a haav hae using fun i : Fin g =>
    lattice_element_loop_avoiding h p D.support (b (.inl i))
  choose c hcav hce using fun i : Fin g =>
    lattice_element_loop_avoiding h p D.support (b (.inr i))
  exact ⟨{
    genus := g
    a := a
    b := c
    latticeBasis := b
    forms := forms
    a_basis := fun i => (hae i).symm
    b_basis := fun i => (hce i).symm
    a_avoids := haav
    b_avoids := hcav
    intersection := Q
    intersection_spec := hQ
    aa := haa
    bb := hbb
    ab := hab
    normalized := fun i j => by
      change (b3_latticePeriod E C (a i)).val (forms j) = _
      rw [hae i]
      exact hnorm i j }⟩

end HodgeLean.Foundations.Curves.AbelTheorem
