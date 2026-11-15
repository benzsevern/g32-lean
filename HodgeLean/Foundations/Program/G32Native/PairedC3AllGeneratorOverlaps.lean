import HodgeLean.Foundations.Program.G32Native.PairedC3SameGeneratorOverlap
import HodgeLean.Foundations.Program.G32Native.PairedC3UniversalGeneratorOverlap

/-! # All four index choices on normalized residual overlaps -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.RamifiedNormalization.StageFour
namespace HodgeLean.Foundations.Program.G32Native

/-- Independently chosen equations give the same normalized projective
morphism for every pair of chart indices. The selected Rees equation is
retained as an equation in the ambient overlap ring. -/
theorem pairedC3_projective_generator_overlap
    {A B C : Type} [CommRing A] [CommRing B] [CommRing C] [Algebra ℂ C]
    [IsSeparated projectiveLine.hom] [LocallyOfFiniteType projectiveLine.hom]
    (I : Ideal A) (f : A →+* B) (g : B →+* C)
    (hI : I ≤ RingHom.ker (g.comp f))
    (u v u' v' α α' : A) (t t' : B) (k k' : Fin 2)
    (hu : IsRegular u) (hv : IsRegular v)
    (huf : IsRegular (f u)) (hvf : IsRegular (f v))
    (hqu : IsRegular (Ideal.Quotient.mk I u))
    (hu' : Ideal.span {u} = Ideal.span {u'})
    (hv' : Ideal.span {v} = Ideal.span {v'})
    (ht : if k = 0 then f u = t * f v else f v = t * f u)
    (ht' : if k' = 0 then f u' = t' * f v' else f v' = t' * f u')
    (hα : v - α * u ∈ I) (hα' : v' - α' * u' ∈ I)
    (c c' : Cˣ) (hc : (c : C) = g (f α)) (hc' : (c' : C) = g (f α')) :
    projectiveLineChart k' ((if k' = 0 then (c' : C) else ↑c'⁻¹) * g t') =
      projectiveLineChart k ((if k = 0 then (c : C) else ↑c⁻¹) * g t) := by
  fin_cases k <;> fin_cases k' <;> simp only [ite_true, Fin.zero_eta] at ht ht' ⊢
  · rw [pairedC3_residual_zero_parameter_of_equal_branch_ideals I f g hI
      u v u' v' α α' t t' hu hv hvf hqu hu' hv' ht ht' hα hα' c c' hc hc']
  · exact pairedC3_projective_opposite_generator_overlap_universal I f g hI
      u v u' v' α α' t t' hu hv huf hqu hu' hv' ht ht' hα hα' c c' hc hc'
  · obtain ⟨a, ha⟩ := pairedC3_principal_generator_unit u u' hu hu'
    obtain ⟨b, hb⟩ := pairedC3_principal_generator_unit v v' hv hv'
    have hru' : IsRegular u' := ha ▸ a.isRegular.mul hu
    have hrv' : IsRegular v' := hb ▸ b.isRegular.mul hv
    have hrf' : IsRegular (f u') := by
      rw [ha, map_mul]
      exact (Units.map f.toMonoidHom a).isRegular.mul huf
    have hrq' : IsRegular (Ideal.Quotient.mk I u') := by
      rw [ha, map_mul]
      exact (Units.map (Ideal.Quotient.mk I).toMonoidHom a).isRegular.mul hqu
    exact (pairedC3_projective_opposite_generator_overlap_universal I f g hI
      u' v' u v α' α t' t hru' hrv' hrf' hrq' hu'.symm hv'.symm
      ht' ht hα' hα c' c hc' hc).symm
  · change projectiveLineChart 1 ((↑c'⁻¹ : C) * g t') =
      projectiveLineChart 1 ((↑c⁻¹ : C) * g t)
    rw [pairedC3_residual_parameter_of_equal_branch_ideals I f g hI
      u v u' v' α α' t t' hu hv huf hqu hu' hv' ht ht' hα hα' c c' hc hc']

#print axioms pairedC3_projective_generator_overlap
end HodgeLean.Foundations.Program.G32Native
