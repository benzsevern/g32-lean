import HodgeLean.Foundations.Program.G32Native.PairedC3PrincipalGeneratorChange

/-! # Opposite residual charts with independently chosen branch equations -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.RamifiedNormalization.StageFour
namespace HodgeLean.Foundations.Program.G32Native

/-- The two normalized projective maps agree on opposite charts even when
the branch equations were chosen independently. Equality of their principal
ideals supplies the generator units; ambient cancellation supplies reciprocity. -/
theorem pairedC3_projective_opposite_generator_overlap
    {A B C : Type} [CommRing A] [CommRing B] [CommRing C] [Algebra ℂ C]
    [IsReduced (Spec (CommRingCat.of C))]
    [LocallyOfFiniteType (ComplexPoint.affineSpecStructureMap C)]
    [IsSeparated projectiveLine.hom] [LocallyOfFiniteType projectiveLine.hom]
    (I : Ideal A) (f : A →+* B) (g : B →+* C)
    (hI : I ≤ RingHom.ker (g.comp f))
    (u v u' v' α α' : A) (s t' : B)
    (hu : IsRegular u) (hv : IsRegular v)
    (huf : IsRegular (f u)) (hqu : IsRegular (Ideal.Quotient.mk I u))
    (hu' : Ideal.span {u} = Ideal.span {u'})
    (hv' : Ideal.span {v} = Ideal.span {v'})
    (hs : f u = s * f v) (ht' : f v' = t' * f u')
    (hα : v - α * u ∈ I) (hα' : v' - α' * u' ∈ I)
    (c c' : Cˣ) (hc : (c : C) = g (f α)) (hc' : (c' : C) = g (f α')) :
    projectiveLineChart 1 ((↑c'⁻¹ : C) * g t') =
      projectiveLineChart 0 ((↑c : C) * g s) := by
  obtain ⟨a, ha⟩ := pairedC3_principal_generator_unit u u' hu hu'
  obtain ⟨b, hb⟩ := pairedC3_principal_generator_unit v v' hv hv'
  let aB := Units.map f.toMonoidHom a
  let bB := Units.map f.toMonoidHom b
  let t : B := (aB : B) * ↑bB⁻¹ * t'
  have ht : f v = t * f u := by
    have h := ht'
    rw [ha, hb, map_mul, map_mul] at h
    change (bB : B) * f v = t' * ((aB : B) * f u) at h
    have hh := congrArg (fun z : B => (↑bB⁻¹ : B) * z) h
    rw [← mul_assoc, Units.inv_mul, one_mul] at hh
    calc
      f v = (↑bB⁻¹ : B) * (t' * ((aB : B) * f u)) := hh
      _ = t * f u := by dsimp only [t]; ring
  have heq := pairedC3_residual_parameter_of_equal_branch_ideals I f g hI
    u v u' v' α α' t t' hu hv huf hqu hu' hv' ht ht' hα hα' c c' hc hc'
  rw [heq]
  exact pairedC3_projective_overlap_of_rees_equations g (f u) (f v) s t huf hs ht c

#print axioms pairedC3_projective_opposite_generator_overlap
end HodgeLean.Foundations.Program.G32Native
