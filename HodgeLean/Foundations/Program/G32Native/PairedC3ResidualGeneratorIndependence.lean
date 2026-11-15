import HodgeLean.Foundations.Program.G32Native.PairedC3ReesOverlapRelations

/-! # Independence of normalized residual parameters from branch generators -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.Program.G32Native

/-- The normalization coefficient and the raw Rees parameter change by the
same unit. Their quotient is therefore unchanged after residual restriction.
The hypotheses are equations of branch generators and their slice restrictions;
no transition formula for either parameter is supplied as an input. -/
theorem pairedC3_residual_parameter_generator_independent
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    (I : Ideal A) (f : A →+* B) (g : B →+* C)
    (hI : I ≤ RingHom.ker (g.comp f))
    (u v α α' : A) (a b : Aˣ) (t t' : B)
    (hu : IsRegular (f u)) (hqu : IsRegular (Ideal.Quotient.mk I u))
    (ht : f v = t * f u)
    (ht' : f ((b : A) * v) = t' * f ((a : A) * u))
    (hα : v - α * u ∈ I)
    (hα' : (b : A) * v - α' * ((a : A) * u) ∈ I)
    (c c' : Cˣ) (hc : (c : C) = g (f α)) (hc' : (c' : C) = g (f α')) :
    (↑c'⁻¹ : C) * g t' = (↑c⁻¹ : C) * g t := by
  let F := g.comp f
  let q := Ideal.Quotient.lift I F (fun x hx => hI hx)
  have hcoef : F α' = F ((b : A) * ↑a⁻¹ * α) := by
    exact congrArg q (pairedC3_slice_overlap_coefficient I u v α α' a b hqu hα hα')
  have hparam : t' = f (b : A) * f (↑a⁻¹ : A) * t := by
    have h := pairedC3_rees_overlap_generator_change (f u) (f v) t t'
      (Units.map f.toMonoidHom a) (Units.map f.toMonoidHom b) hu ht
      (by
        change f (b : A) * f v = t' * (f (a : A) * f u)
        simpa only [map_mul] using ht')
    change t' = f (b : A) * f (↑a⁻¹ : A) * t at h
    exact h
  let aC := Units.map F.toMonoidHom a
  let bC := Units.map F.toMonoidHom b
  have hcunits : c' = bC * aC⁻¹ * c := by
    apply Units.ext
    change (c' : C) = F (b : A) * F (↑a⁻¹ : A) * (c : C)
    rw [hc, hc']
    change g (f α') = g (f ((b : A) * ↑a⁻¹ * α)) at hcoef
    simpa only [F, RingHom.comp_apply, map_mul] using hcoef
  rw [hcunits, hparam, map_mul, map_mul]
  exact pairedC3_normalized_generator_change c aC bC (g t)

#print axioms pairedC3_residual_parameter_generator_independent
end HodgeLean.Foundations.Program.G32Native
