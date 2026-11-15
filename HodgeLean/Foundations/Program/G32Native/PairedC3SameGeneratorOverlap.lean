import HodgeLean.Foundations.Program.G32Native.PairedC3OppositeGeneratorOverlap

/-! # Same-index comparisons for independently chosen branch equations -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.RamifiedNormalization.StageFour
namespace HodgeLean.Foundations.Program.G32Native

/-- On chart zero, the raw parameter and the slice coefficient have inverse
changes of scale. Cancellation occurs in the ambient chart and on the slice,
before passing to the residual ring. -/
theorem pairedC3_residual_zero_parameter_of_equal_branch_ideals
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    (I : Ideal A) (f : A →+* B) (g : B →+* C)
    (hI : I ≤ RingHom.ker (g.comp f))
    (u v u' v' α α' : A) (s s' : B)
    (hu : IsRegular u) (hv : IsRegular v)
    (hvf : IsRegular (f v)) (hqu : IsRegular (Ideal.Quotient.mk I u))
    (hu' : Ideal.span {u} = Ideal.span {u'})
    (hv' : Ideal.span {v} = Ideal.span {v'})
    (hs : f u = s * f v) (hs' : f u' = s' * f v')
    (hα : v - α * u ∈ I) (hα' : v' - α' * u' ∈ I)
    (c c' : Cˣ) (hc : (c : C) = g (f α)) (hc' : (c' : C) = g (f α')) :
    (c' : C) * g s' = (c : C) * g s := by
  obtain ⟨a, ha⟩ := pairedC3_principal_generator_unit u u' hu hu'
  obtain ⟨b, hb⟩ := pairedC3_principal_generator_unit v v' hv hv'
  let F := g.comp f
  let q := Ideal.Quotient.lift I F (fun x hx => hI hx)
  have hcoef : F α' = F ((b : A) * ↑a⁻¹ * α) := by
    exact congrArg q (pairedC3_slice_overlap_coefficient I u v α α' a b hqu hα
      (by simpa only [← ha, ← hb] using hα'))
  have hparam : s' = f (a : A) * f (↑b⁻¹ : A) * s := by
    exact pairedC3_rees_overlap_generator_change (f v) (f u) s s'
      (Units.map f.toMonoidHom b) (Units.map f.toMonoidHom a) hvf hs
      (by
        change f (a : A) * f u = s' * (f (b : A) * f v)
        simpa only [map_mul, ha, hb] using hs')
  let aC := Units.map F.toMonoidHom a
  let bC := Units.map F.toMonoidHom b
  have hcunits : c' = bC * aC⁻¹ * c := by
    apply Units.ext
    change (c' : C) = F (b : A) * F (↑a⁻¹ : A) * (c : C)
    rw [hc, hc']
    simpa only [F, RingHom.comp_apply, map_mul] using hcoef
  rw [hcunits, hparam, map_mul, map_mul]
  change ((bC : C) * ↑aC⁻¹ * ↑c) * ((aC : C) * ↑bC⁻¹ * g s) = ↑c * g s
  calc
    _ = ((bC : C) * ↑bC⁻¹) * (↑aC⁻¹ * ↑aC) * (↑c * g s) := by ring
    _ = _ := by rw [Units.mul_inv, Units.inv_mul, one_mul, one_mul]

#print axioms pairedC3_residual_zero_parameter_of_equal_branch_ideals
end HodgeLean.Foundations.Program.G32Native
