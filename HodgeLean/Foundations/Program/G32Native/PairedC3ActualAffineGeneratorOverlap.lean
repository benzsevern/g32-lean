import HodgeLean.Foundations.Program.G32Native.PairedC3AllGeneratorOverlaps
import HodgeLean.Foundations.Program.G32Native.PairedC3QuotientRulingCharts

/-! # Generator comparison on an actual residual quotient spectrum -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.RamifiedNormalization.StageFour
namespace HodgeLean.Foundations.Program.G32Native

/-- The ring comparison applies to the original residual quotient spectrum
and its original complex structure map. Its slice ideal may be strictly
smaller than the residual base ideal. -/
theorem pairedC3_actual_affine_generator_overlap
    {X : Scheme} (Y : Over (Spec ↧ℂ)) (p : Y.left ⟶ X) (D : X.IdealSheafData)
    (U : X.affineOpens) (W : Y.left.affineOpens) (hW : W.1 ≤ p ⁻¹ᵁ U.1)
    (I : Ideal Γ(X, U)) (hID : I ≤ D.ideal U)
    (u v u' v' α α' : Γ(X, U)) (t t' : Γ(Y.left, W)) (k k' : Fin 2)
    (hu : IsRegular u) (hv : IsRegular v)
    (huf : IsRegular ((p.appLE U.1 W.1 hW).hom u))
    (hvf : IsRegular ((p.appLE U.1 W.1 hW).hom v))
    (hqu : IsRegular (Ideal.Quotient.mk I u))
    (hu' : Ideal.span {u} = Ideal.span {u'})
    (hv' : Ideal.span {v} = Ideal.span {v'})
    (ht : if k = 0 then (p.appLE U.1 W.1 hW).hom u = t * (p.appLE U.1 W.1 hW).hom v
      else (p.appLE U.1 W.1 hW).hom v = t * (p.appLE U.1 W.1 hW).hom u)
    (ht' : if k' = 0 then (p.appLE U.1 W.1 hW).hom u' = t' * (p.appLE U.1 W.1 hW).hom v'
      else (p.appLE U.1 W.1 hW).hom v' = t' * (p.appLE U.1 W.1 hW).hom u')
    (hα : v - α * u ∈ I) (hα' : v' - α' * u' ∈ I)
    (c c' : (Γ(X, U) ⧸ D.ideal U)ˣ)
    (hc : (c : Γ(X, U) ⧸ D.ideal U) = Ideal.Quotient.mk (D.ideal U) α)
    (hc' : (c' : Γ(X, U) ⧸ D.ideal U) = Ideal.Quotient.mk (D.ideal U) α') :
    let F := pairedC3AffineResidualCoefficient p D U W hW
    let β := Units.map F.toMonoidHom c
    let β' := Units.map F.toMonoidHom c'
    let q := Ideal.Quotient.mk ((D.comap p).ideal W)
    (pairedC3ResidualProjectiveMap Y (D.comap p) W k'
      ((if k' = 0 then ↑β' else ↑β'⁻¹) * q t')).left =
    (pairedC3ResidualProjectiveMap Y (D.comap p) W k
      ((if k = 0 then ↑β else ↑β⁻¹) * q t)).left := by
  let F := pairedC3AffineResidualCoefficient p D U W hW
  let β := Units.map F.toMonoidHom c
  let β' := Units.map F.toMonoidHom c'
  let q := Ideal.Quotient.mk ((D.comap p).ideal W)
  let f := (p.appLE U.1 W.1 hW).hom
  letI := pairedC3SpecAlgebra ((D.comap p).subschemeCover.f W ≫
    (D.comap p).subschemeι ≫ Y.hom)
  have hI : I ≤ RingHom.ker (q.comp f) := by
    intro a ha
    change F (Ideal.Quotient.mk (D.ideal U) a) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hID ha), map_zero]
  have hβ : (β : Γ(Y.left, W) ⧸ (D.comap p).ideal W) = q (f α) := by
    change F (c : Γ(X, U) ⧸ D.ideal U) = _
    rw [hc]
    rfl
  have hβ' : (β' : Γ(Y.left, W) ⧸ (D.comap p).ideal W) = q (f α') := by
    change F (c' : Γ(X, U) ⧸ D.ideal U) = _
    rw [hc']
    rfl
  change (projectiveLineChart k' ((if k' = 0 then ↑β' else ↑β'⁻¹) * q t')).left =
    (projectiveLineChart k ((if k = 0 then ↑β else ↑β⁻¹) * q t)).left
  exact congrArg Over.Hom.left (pairedC3_projective_generator_overlap I f q hI
    u v u' v' α α' t t' k k' hu hv huf hvf hqu hu' hv' ht ht' hα hα' β β' hβ hβ')

#print axioms pairedC3_actual_affine_generator_overlap
end HodgeLean.Foundations.Program.G32Native
