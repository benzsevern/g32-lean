import HodgeLean.Foundations.TubularEuler.NormalConormalDifferentialHelpers

/-! # Analytic differentials of actual local-ring germs

Equality of original stalk germs identifies their analytic differentials in a fixed ambient chart.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Topology
namespace HodgeLean.Foundations.TubularEuler
open HodgeLean.Adapters

theorem actual_stalk_differential_exists
    (X : Over (Spec (CommRingCat.of ℂ))) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (z x : ComplexPoint X) (hx : x ∈ (chartAt (Fin d → ℂ) z).source)
    (h : X.left.presheaf.stalk x.underlying) :
    ∃ D : (Fin d → ℂ) →L[ℂ] ℂ, ∀ (W : X.left.Opens) (hW : x.underlying ∈ W)
      (s : Γ(X.left, W)), X.left.presheaf.germ W x.underlying hW s = h →
      fderiv ℂ (fun a : Fin d → ℂ => Point.evaluate W s ((chartAt (Fin d → ℂ) z).symm a))
        ((chartAt (Fin d → ℂ) z) x) = D := by
  obtain ⟨W₀, hW₀, s₀, hs₀⟩ := X.left.presheaf.exists_germ_eq h
  refine ⟨fderiv ℂ (fun a : Fin d → ℂ => Point.evaluate W₀ s₀
    ((chartAt (Fin d → ℂ) z).symm a)) ((chartAt (Fin d → ℂ) z) x), ?_⟩
  intro W hW s hs
  have heq := a3b4g_evaluate_eventuallyEq_of_germ_eq X z x hx s s₀ hW hW₀ (hs.trans hs₀.symm)
  exact heq.fderiv_eq

def actualStalkDifferential
    (X : Over (Spec (CommRingCat.of ℂ))) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (z x : ComplexPoint X) (hx : x ∈ (chartAt (Fin d → ℂ) z).source)
    (h : X.left.presheaf.stalk x.underlying) : (Fin d → ℂ) →L[ℂ] ℂ :=
  Classical.choose (actual_stalk_differential_exists X d z x hx h)

theorem actualStalkDifferential_eq_section
    (X : Over (Spec (CommRingCat.of ℂ))) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (z x : ComplexPoint X) (hx : x ∈ (chartAt (Fin d → ℂ) z).source)
    (W : X.left.Opens) (hW : x.underlying ∈ W) (s : Γ(X.left, W)) :
    actualStalkDifferential X d z x hx (X.left.presheaf.germ W x.underlying hW s) =
      fderiv ℂ (fun a : Fin d → ℂ => Point.evaluate W s ((chartAt (Fin d → ℂ) z).symm a))
        ((chartAt (Fin d → ℂ) z) x) := by
  exact (Classical.choose_spec (actual_stalk_differential_exists X d z x hx
    (X.left.presheaf.germ W x.underlying hW s)) W hW s rfl).symm

theorem actualStalkDifferential_hasFDerivAt_section
    (X : Over (Spec (CommRingCat.of ℂ))) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (z x : ComplexPoint X) (hx : x ∈ (chartAt (Fin d → ℂ) z).source)
    (W : X.left.Opens) (hW : x.underlying ∈ W) (s : Γ(X.left, W)) :
    HasFDerivAt (fun a : Fin d → ℂ => Point.evaluate W s ((chartAt (Fin d → ℂ) z).symm a))
      (actualStalkDifferential X d z x hx (X.left.presheaf.germ W x.underlying hW s))
      ((chartAt (Fin d → ℂ) z) x) := by
  rw [actualStalkDifferential_eq_section]
  have ha := ComplexPoint.analyticAt_localChart_symm_evaluate X d z
    ((chartAt (Fin d → ℂ) z).map_source hx) W s (by
      change ((chartAt (Fin d → ℂ) z).symm ((chartAt (Fin d → ℂ) z x))).underlying ∈ W
      rw [(chartAt (Fin d → ℂ) z).left_inv hx]
      exact hW)
  exact ha.hasStrictFDerivAt.hasFDerivAt

theorem actualStalkDifferential_square_zero
    (X : Over (Spec (CommRingCat.of ℂ))) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (z x : ComplexPoint X) (hx : x ∈ (chartAt (Fin d → ℂ) z).source)
    (h : X.left.presheaf.stalk x.underlying)
    (hh : h ∈ IsLocalRing.maximalIdeal (X.left.presheaf.stalk x.underlying) ^ 2) :
    actualStalkDifferential X d z x hx h = 0 := by
  obtain ⟨W, hW, s, hs⟩ := X.left.presheaf.exists_germ_eq h
  have hd := a3b4g_hasFDerivAt_zero_of_mem_sq X z x hx h hh W hW s hs
  rw [← hs, actualStalkDifferential_eq_section]
  exact hd.fderiv

#print axioms actualStalkDifferential_square_zero

#print axioms actualStalkDifferential_hasFDerivAt_section

#print axioms actualStalkDifferential_eq_section

#print axioms actual_stalk_differential_exists

end HodgeLean.Foundations.TubularEuler
