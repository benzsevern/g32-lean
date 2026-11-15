import Mathlib.Analysis.Calculus.FDeriv.Mul
import HodgeLean.Foundations.TubularEuler.ConormalEquationRelationHelpers
import HodgeLean.Foundations.TubularEuler.NormalEquationSquareErrorHelpers

/-! # Analytic differentials of actual conormal equation relations

Cotangent relations on the original stalk give regular equation errors with zero analytic differential.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Topology
open scoped BigOperators
namespace HodgeLean.Foundations.TubularEuler
open HodgeLean.Adapters

theorem normal_conormal_relation_error_hasFDerivAt_zero
    (X : Over (Spec (CommRingCat.of ℂ))) (d k : ℕ) [SmoothOfRelativeDimension d X.hom]
    (z x : ComplexPoint X) (hx : x ∈ (chartAt (Fin d → ℂ) z).source)
    (W : X.left.Opens) (hW : x.underlying ∈ W)
    (I : Ideal (X.left.presheaf.stalk x.underlying))
    (hIM : I ≤ IsLocalRing.maximalIdeal (X.left.presheaf.stalk x.underlying))
    (f : Fin k → Γ(X.left, W)) (g : Γ(X.left, W)) (c : Fin k → Γ(X.left, W))
    (hf : ∀ i, X.left.presheaf.germ W x.underlying hW (f i) ∈ I)
    (hg : X.left.presheaf.germ W x.underlying hW g ∈ I)
    (hrel : I.toCotangent ⟨X.left.presheaf.germ W x.underlying hW g, hg⟩ =
      ∑ i, (X.left.presheaf.germ W x.underlying hW (c i)) •
        I.toCotangent ⟨X.left.presheaf.germ W x.underlying hW (f i), hf i⟩) :
    HasFDerivAt (fun a : Fin d → ℂ => Point.evaluate W (g - ∑ i, c i * f i)
      ((chartAt (Fin d → ℂ) z).symm a)) (0 : (Fin d → ℂ) →L[ℂ] ℂ)
      ((chartAt (Fin d → ℂ) z) x) := by
  have h := conormal_relation_error_mem_square I
    (IsLocalRing.maximalIdeal (X.left.presheaf.stalk x.underlying)) hIM
    (fun i => ⟨X.left.presheaf.germ W x.underlying hW (f i), hf i⟩)
    ⟨X.left.presheaf.germ W x.underlying hW g, hg⟩
    (fun i => X.left.presheaf.germ W x.underlying hW (c i)) hrel
  have hsq : X.left.presheaf.germ W x.underlying hW (g - ∑ i, c i * f i) ∈
      IsLocalRing.maximalIdeal (X.left.presheaf.stalk x.underlying) ^ 2 := by
    simpa only [map_sub, map_sum, map_mul] using h
  exact a3b4g_hasFDerivAt_zero_of_mem_sq X z x hx _ hsq W hW _ rfl

theorem normal_conormal_relation_fderiv
    (X : Over (Spec (CommRingCat.of ℂ))) (d k : ℕ) [SmoothOfRelativeDimension d X.hom]
    (z x : ComplexPoint X) (hx : x ∈ (chartAt (Fin d → ℂ) z).source)
    (W : X.left.Opens) (hW : x.underlying ∈ W)
    (I : Ideal (X.left.presheaf.stalk x.underlying))
    (hIM : I ≤ IsLocalRing.maximalIdeal (X.left.presheaf.stalk x.underlying))
    (f : Fin k → Γ(X.left, W)) (g : Γ(X.left, W)) (c : Fin k → Γ(X.left, W))
    (hf : ∀ i, X.left.presheaf.germ W x.underlying hW (f i) ∈ I)
    (hg : X.left.presheaf.germ W x.underlying hW g ∈ I)
    (hrel : I.toCotangent ⟨X.left.presheaf.germ W x.underlying hW g, hg⟩ =
      ∑ i, (X.left.presheaf.germ W x.underlying hW (c i)) •
        I.toCotangent ⟨X.left.presheaf.germ W x.underlying hW (f i), hf i⟩) :
    fderiv ℂ (fun a : Fin d → ℂ => Point.evaluate W g ((chartAt (Fin d → ℂ) z).symm a))
        ((chartAt (Fin d → ℂ) z) x) =
      ∑ i, Point.evaluate W (c i) x •
        fderiv ℂ (fun a : Fin d → ℂ => Point.evaluate W (f i) ((chartAt (Fin d → ℂ) z).symm a))
          ((chartAt (Fin d → ℂ) z) x) := by
  let χ := chartAt (Fin d → ℂ) z
  let p := χ x
  let e : Γ(X.left, W) → (Fin d → ℂ) → ℂ := fun t a => Point.evaluate W t (χ.symm a)
  let δ := fun t => fderiv ℂ (e t) p
  have hepoint : ∀ t, e t p = Point.evaluate W t x := by
    intro t
    change Point.evaluate W t (χ.symm (χ x)) = Point.evaluate W t x
    rw [χ.left_inv hx]
  have ha : ∀ t, AnalyticAt ℂ (e t) p := by
    intro t
    exact ComplexPoint.analyticAt_localChart_symm_evaluate X d z (χ.map_source hx) W t (by
      change (χ.symm (χ x)).underlying ∈ W
      rw [χ.left_inv hx]
      exact hW)
  have hδ : ∀ t, HasFDerivAt (e t) (δ t) p :=
    fun t => (ha t).hasStrictFDerivAt.hasFDerivAt
  have hfzero : ∀ i, e (f i) p = 0 := by
    intro i
    rw [hepoint]
    have h := a3b4g_stalkHom_eq_zero_of_mem x _ (hIM (hf i))
    rwa [a3b4g_stalkHom_germ W (f i) x hW] at h
  have hprod : ∀ i, HasFDerivAt (fun a => e (c i) a * e (f i) a)
      (Point.evaluate W (c i) x • δ (f i)) p := by
    intro i
    have h := (hδ (c i)).fun_mul (hδ (f i))
    rw [hfzero i, zero_smul, add_zero, hepoint] at h
    exact h
  have hsum : HasFDerivAt (fun a => ∑ i, e (c i) a * e (f i) a)
      (∑ i, Point.evaluate W (c i) x • δ (f i)) p := by
    apply HasFDerivAt.fun_sum
    intro i _
    exact hprod i
  have herr : e (g - ∑ i, c i * f i) = (fun a => e g a - ∑ i, e (c i) a * e (f i) a) := by
    funext a
    dsimp only [e]
    rw [a3b4g_evaluate_sub, a3b4g_evaluate_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [a3b4g_evaluate_mul]
  have hzero := normal_conormal_relation_error_hasFDerivAt_zero X d k z x hx W hW I hIM f g c hf hg hrel
  change HasFDerivAt (e (g - ∑ i, c i * f i)) (0 : (Fin d → ℂ) →L[ℂ] ℂ) p at hzero
  rw [herr] at hzero
  exact sub_eq_zero.mp (((hδ g).fun_sub hsum).unique hzero)

#print axioms normal_conormal_relation_fderiv

#print axioms normal_conormal_relation_error_hasFDerivAt_zero

end HodgeLean.Foundations.TubularEuler
