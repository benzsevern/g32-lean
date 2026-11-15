import HodgeLean.Foundations.TubularEuler.AnalyticStalkDifferentialHelpers

/-! # Algebra of actual analytic stalk differentials

Common regular representatives retain the original local-ring operations under analytic differentiation.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Topology
namespace HodgeLean.Foundations.TubularEuler
open HodgeLean.Adapters

theorem actual_stalk_common_regular_representatives
    (X : Over (Spec (CommRingCat.of ℂ))) (x : ComplexPoint X)
    (h k : X.left.presheaf.stalk x.underlying) :
    ∃ (W : X.left.Opens) (hW : x.underlying ∈ W) (s t : Γ(X.left, W)),
      X.left.presheaf.germ W x.underlying hW s = h ∧
      X.left.presheaf.germ W x.underlying hW t = k := by
  obtain ⟨U, hU, s, hs⟩ := X.left.presheaf.exists_germ_eq h
  obtain ⟨V, hV, t, ht⟩ := X.left.presheaf.exists_germ_eq k
  let W := U ⊓ V
  have hW : x.underlying ∈ W := ⟨hU, hV⟩
  let s' := X.left.presheaf.map (homOfLE (inf_le_left : W ≤ U)).op s
  let t' := X.left.presheaf.map (homOfLE (inf_le_right : W ≤ V)).op t
  refine ⟨W, hW, s', t', ?_, ?_⟩
  · rw [TopCat.Presheaf.germ_res_apply, hs]
  · rw [TopCat.Presheaf.germ_res_apply, ht]

theorem actualStalkDifferential_add
    (X : Over (Spec (CommRingCat.of ℂ))) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (z x : ComplexPoint X) (hx : x ∈ (chartAt (Fin d → ℂ) z).source)
    (h k : X.left.presheaf.stalk x.underlying) :
    actualStalkDifferential X d z x hx (h + k) =
      actualStalkDifferential X d z x hx h + actualStalkDifferential X d z x hx k := by
  obtain ⟨W, hW, s, t, hs, ht⟩ := actual_stalk_common_regular_representatives X x h k
  have hgs : X.left.presheaf.germ W x.underlying hW (s + t) = h + k := by
    rw [map_add, hs, ht]
  have hσ := actualStalkDifferential_hasFDerivAt_section X d z x hx W hW s
  have hτ := actualStalkDifferential_hasFDerivAt_section X d z x hx W hW t
  have hsum := actualStalkDifferential_hasFDerivAt_section X d z x hx W hW (s + t)
  rw [hs] at hσ
  rw [ht] at hτ
  rw [hgs] at hsum
  have heq : (fun a : Fin d → ℂ => Point.evaluate W (s + t) ((chartAt (Fin d → ℂ) z).symm a)) =
      (fun a => Point.evaluate W s ((chartAt (Fin d → ℂ) z).symm a) +
        Point.evaluate W t ((chartAt (Fin d → ℂ) z).symm a)) := by
    funext a
    exact a3b4g_evaluate_add W s t _
  rw [heq] at hsum
  exact hsum.unique (hσ.fun_add hτ)

theorem actualStalkDifferential_mul
    (X : Over (Spec (CommRingCat.of ℂ))) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (z x : ComplexPoint X) (hx : x ∈ (chartAt (Fin d → ℂ) z).source)
    (h k : X.left.presheaf.stalk x.underlying) :
    actualStalkDifferential X d z x hx (h * k) =
      x.stalkHom.hom h • actualStalkDifferential X d z x hx k +
      x.stalkHom.hom k • actualStalkDifferential X d z x hx h := by
  obtain ⟨W, hW, s, t, hs, ht⟩ := actual_stalk_common_regular_representatives X x h k
  have hgp : X.left.presheaf.germ W x.underlying hW (s * t) = h * k := by
    rw [map_mul, hs, ht]
  have hσ := actualStalkDifferential_hasFDerivAt_section X d z x hx W hW s
  have hτ := actualStalkDifferential_hasFDerivAt_section X d z x hx W hW t
  have hprod := actualStalkDifferential_hasFDerivAt_section X d z x hx W hW (s * t)
  rw [hs] at hσ
  rw [ht] at hτ
  rw [hgp] at hprod
  have heq : (fun a : Fin d → ℂ => Point.evaluate W (s * t) ((chartAt (Fin d → ℂ) z).symm a)) =
      (fun a => Point.evaluate W s ((chartAt (Fin d → ℂ) z).symm a) *
        Point.evaluate W t ((chartAt (Fin d → ℂ) z).symm a)) := by
    funext a
    exact a3b4g_evaluate_mul W s t _
  rw [heq] at hprod
  have h := hprod.unique (hσ.fun_mul hτ)
  rw [(chartAt (Fin d → ℂ) z).left_inv hx,
    ← a3b4g_stalkHom_germ W s x hW, ← a3b4g_stalkHom_germ W t x hW, hs, ht] at h
  exact h

#print axioms actualStalkDifferential_mul

#print axioms actualStalkDifferential_add

#print axioms actual_stalk_common_regular_representatives

end HodgeLean.Foundations.TubularEuler
