import HodgeLean.Foundations.QuotientDuality.ProperCycleSmoothOpenChartFunction
import HodgeLean.Adapters.NormalConeB4aClassAnalyticIdentity

/-! # Actual tangential analytic equations inside a smooth affine open -/

noncomputable section
namespace HodgeLean.Foundations.QuotientDuality
open CategoryTheory AlgebraicGeometry Set Filter Topology TopologicalSpace
open HodgeLean.Adapters HodgeLean.Foundations.Analytic

/-- A closed analytic subset has local analytic equations on the tangential
slice of an original chart contained in a smooth affine open of the ambient scheme.
Source: Gunning and Rossi, Analytic Functions of Several Complex Variables, chapter II, analytic defining equations.
HC no distance; AV milestone no distance. -/
lemma properCycle_chart_slice_equations_on_smooth_affine_open
    (X : Over (Spec (CommRingCat.of ℂ))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom]
    (U : X.left.Opens) (hU : IsAffineOpen U)
    [Smooth (ComplexPoint.openScheme X U).hom] {r c : ℕ}
    (e : OpenPartialHomeomorph (ComplexPoint X) ((Fin r → ℂ) × (Fin c → ℂ)))
    (he : a3b4_IsHolChart X.hom e)
    (hsource : ∀ x ∈ e.source, x.underlying ∈ U) (A : Set (ComplexPoint X))
    (hA : an_IsClosedAnalytic (f4_analytification X) A) :
    let V := {t : Fin r → ℂ | (t, (0 : Fin c → ℂ)) ∈ e.target}
    let T := {t : Fin r → ℂ | e.symm (t, (0 : Fin c → ℂ)) ∈ A}
    (closure T ∩ V ⊆ T) ∧ ∀ t ∈ V ∩ T, anrem_LocEq T t := by
  classical
  let j : (Fin r → ℂ) → ((Fin r → ℂ) × (Fin c → ℂ)) := fun t => (t, 0)
  have hj : Continuous j := continuous_id.prodMk continuous_const
  let V := j ⁻¹' e.target
  let T := {t : Fin r → ℂ | e.symm (j t) ∈ A}
  have hV : IsOpen V := e.open_target.preimage hj
  have hcont : ContinuousOn (fun t => e.symm (j t)) V :=
    e.symm.continuousOn.comp hj.continuousOn (fun _ h => h)
  have hbad : IsOpen (V ∩ (fun t => e.symm (j t)) ⁻¹' Aᶜ) :=
    hcont.isOpen_inter_preimage hV hA.1.isOpen_compl
  constructor
  · intro t ht
    by_contra hn
    obtain ⟨s, hs, hsT⟩ := mem_closure_iff.mp ht.1 _ hbad ⟨ht.2, hn⟩
    exact hs.2 hsT
  · intro t ht
    obtain ⟨W, hW, htW, k, g, hg, hEq⟩ := hA.2 (e.symm (j t)) ht.2
    let g' (i : Fin k) (x : ComplexPoint X) : ℂ := if h : x ∈ W then g i ⟨x, h⟩ else 0
    have hgeval (i : Fin k) (x : ComplexPoint X) (hx : x ∈ W) :
        g' i x = g i ⟨x, hx⟩ := dite_eq_left hx
    have hg' (i : Fin k) : (f4_analytification X).IsHolFun (fun x : W => g' i x) := by
      have hfun : (fun x : W => g' i x) = g i := funext fun x => hgeval i x x.2
      rw [hfun]
      exact hg i
    let N := V ∩ (fun s => e.symm (j s)) ⁻¹' W
    have hN : IsOpen N := hcont.isOpen_inter_preimage hV hW
    refine ⟨N, hN, ⟨ht.1, htW⟩, k, fun i s => g' i (e.symm (j s)), ?_, ?_⟩
    · intro i s hs
      have hgi := properCycle_chart_function_analytic_on_smooth_affine_open X U hU e he W hW (g' i)
        (hg' i) (j s) hs.1 hs.2 (hsource _ (e.map_target hs.1))
      exact hgi.comp (by fun_prop : AnalyticAt ℂ j s)
    · intro s hs
      change e.symm (j s) ∈ A ↔ ∀ i, g' i (e.symm (j s)) = 0
      simp only [hgeval _ _ hs.2]
      exact hEq ⟨e.symm (j s), hs.2⟩

end HodgeLean.Foundations.QuotientDuality
