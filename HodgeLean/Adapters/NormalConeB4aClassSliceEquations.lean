import HodgeLean.Adapters.NormalConeB4aClassChartFunction
import HodgeLean.Adapters.NormalConeB4aClassAnalyticIdentity

/-! # Component equations on tangential chart slices

Route: pull finite holomorphic defining equations through the inverse normal
chart and then along its zero-normal slice.
-/
noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry Set Filter Topology TopologicalSpace
open HodgeLean.Foundations.Analytic

/-- A closed analytic subset has local analytic equations on the tangential
slice of every frozen holomorphic normal chart. -/
theorem a3b4a_classHolomorphicChart_slice_equations
    (X : Over (Spec (CommRingCat.of ℂ))) [Smooth X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom] {r c : ℕ}
    (e : OpenPartialHomeomorph (ComplexPoint X) ((Fin r → ℂ) × (Fin c → ℂ)))
    (he : a3b4_IsHolChart X.hom e) (A : Set (ComplexPoint X))
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
      have hgi := a3b4a_classHolomorphicChart_function_analytic X e he W hW (g' i)
        (hg' i) (j s) hs.1 hs.2
      exact hgi.comp (by fun_prop : AnalyticAt ℂ j s)
    · intro s hs
      change e.symm (j s) ∈ A ↔ ∀ i, g' i (e.symm (j s)) = 0
      simp only [hgeval _ _ hs.2]
      exact hEq ⟨e.symm (j s), hs.2⟩

end HodgeLean.Adapters
