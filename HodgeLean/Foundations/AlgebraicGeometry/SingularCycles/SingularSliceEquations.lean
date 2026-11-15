import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.HolomorphicChartImage
import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.ChartCoordinates

/-! # Analytic equations on slices in singular ambient spaces

HC no distance; AV milestone no distance.
-/

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open Set Filter Topology HodgeLean.Foundations.Analytic HodgeLean.Adapters
namespace AlgebraicGeometry.SingularCycles

/-- Closed analytic subsets have local analytic equations on tangential slices of holomorphic charts.
Source: Grauert–Remmert, Coherent Analytic Sheaves, Ch. 2; the finite mapping theorem. -/
theorem singular_chart_slice_equations
    (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    {r c : ℕ} (e : OpenPartialHomeomorph (ComplexPoint X) ((Fin r → ℂ) × (Fin c → ℂ)))
    (he : a3b4_IsHolChart X.hom e) (A : Set (ComplexPoint X))
    (hA : an_IsClosedAnalytic (f4_analytification X) A) :
    let D := {t : Fin r → ℂ | (t, (0 : Fin c → ℂ)) ∈ e.target}
    let T := {t : Fin r → ℂ | e.symm (t, (0 : Fin c → ℂ)) ∈ A}
    (closure T ∩ D ⊆ T) ∧ ∀ t ∈ D ∩ T, anrem_LocEq T t := by
  let j : (Fin r → ℂ) → ((Fin r → ℂ) × (Fin c → ℂ)) := fun t => (t, 0)
  let D := j ⁻¹' e.target
  let T := {t | e.symm (j t) ∈ A}
  have hD : IsOpen D := e.open_target.preimage (continuous_id.prodMk continuous_const)
  have hcont : ContinuousOn (fun t => e.symm (j t)) D :=
    e.symm.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn (fun _ h => h)
  constructor
  · intro t ht
    by_contra hn
    have hbad : IsOpen (D ∩ (fun t => e.symm (j t)) ⁻¹' Aᶜ) :=
      hcont.isOpen_inter_preimage hD hA.1.isOpen_compl
    obtain ⟨s, hs, hsT⟩ := mem_closure_iff.mp ht.1 _ hbad ⟨ht.2, hn⟩
    exact hs.2 hsT
  · intro t ht
    let L := chartProductEquiv r c
    let E := e.transHomeomorph L.toHomeomorph
    have hc : ∀ i, (f4_analytification X).IsHolFun (fun x : E.source => E x i) := by
      intro i
      refine Fin.addCases (fun k => ?_) (fun k => ?_) i
      · change (f4_analytification X).IsHolFun
          (fun x : e.source => Fin.append (e x).1 (e x).2 (Fin.castAdd c k))
        simp only [Fin.append_left]
        exact he.1 k
      · change (f4_analytification X).IsHolFun
          (fun x : e.source => Fin.append (e x).1 (e x).2 (Fin.natAdd r k))
        simp only [Fin.append_right]
        exact he.2 k
    let φ : (Fin r → ℂ) → (Fin (r + c) → ℂ) := fun s => L (j s)
    have hφ : ∀ s, AnalyticAt ℂ φ s := fun s =>
      (L.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℂ (Fin r → ℂ) (Fin c → ℂ))).analyticAt s
    have hval : ∀ s ∈ D, E (e.symm (j s)) = φ s := by
      intro s hs
      change L (e (e.symm (j s))) = L (j s)
      rw [e.right_inv hs]
    have hloc := holomorphic_chart_image_ambient (f4_analytification X) E hc A hA
      (e.symm (j t)) (e.map_target ht.1) ht.2
    rw [hval t ht.1] at hloc
    obtain ⟨B, hB, htB, m, g, hg, hEq⟩ := hloc
    have hmem : ∀ s ∈ D, (s ∈ T ↔ φ s ∈ E '' (A ∩ E.source)) := by
      intro s hs
      constructor
      · intro hsA
        exact ⟨e.symm (j s), ⟨hsA, e.map_target hs⟩, hval s hs⟩
      · rintro ⟨x, hx, hEx⟩
        have hex : e x = j s := L.injective hEx
        have hxe : x = e.symm (j s) := by rw [← hex, e.left_inv hx.2]
        change e.symm (j s) ∈ A
        rw [← hxe]
        exact hx.1
    refine ⟨D ∩ φ ⁻¹' B, hD.inter (hB.preimage
      (continuous_iff_continuousAt.mpr fun s => (hφ s).continuousAt)), ⟨ht.1, htB⟩,
      m, fun i s => g i (φ s), ?_, ?_⟩
    · intro i s hs
      exact (hg i _ hs.2).comp (hφ s)
    · intro s hs
      exact (hmem s hs.1).trans (hEq _ hs.2)

end AlgebraicGeometry.SingularCycles
