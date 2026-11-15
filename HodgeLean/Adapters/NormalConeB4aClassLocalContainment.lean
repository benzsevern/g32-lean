import HodgeLean.Adapters.NormalConeB4aClassSliceEquations

/-! # Local component containment on a normal chart

Route: the tangential inverse chart transports a local containment to an
open piece of the component equations. The identity principle propagates it
through a connected tangential domain.
-/
noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry Set Filter Topology TopologicalSpace
open HodgeLean.Foundations.Analytic

/-- Local containment of a flattened support in a closed analytic subset is
equivalent to containment of its connected tangential chart slice. -/
theorem a3b4a_classHolomorphicChart_localContainment
    (X : Over (Spec (CommRingCat.of ℂ))) [Smooth X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom] {r c : ℕ}
    (e : OpenPartialHomeomorph (ComplexPoint X) ((Fin r → ℂ) × (Fin c → ℂ)))
    (he : a3b4_IsHolChart X.hom e) (S A : Set (ComplexPoint X))
    (hS : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0)
    (hA : an_IsClosedAnalytic (f4_analytification X) A)
    (V : Set (Fin r → ℂ)) (hV : IsOpen V) (hconn : IsPreconnected V)
    (hVT : ∀ t ∈ V, (t, (0 : Fin c → ℂ)) ∈ e.target)
    (y : ComplexPoint X) (hy : y ∈ e.source) (hyS : y ∈ S) (hyV : (e y).1 ∈ V) :
    (∃ U : Set (ComplexPoint X), IsOpen U ∧ y ∈ U ∧ U ∩ S ⊆ A) ↔
      ∀ t ∈ V, e.symm (t, (0 : Fin c → ℂ)) ∈ A := by
  let j : (Fin r → ℂ) → ((Fin r → ℂ) × (Fin c → ℂ)) := fun t => (t, 0)
  let f := fun t => e.symm (j t)
  let T := {t : Fin r → ℂ | f t ∈ A}
  have hcont : ContinuousOn f V :=
    e.symm.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn hVT
  have hy0 := (hS y hy).mp hyS
  have hjy : j (e y).1 = e y := Prod.ext rfl hy0.symm
  have hfy : f (e y).1 = y := by
    change e.symm (j (e y).1) = y
    rw [hjy, e.left_inv hy]
  constructor
  · rintro ⟨U, hU, hyU, hUA⟩
    obtain ⟨hclosed, heq⟩ := a3b4a_classHolomorphicChart_slice_equations X e he A hA
    have hT : V ⊆ T := by
      apply a3b4a_classAnalytic_subset_of_interior r V T hV hconn
        (fun t ht => hclosed ⟨ht.1, hVT t ht.2⟩)
        (fun t ht => heq t ⟨hVT t ht.1, ht.2⟩)
      refine ⟨(e y).1, hyV, ?_⟩
      have hO : IsOpen (V ∩ f ⁻¹' U) := hcont.isOpen_inter_preimage hV hU
      apply (hO.subset_interior_iff.mpr ?_) ⟨hyV, by change f (e y).1 ∈ U; rwa [hfy]⟩
      intro t ht
      apply hUA
      refine ⟨ht.2, (hS (f t) (e.map_target (hVT t ht.1))).mpr ?_⟩
      change (e (e.symm (j t))).2 = 0
      rw [e.right_inv (hVT t ht.1)]
    exact hT
  · intro h
    let Q := e.source ∩ e ⁻¹' (V ×ˢ (Set.univ : Set (Fin c → ℂ)))
    have hQ : IsOpen Q :=
      e.continuousOn.isOpen_inter_preimage e.open_source (hV.prod isOpen_univ)
    refine ⟨Q, hQ, ⟨hy, hyV, Set.mem_univ _⟩, ?_⟩
    intro z hz
    have hz0 := (hS z hz.1.1).mp hz.2
    have hjz : j (e z).1 = e z := Prod.ext rfl hz0.symm
    have hm := h (e z).1 hz.1.2.1
    change e.symm (j (e z).1) ∈ A at hm
    rwa [hjz, e.left_inv hz.1.1] at hm

end HodgeLean.Adapters
