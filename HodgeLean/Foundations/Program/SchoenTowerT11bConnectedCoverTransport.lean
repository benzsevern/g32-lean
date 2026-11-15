import HodgeLean.Foundations.Program.SchoenTowerT11bFormulaSubregionCharts
import HodgeLean.Foundations.Program.SchoenTowerT11bLineConnectedCover

/-! Transporting finite connected fiber covers through actual product charts.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Actual product coordinates lift a finite preconnected fiber cover over a preconnected base.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, connected cylindrical cover lifting step. -/
theorem s2v_t11b_product_chart_preconnected_cover {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (S : Set X) (B : Set Y) (K : Set Z) (hK : IsPreconnected K)
    (e : (B × K) ≃ₜ S) {m : ℕ} (U : Fin m → Set Y)
    (hU : ∀ i, IsPreconnected (U i) ∧ U i ⊆ B)
    (hcover : ∀ y ∈ B, ∃ i, y ∈ U i) :
    ∃ V : Fin m → Set X, (∀ i, IsPreconnected (V i) ∧ V i ⊆ S) ∧
      ∀ x ∈ S, ∃ i, x ∈ V i := by
  let F : (i : Fin m) → (U i × K) → X := fun i z =>
    (e (⟨z.1.val, (hU i).2 z.1.property⟩, z.2)).val
  have hF : ∀ i, Continuous (F i) := by
    intro i
    exact continuous_subtype_val.comp (e.continuous.comp
      (((continuous_subtype_val.comp continuous_fst).subtype_mk _).prodMk continuous_snd))
  refine ⟨fun i => Set.range (F i), ?_, ?_⟩
  · intro i
    haveI : PreconnectedSpace (U i) := isPreconnected_iff_preconnectedSpace.mp (hU i).1
    haveI : PreconnectedSpace K := isPreconnected_iff_preconnectedSpace.mp hK
    refine ⟨isPreconnected_range (hF i), ?_⟩
    rintro x ⟨z, rfl⟩
    exact (e (⟨z.1.val, (hU i).2 z.1.property⟩, z.2)).property
  · intro x hx
    let z := e.symm ⟨x, hx⟩
    obtain ⟨i, hi⟩ := hcover z.1.val z.1.property
    refine ⟨i, ⟨(⟨z.1.val, hi⟩, z.2), ?_⟩⟩
    change (e z).val = x
    exact congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)

end HodgeLean.Foundations.Program
