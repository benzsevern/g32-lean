import HodgeLean.Adapters.NormalConeB4aGysinChartFamily
import Mathlib.Analysis.Calculus.FDeriv.Add

noncomputable section
namespace HodgeLean.Adapters
open scoped Topology

/-- A continuous graph in a product chart has a flattening chart whose normal
coordinate has identity derivative along the original vertical disks. -/
theorem a3b4a_gysin_graph_flattening_chart
    {Y : Type*} [TopologicalSpace Y] {n c : ℕ}
    (Φ : OpenPartialHomeomorph Y ((Fin n → ℂ) × (Fin c → ℂ)))
    (ψ : C((Fin n → ℂ), (Fin c → ℂ))) (S : Set Y)
    (hS : ∀ y ∈ Φ.source, y ∈ S ↔ (Φ y).2 = ψ (Φ y).1) :
    ∃ Ψ : OpenPartialHomeomorph Y ((Fin n → ℂ) × (Fin c → ℂ)),
      Ψ.source = Φ.source ∧
      (∀ y, Ψ y = ((Φ y).1, (Φ y).2 - ψ (Φ y).1)) ∧
      (∀ y ∈ Ψ.source, y ∈ S ↔ (Ψ y).2 = 0) ∧
      ∀ a v, (a, v) ∈ Φ.target →
        HasFDerivAt (fun v' => (Ψ (Φ.symm (a, v' + v))).2)
          (ContinuousLinearMap.id ℂ (Fin c → ℂ)) 0 := by
  let H : ((Fin n → ℂ) × (Fin c → ℂ)) ≃ₜ
      ((Fin n → ℂ) × (Fin c → ℂ)) :=
    { toFun := fun z => (z.1, z.2 - ψ z.1)
      invFun := fun z => (z.1, z.2 + ψ z.1)
      left_inv := by intro z; ext <;> simp
      right_inv := by intro z; ext <;> simp
      continuous_toFun := continuous_fst.prodMk
        (continuous_snd.sub (ψ.continuous.comp continuous_fst))
      continuous_invFun := continuous_fst.prodMk
        (continuous_snd.add (ψ.continuous.comp continuous_fst)) }
  let Ψ := Φ.trans H.toOpenPartialHomeomorph
  have hsource : Ψ.source = Φ.source := by
    simp [Ψ, OpenPartialHomeomorph.trans_source]
  have hcoord (y : Y) : Ψ y = ((Φ y).1, (Φ y).2 - ψ (Φ y).1) := rfl
  refine ⟨Ψ, hsource, hcoord, ?_, ?_⟩
  · intro y hy
    rw [hsource] at hy
    simpa only [hcoord, sub_eq_zero] using hS y hy
  · intro a v hav
    have hmem : ∀ᶠ u : Fin c → ℂ in 𝓝 0, (a, u + v) ∈ Φ.target := by
      exact (continuous_const.prodMk (continuous_id.add continuous_const)).continuousAt
        |>.preimage_mem_nhds (by simpa using Φ.open_target.mem_nhds hav)
    have heq : (fun u : Fin c → ℂ => (Ψ (Φ.symm (a, u + v))).2) =ᶠ[𝓝 0]
        (fun u => u + v - ψ a) := by
      filter_upwards [hmem] with u hu
      rw [hcoord, Φ.right_inv hu]
    exact (((hasFDerivAt_id (𝕜 := ℂ) (0 : Fin c → ℂ)).add_const v).sub_const
      (ψ a)).congr_of_eventuallyEq heq

end HodgeLean.Adapters
