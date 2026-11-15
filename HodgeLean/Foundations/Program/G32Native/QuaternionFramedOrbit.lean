import HodgeLean.Foundations.Program.G32Native.QuaternionGraphWedge
import HodgeLean.Foundations.Program.G32Native.QuaternionGraphHomogeneous

noncomputable section
set_option maxHeartbeats 200000
namespace HodgeLean.Foundations.Program.QuaternionGraph
variable {K V I : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]

/-- The two top-frame lines retained before applying the exterior orbit. -/
def frameLines {n : ℕ} (b : Module.Basis (Fin n × Fin 2) K V) : Submodule K (⋀[K]^n V) :=
  Submodule.span K {exteriorPower.ιMulti K n (fun i => b (i,0)),
    exteriorPower.ιMulti K n (fun i => b (i,1))}

/-- The span of the exterior images of a subspace under a family of linear operators. -/
def exteriorOrbit {n : ℕ} (T : I → Module.End K V) (L : Submodule K (⋀[K]^n V)) :
    Submodule K (⋀[K]^n V) := ⨆ i, L.map (exteriorPower.map n (T i))

/-- Uniform two-frame action and distinct graph samples determine the exterior orbit rank. -/
theorem framed_orbit_finrank {n : ℕ} (b : Module.Basis (Fin n × Fin 2) K V)
    (T : I → Module.End K V)
    (hT : ∀ d, ∃ a₀ a₁ c₀ c₁ : K, ∀ i,
      T d (b (i,0)) = a₀ • b (i,0) + a₁ • b (i,1) ∧
      T d (b (i,1)) = c₀ • b (i,0) + c₁ • b (i,1))
    (hSamples : ∀ t : Fin (n+1), ∃ d, ∀ i,
      T d (b (i,0)) = b (i,0) + (t.val : K) • b (i,1)) :
    Module.finrank K (exteriorOrbit T (frameLines b)) = n+1 := by
  classical
  letI : Module.Finite K V := Module.Finite.of_basis b
  let C := Submodule.span K (Set.range (graphCoeff (K := K) (fun i => b (i,0)) (fun i => b (i,1))))
  have hUpper : exteriorOrbit T (frameLines b) ≤ C := by
    apply iSup_le
    intro d
    obtain ⟨a₀,a₁,c₀,c₁,hd⟩ := hT d
    rw [frameLines, Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨w, hw, rfl⟩
    rcases Set.mem_insert_iff.mp hw with rfl | hw
    · rw [exteriorPower.map_apply_ιMulti]
      have he : T d ∘ (fun i => b (i,0)) =
          (fun i => a₀ • b (i,0) + a₁ • b (i,1)) := funext (fun i => (hd i).1)
      rw [he]
      exact homogeneousWedge_mem_coeff_span _ _ _ _
    · rcases Set.mem_singleton_iff.mp hw with rfl
      rw [exteriorPower.map_apply_ιMulti]
      have he : T d ∘ (fun i => b (i,1)) =
          (fun i => c₀ • b (i,0) + c₁ • b (i,1)) := funext (fun i => (hd i).2)
      rw [he]
      exact homogeneousWedge_mem_coeff_span _ _ _ _
  have hRankUpper : Module.finrank K (exteriorOrbit T (frameLines b)) ≤ n+1 :=
    (Submodule.finrank_mono hUpper).trans (by
      simpa only [Fintype.card_fin, Set.finrank] using
        (finrank_range_le_card (R := K) (graphCoeff (K := K) (fun i => b (i,0)) (fun i => b (i,1)))))
  have hSampleMem (t : Fin (n+1)) :
      graphWedge (K := K) (fun i => b (i,0)) (fun i => b (i,1)) (t.val : K) ∈
        exteriorOrbit T (frameLines b) := by
    obtain ⟨d, hd⟩ := hSamples t
    apply (le_iSup (fun d => (frameLines b).map (exteriorPower.map n (T d))) d)
    refine ⟨exteriorPower.ιMulti K n (fun i => b (i,0)),
      Submodule.subset_span (Set.mem_insert _ _), ?_⟩
    rw [exteriorPower.map_apply_ιMulti]
    change exteriorPower.ιMulti K n _ = exteriorPower.ιMulti K n _
    congr 1
    funext i
    exact hd i
  have hi := graphWedge_samples_independent b (fun i : Fin (n+1) => (i.val : K))
    (fun i j h => Fin.ext (Nat.cast_injective h))
  have hLower : Submodule.span K (Set.range (fun t : Fin (n+1) =>
      graphWedge (K := K) (fun i => b (i,0)) (fun i => b (i,1)) (t.val : K))) ≤
      exteriorOrbit T (frameLines b) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨t, rfl⟩
    exact hSampleMem t
  have hr := Submodule.finrank_mono hLower
  rw [finrank_span_eq_card hi, Fintype.card_fin] at hr
  exact Nat.le_antisymm hRankUpper hr

#print axioms framed_orbit_finrank
end HodgeLean.Foundations.Program.QuaternionGraph
