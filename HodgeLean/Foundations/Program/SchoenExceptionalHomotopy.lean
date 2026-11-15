module

public import HodgeLean.Foundations.Program.SchoenExceptionalDefs
public import Mathlib.Analysis.Complex.Convex

@[expose] public noncomputable section
open scoped OnePoint
open Topology Filter
namespace HodgeLean.Foundations.Program

theorem s3_continuous_dilation (γ : C(unitInterval, ℂˣ)) :
    Continuous (fun p : unitInterval × OnePoint ℂ =>
      OnePoint.map (fun z : ℂ => (γ p.1 : ℂ) * z) p.2) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨t, z⟩
  induction z using OnePoint.rec with
  | coe z =>
    apply ((Topology.IsOpenEmbedding.id.prodMap OnePoint.isOpenEmbedding_coe).continuousAt_iff
      (g := fun p : unitInterval × OnePoint ℂ =>
        OnePoint.map (fun z : ℂ => (γ p.1 : ℂ) * z) p.2) (x := (t, z))).mp
    exact (OnePoint.continuous_coe.comp
      ((Units.continuous_val.comp (γ.continuous.comp continuous_fst)).mul continuous_snd)).continuousAt
  | infty =>
    change Tendsto _ (𝓝 (t, (∞ : OnePoint ℂ))) (𝓝 (∞ : OnePoint ℂ))
    apply OnePoint.hasBasis_nhds_infty.tendsto_right_iff.mpr
    rintro K ⟨hKc, hK⟩
    let L : Set ℂ := (fun p : unitInterval × ℂ => (γ p.1 : ℂ)⁻¹ * p.2) ''
      (Set.univ ×ˢ K)
    have hL : IsCompact L := (isCompact_univ.prod hK).image
      (((Units.continuous_val.comp (γ.continuous.comp continuous_fst)).inv₀
        (fun p => Units.ne_zero (γ p.1))).mul continuous_snd)
    have hn : ((↑) '' Lᶜ ∪ {∞} : Set (OnePoint ℂ)) ∈ 𝓝 (∞ : OnePoint ℂ) :=
      OnePoint.hasBasis_nhds_infty.mem_of_mem ⟨hL.isClosed, hL⟩
    filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds hn] with p hp
    rcases hp with ⟨w, hw, he⟩ | he
    · left
      refine ⟨(γ p.1 : ℂ) * w, ?_, ?_⟩
      · intro hmem
        apply hw
        refine ⟨(p.1, (γ p.1 : ℂ) * w), ⟨Set.mem_univ _, hmem⟩, ?_⟩
        simp
      · rw [← he]
        rfl
    · right
      change OnePoint.map _ p.2 = ∞
      rw [Set.mem_singleton_iff.mp he]
      rfl

theorem s3_deck_iterate (d k : ℕ) (c : ℂ) (hc : c ≠ 0) (i : ZMod d)
    (z : OnePoint ℂ) :
    (s3_deck d c hc)^[k] (i, z) =
      (i + (k : ZMod d), OnePoint.map (fun w : ℂ => c ^ k * w) z) := by
  induction k with
  | zero =>
    induction z using OnePoint.rec <;> simp [OnePoint.map] <;> rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    induction z using OnePoint.rec with
    | infty =>
      change (i + (k : ZMod d) + 1, (∞ : OnePoint ℂ)) = (i + ((k+1 : ℕ) : ZMod d), ∞)
      simp only [Nat.cast_add, Nat.cast_one, add_assoc]
    | coe w =>
      change (i + (k : ZMod d) + 1, ((c * (c ^ k * w) : ℂ) : OnePoint ℂ)) =
        (i + ((k+1 : ℕ) : ZMod d), ((c ^ (k+1) * w : ℂ) : OnePoint ℂ))
      simp only [Nat.cast_add, Nat.cast_one, add_assoc, pow_succ', mul_assoc]

def s3_dilation_homotopy (d : ℕ) (u : ℂˣ) :
    ContinuousMap.Homotopy
      ⟨fun p : s3_Fibre d => (p.1, OnePoint.map (fun w : ℂ => (u : ℂ) * w) p.2),
        continuous_fst.prodMk (by
          exact (Homeomorph.onePointCongr (Homeomorph.mulLeft₀ (u : ℂ) u.ne_zero)).continuous.comp
            continuous_snd)⟩
      (ContinuousMap.id (s3_Fibre d)) := by
  let γ : Path u 1 := PathConnectedSpace.somePath u 1
  exact {
    toFun := fun p => (p.2.1, OnePoint.map (fun w : ℂ => (γ p.1 : ℂ) * w) p.2.2)
    continuous_toFun := continuous_snd.fst.prodMk
      ((s3_continuous_dilation γ.toContinuousMap).comp
        (continuous_fst.prodMk continuous_snd.snd))
    map_zero_left := fun p => by simp
    map_one_left := fun p => by
      rcases p with ⟨i, z⟩
      induction z using OnePoint.rec <;> simp [OnePoint.map] <;> rfl }

end HodgeLean.Foundations.Program
