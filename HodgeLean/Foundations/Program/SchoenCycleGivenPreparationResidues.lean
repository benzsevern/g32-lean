import HodgeLean.Foundations.Program.SchoenCyclePreparedResidues

/-! # Signed constant coefficients for a specified preparation -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Filter Topology Manifold
open HodgeLean.Foundations.AnalyticDivisorAlgebraic4
open HodgeLean.Foundations.AnalyticDivisorAlgebraic5
open scoped BigOperators ContDiff
namespace HodgeLean.Foundations.Program
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

/-- The supplied preparation has the signed residue as its constant coefficient up to a unit.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4, printed p. 15. -/
theorem s2e_given_preparation_signed_constant_term
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) {r m : ℕ}
    (w : Fin r → b4c_MeroForm E C hE) (y : Fin (2 * r) → C)
    (hres : ∀ i j, b4c_res (hE := hE) (w i)
      (y ⟨2 * j.val + 1, by omega⟩) = if i = j then 1 else 0)
    (hpair : ∀ i j, b4c_res (hE := hE) (w i)
      (y ⟨2 * j.val, by omega⟩) = if i = j then -1 else 0)
    (b : Fin m → b3_HolForm E C × (Fin r → ℂ))
    (a : Fin m → ℂ) (j : Fin r) (s : Bool)
    {d : ℕ} (g u : (Fin m → ℂ) × ℂ → ℂ)
    (c : Fin d → (Fin m → ℂ) → ℂ)
    (hg : ∀ a', AnalyticAt ℂ g (a', 0))
    (he : let p := if s then y ⟨2 * j.val + 1, by omega⟩ else y ⟨2 * j.val, by omega⟩
      ∀ᶠ z in 𝓝[≠] (0 : ℂ), ∀ a', z * HurwitzPrymRR_loc hE
        (s2e_pairedDifferentialLinear hE w (∑ i, a' i • b i)) p z = g (a', z))
    (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (hprep : (fun tz => g (a + tz.1, tz.2)) =ᶠ[𝓝 0]
      fun tz => u tz * monicInLast c tz) :
    ∃ η : (Fin m → ℂ) → ℂ, AnalyticAt ℂ η 0 ∧ η 0 ≠ 0 ∧
      ∀ᶠ t in 𝓝 0, (monicPoly c t).coeff 0 =
        η t * ((∑ i, (a + t) i • b i).2 j * (if s then 1 else -1)) := by
  classical
  let xs : Fin r → C := fun l =>
    if s then y ⟨2 * l.val + 1, by omega⟩ else y ⟨2 * l.val, by omega⟩
  let sign : ℂ := if s then 1 else -1
  have hs : ∀ i l, b4c_res (hE := hE) (w i) (xs l) =
      if i = l then sign else 0 := by
    cases s
    · exact hpair
    · exact hres
  have hv (t : Fin m → ℂ) : g (a + t, 0) = (∑ i, (a + t) i • b i).2 j * sign := by
    apply s2e_corrected_paired_coefficient_value hE w xs sign hs _ j
      (fun z => g (a + t, z))
    · exact (hg (a + t)).comp (f := fun z : ℂ => (a + t, z))
        (analyticAt_const.prod analyticAt_id)
    · filter_upwards [he] with z hz
      exact hz (a + t)
  exact s2e_prepared_constant_term_unit
    (fun tz => g (a + tz.1, tz.2)) u c
    (fun t => (∑ i, (a + t) i • b i).2 j * sign) hu hu0 hprep hv

end HodgeLean.Foundations.Program
