import HodgeLean.Foundations.Program.SchoenCyclePoleClearing

/-! # Values of pole-corrected coefficients at paired marked points -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Filter Topology Manifold
open TauCeti.Contour
open scoped BigOperators ContDiff
namespace HodgeLean.Foundations.Program

/-- The value of an analytic extension of the corrected coefficient is its residue.
Source: Forster, Lectures on Riemann Surfaces, §10, Laurent coefficients and residues. -/
theorem s2e_corrected_coefficient_value
    (f g : ℂ → ℂ) (hf : MeromorphicAt f 0) (hg : AnalyticAt ℂ g 0)
    (he : (fun z => z * f z) =ᶠ[𝓝[≠] 0] g) :
    g 0 = residue f 0 := by
  symm
  apply residue_eq_of_tendsto_sub_mul hf
  simpa only [sub_zero] using
    (hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' he.symm

variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

/-- A corrected paired-family coefficient evaluates to the signed residue coordinate.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4, printed p. 15. -/
theorem s2e_corrected_paired_coefficient_value
    (hE : Module.finrank ℂ E = 1) {r : ℕ}
    (w : Fin r → b4c_MeroForm E C hE) (x : Fin r → C) (c : ℂ)
    (hres : ∀ i j, b4c_res (hE := hE) (w i) (x j) = if i = j then c else 0)
    (v : b3_HolForm E C × (Fin r → ℂ)) (j : Fin r)
    (g : ℂ → ℂ) (hg : AnalyticAt ℂ g 0)
    (he : (fun z => z * HurwitzPrymRR_loc hE
      (s2e_pairedDifferentialLinear hE w v) (x j) z) =ᶠ[𝓝[≠] 0] g) :
    g 0 = v.2 j * c := by
  rw [s2e_corrected_coefficient_value _ g
    ((s2e_pairedDifferentialLinear_isMeroForm hE w v.1 v.2).2 (x j)) hg he]
  exact s2e_pairedDifferentialLinear_residue_coordinate hE w x c hres v.1 v.2 j

/-- The jointly analytic corrected family retains its exact signed coordinate at the centre.
Source: Schoen, Compositio Mathematica 65 (1988), Lemmas 2.3–2.4, printed pp. 13–15. -/
theorem s2e_corrected_paired_family_values
    (hE : Module.finrank ℂ E = 1) {r n m : ℕ}
    (w : Fin r → b4c_MeroForm E C hE) (y : Fin n → C)
    (horder : ∀ i p, (-1 : WithTop ℤ) ≤ meromorphicOrderAt
      (HurwitzPrymRR_loc hE (w i) p) 0)
    (hout : ∀ i p, p ∉ Set.range y → AnalyticAt ℂ
      (HurwitzPrymRR_loc hE (w i) p) 0)
    (x : Fin r → C) (hx : ∀ j, x j ∈ Set.range y) (c : ℂ)
    (hres : ∀ i j, b4c_res (hE := hE) (w i) (x j) = if i = j then c else 0)
    (b : Fin m → b3_HolForm E C × (Fin r → ℂ)) (j : Fin r) :
    ∃ g : (Fin m → ℂ) × ℂ → ℂ,
      (∀ a, AnalyticAt ℂ g (a, 0)) ∧
      (∀ᶠ z in 𝓝[≠] (0 : ℂ), ∀ a, z * HurwitzPrymRR_loc hE
        (s2e_pairedDifferentialLinear hE w (∑ i, a i • b i)) (x j) z = g (a, z)) ∧
      (∀ a, g (a, 0) = (∑ i, a i • b i).2 j * c) := by
  obtain ⟨g, hg, he⟩ := s2e_paired_family_pole_correction hE w y horder hout b (x j)
  have he' : ∀ᶠ z in 𝓝[≠] (0 : ℂ), ∀ a, z * HurwitzPrymRR_loc hE
      (s2e_pairedDifferentialLinear hE w (∑ i, a i • b i)) (x j) z = g (a, z) := by
    simpa only [ite_eq_left (hx j)] using he
  refine ⟨g, hg, he', ?_⟩
  intro a
  apply s2e_corrected_paired_coefficient_value hE w x c hres (∑ i, a i • b i) j (fun z => g (a, z))
  · exact (hg a).comp (analyticAt_const.prod analyticAt_id)
  · filter_upwards [he'] with z hz
    exact hz a

/-- The full paired residue matrix gives opposite values on the two marked branches.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4, printed p. 15. -/
theorem s2e_corrected_paired_branch_values
    (hE : Module.finrank ℂ E = 1) {r : ℕ}
    (w : Fin r → b4c_MeroForm E C hE) (y : Fin (2 * r) → C)
    (hres : ∀ i j, b4c_res (hE := hE) (w i)
      (y ⟨2 * j.val + 1, by omega⟩) = if i = j then 1 else 0)
    (hpair : ∀ i j, b4c_res (hE := hE) (w i)
      (y ⟨2 * j.val, by omega⟩) = if i = j then -1 else 0)
    (v : b3_HolForm E C × (Fin r → ℂ)) (j : Fin r)
    (gm gp : ℂ → ℂ) (hgm : AnalyticAt ℂ gm 0) (hgp : AnalyticAt ℂ gp 0)
    (hem : (fun z => z * HurwitzPrymRR_loc hE
      (s2e_pairedDifferentialLinear hE w v) (y ⟨2 * j.val, by omega⟩) z)
        =ᶠ[𝓝[≠] 0] gm)
    (hep : (fun z => z * HurwitzPrymRR_loc hE
      (s2e_pairedDifferentialLinear hE w v) (y ⟨2 * j.val + 1, by omega⟩) z)
        =ᶠ[𝓝[≠] 0] gp) :
    gm 0 = -v.2 j ∧ gp 0 = v.2 j := by
  constructor
  · simpa only [mul_neg_one] using s2e_corrected_paired_coefficient_value hE w
      (fun j => y ⟨2 * j.val, by omega⟩) (-1) hpair v j gm hgm hem
  · simpa only [mul_one] using s2e_corrected_paired_coefficient_value hE w
      (fun j => y ⟨2 * j.val + 1, by omega⟩) 1 hres v j gp hgp hep

end HodgeLean.Foundations.Program
