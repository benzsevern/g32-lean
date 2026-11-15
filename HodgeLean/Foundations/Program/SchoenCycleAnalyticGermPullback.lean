import HodgeLean.Foundations.AnalyticDivisorAlgebraic18

/-! # Pullback of actual analytic germs -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open Filter Topology
open HodgeLean.Foundations.AnalyticDivisorAlgebraic11
namespace HodgeLean.Foundations.Program

/-- An analytic map carrying the specified centre to the specified centre pulls back analytic germs as a ring homomorphism.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4, printed p. 15;
Gunning–Rossi, Analytic Functions of Several Complex Variables, II.B. -/
def s2e_analyticGermPullback {n m : ℕ} {p : Fin n → ℂ} {q : Fin m → ℂ}
    (φ : (Fin n → ℂ) → (Fin m → ℂ)) (hφ : AnalyticAt ℂ φ p) (he : φ p = q) :
    AnalyticGermAt m q →+* AnalyticGermAt n p where
  toFun g := ⟨g.val.compTendsto φ (he ▸ hφ.continuousAt), by
    obtain ⟨f, hf, hfg⟩ := g.2
    refine ⟨f ∘ φ, hf.comp_of_eq hφ he, ?_⟩
    rw [← hfg]
    rfl⟩
  map_one' := rfl
  map_zero' := rfl
  map_mul' g h := by
    apply Subtype.ext
    obtain ⟨f, hf, hfg⟩ := g.2
    obtain ⟨k, hk, hkh⟩ := h.2
    change (g.val * h.val).compTendsto φ (he ▸ hφ.continuousAt) =
      g.val.compTendsto φ (he ▸ hφ.continuousAt) * h.val.compTendsto φ (he ▸ hφ.continuousAt)
    rw [← hfg, ← hkh]
    rfl
  map_add' g h := by
    apply Subtype.ext
    obtain ⟨f, hf, hfg⟩ := g.2
    obtain ⟨k, hk, hkh⟩ := h.2
    change (g.val + h.val).compTendsto φ (he ▸ hφ.continuousAt) =
      g.val.compTendsto φ (he ▸ hφ.continuousAt) + h.val.compTendsto φ (he ▸ hφ.continuousAt)
    rw [← hfg, ← hkh]
    rfl

/-- Analytic germ pullback preserves evaluation at the specified centres.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4, printed p. 15;
Gunning–Rossi, Analytic Functions of Several Complex Variables, II.B. -/
theorem s2e_analyticGermPullback_value {n m : ℕ} {p : Fin n → ℂ} {q : Fin m → ℂ}
    (φ : (Fin n → ℂ) → (Fin m → ℂ)) (hφ : AnalyticAt ℂ φ p) (he : φ p = q)
    (g : AnalyticGermAt m q) :
    analyticGermAtValue n p (s2e_analyticGermPullback φ hφ he g) =
      analyticGermAtValue m q g := by
  obtain ⟨f, hf, hfg⟩ := g.2
  change (g.val.compTendsto φ (he ▸ hφ.continuousAt)).value = g.val.value
  rw [← hfg]
  change (Filter.Germ.ofFun (f ∘ φ)).value = (Filter.Germ.ofFun f).value
  rw [Filter.Germ.value_ofFun, Filter.Germ.value_ofFun]
  exact congrArg f he

/-- A germ analytic at any specified centre is a unit exactly when its value there is nonzero.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4, printed p. 15;
Gunning–Rossi, Analytic Functions of Several Complex Variables, II.B. -/
theorem s2e_analyticGermAt_isUnit_iff {n : ℕ} {p : Fin n → ℂ}
    (g : AnalyticGermAt n p) : IsUnit g ↔ analyticGermAtValue n p g ≠ 0 := by
  constructor
  · intro hg
    exact (hg.map (analyticGermAtValue n p)).ne_zero
  · intro hv
    obtain ⟨f, hf, hfg⟩ := g.2
    have hf0 : f p ≠ 0 := by
      change g.val.value ≠ 0 at hv
      rwa [← hfg, Filter.Germ.value_ofFun] at hv
    let k : AnalyticGermAt n p :=
      ⟨Filter.Germ.ofFun (fun z => (f z)⁻¹), fun z => (f z)⁻¹, hf.inv hf0, rfl⟩
    apply isUnit_iff_exists_inv.mpr
    refine ⟨k, Subtype.ext ?_⟩
    change g.val * k.val = 1
    rw [← hfg]
    apply Filter.Germ.coe_eq.mpr
    filter_upwards [hf.continuousAt.eventually_ne hf0] with z hz
    exact mul_inv_cancel₀ hz

/-- Pullback along a centred analytic map reflects as well as preserves units of analytic germs.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4, printed p. 15;
Gunning–Rossi, Analytic Functions of Several Complex Variables, II.B. -/
theorem s2e_analyticGermPullback_isUnit_iff {n m : ℕ} {p : Fin n → ℂ} {q : Fin m → ℂ}
    (φ : (Fin n → ℂ) → (Fin m → ℂ)) (hφ : AnalyticAt ℂ φ p) (he : φ p = q)
    (g : AnalyticGermAt m q) :
    IsUnit (s2e_analyticGermPullback φ hφ he g) ↔ IsUnit g := by
  rw [s2e_analyticGermAt_isUnit_iff, s2e_analyticGermAt_isUnit_iff,
    s2e_analyticGermPullback_value]

/-- A squarefree pulled-back analytic germ makes the original germ squarefree, including for ramified maps.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4, printed p. 15;
Gunning–Rossi, Analytic Functions of Several Complex Variables, II.B. -/
theorem s2e_analyticGermPullback_squarefree {n m : ℕ} {p : Fin n → ℂ} {q : Fin m → ℂ}
    (φ : (Fin n → ℂ) → (Fin m → ℂ)) (hφ : AnalyticAt ℂ φ p) (he : φ p = q)
    (g : AnalyticGermAt m q) (hg : Squarefree (s2e_analyticGermPullback φ hφ he g)) :
    Squarefree g := by
  intro r hr
  apply (s2e_analyticGermPullback_isUnit_iff φ hφ he r).mp
  apply hg
  simpa only [map_mul] using map_dvd (s2e_analyticGermPullback φ hφ he) hr

end HodgeLean.Foundations.Program
