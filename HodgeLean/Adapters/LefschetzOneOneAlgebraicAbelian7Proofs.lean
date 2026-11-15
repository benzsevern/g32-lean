import HodgeLean.Foundations.AnalyticStratification
import HodgeLean.Foundations.CechExponential
import HodgeLean.Foundations.SeveralVariableDbar
import HodgeLean.Foundations.AnalyticDivisorAlgebraic19
import Mathlib.Analysis.Complex.LocallyUniformLimit
import HodgeLean.Foundations.DolbeaultCurve2
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import HodgeLean.Foundations.DolbeaultCurveProofs
import Mathlib.Geometry.Manifold.PartitionOfUnity
import HodgeLean.Foundations.AnalyticDivisorAlgebraic2

noncomputable section
open Filter Set Topology
open HodgeLean.Foundations
open HodgeLean.Foundations.AnalyticDivisorAlgebraic7
open HodgeLean.Foundations.AnalyticDivisorAlgebraic11
open HodgeLean.Foundations.AnalyticDivisorAlgebraic5
open HodgeLean.Foundations.AnalyticDivisorAlgebraic6
namespace HodgeLean.Adapters

/-! # Algebraic Appell--Humbert stage 7

Explicit interfaces for reduced transition functions, Cousin trivialization, and analytic
stratification.  The final three statements have the corresponding stage-five types.
HC no distance; AV milestone no distance.
-/

private theorem bh7_germ_isUnit_of_value_ne {n : ℕ} {p : Fin n → ℂ}
    (x : AnalyticGermAt n p) (hx : analyticGermAtValue n p x ≠ 0) : IsUnit x := by
  obtain ⟨f, hf, hfx⟩ := x.2
  have hfp : f p ≠ 0 := by
    change x.1.value ≠ 0 at hx
    rw [← hfx] at hx
    simpa using hx
  let y : AnalyticGermAt n p :=
    ⟨↑(fun z ↦ (f z)⁻¹), fun z ↦ (f z)⁻¹, hf.inv hfp, rfl⟩
  apply isUnit_iff_exists_inv.mpr
  refine ⟨y, ?_⟩
  apply Subtype.ext
  change x.1 * y.1 = 1
  rw [← hfx]
  exact Germ.coe_eq.mpr <| (hf.continuousAt.eventually_ne hfp).mono fun z hz ↦
    mul_inv_cancel₀ hz

private theorem bh7_squarefree_iff_isSquareFreeAt {n : ℕ} {p : Fin n → ℂ}
    {f : (Fin n → ℂ) → ℂ} (hf : AnalyticAt ℂ f p) :
    Squarefree (⟨Germ.ofFun f, f, hf, rfl⟩ : AnalyticGermAt n p) ↔
      IsSquareFreeAt f p := by
  let F : AnalyticGermAt n p := ⟨Germ.ofFun f, f, hf, rfl⟩
  constructor
  · intro hs g h hg hh hg0 hfac
    let G : AnalyticGermAt n p := ⟨Germ.ofFun g, g, hg, rfl⟩
    let H : AnalyticGermAt n p := ⟨Germ.ofFun h, h, hh, rfl⟩
    have hd : G * G ∣ F := by
      refine ⟨H, ?_⟩
      apply Subtype.ext
      exact Germ.coe_eq.mpr (hfac.mono fun z hz ↦ by simpa [pow_two, mul_assoc] using hz)
    have hu := hs G hd
    exact (hu.map (analyticGermAtValue n p)).ne_zero hg0
  · intro hs G hd
    obtain ⟨H, hGH⟩ := hd
    by_contra hGu
    obtain ⟨g, hg, hG⟩ := G.2
    obtain ⟨h, hh, hH⟩ := H.2
    have hg0 : g p = 0 := by
      by_contra hgp
      apply hGu
      apply bh7_germ_isUnit_of_value_ne G
      change G.1.value ≠ 0
      rw [← hG, Germ.value_ofFun]
      exact hgp
    apply hs g h hg hh hg0
    apply Germ.coe_eq.mp
    calc
      Germ.ofFun f = F.1 := rfl
      _ = ((G * G) * H).1 := congrArg Subtype.val hGH
      _ = (G.1 * G.1) * H.1 := rfl
      _ = (Germ.ofFun g * Germ.ofFun g) * Germ.ofFun h := by rw [hG, hH]
      _ = Germ.ofFun (fun z ↦ g z ^ 2 * h z) := by
        apply Germ.coe_eq.mpr
        exact Eventually.of_forall fun z ↦ by simp [pow_two]

private def bh7_splitCoordinates (m : ℕ) :
    (Fin (m + 1) → ℂ) ≃L[ℂ] ((Fin m → ℂ) × ℂ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toEquiv := (Fin.snocEquiv (fun _ : Fin (m + 1) ↦ ℂ)).symm.trans
        (Equiv.prodComm _ _)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

private theorem bh7_eventually_isSquareFreeAt {m : ℕ} {p : Fin (m + 1) → ℂ}
    {f : (Fin (m + 1) → ℂ) → ℂ} (hf : AnalyticAt ℂ f p)
    (hsf : IsSquareFreeAt f p) : ∀ᶠ q in nhds p, IsSquareFreeAt f q := by
  let L := bh7_splitCoordinates m
  let T : ((Fin m → ℂ) × ℂ) → (Fin (m + 1) → ℂ) := fun y ↦ p + L.symm y
  have hT (y) : AnalyticAt ℂ T y := analyticAt_const.add (L.symm.analyticAt y)
  have hfT : AnalyticAt ℂ (fun y ↦ f (T y)) 0 :=
    hf.comp_of_eq (hT 0) (by simp [T])
  have hsfT : IsSquareFreeAt (fun y ↦ f (T y)) 0 := by
    intro a b ha hb ha0 hab
    let A : (Fin (m + 1) → ℂ) → ℂ := fun z ↦ a (L (z - p))
    let B : (Fin (m + 1) → ℂ) → ℂ := fun z ↦ b (L (z - p))
    have hS : AnalyticAt ℂ (fun z ↦ L (z - p)) p :=
      (L.analyticAt _).comp (analyticAt_id.sub analyticAt_const)
    apply hsf A B (ha.comp_of_eq hS (by simp)) (hb.comp_of_eq hS (by simp))
      (by simp [A, ha0])
    have ht : Tendsto (fun z ↦ L (z - p)) (nhds p) (nhds 0) := by
      simpa only [ContinuousAt, sub_self, map_zero] using hS.continuousAt
    filter_upwards [ht.eventually hab] with z hz
    simpa [T, A, B] using hz
  have hnear := spec_eventually_isSquareFreeAt hfT hsfT
  have hS : Tendsto (fun q : Fin (m + 1) → ℂ ↦ L (q - p)) (nhds p) (nhds 0) := by
    have ha : AnalyticAt ℂ (fun q ↦ L (q - p)) p :=
      (L.analyticAt _).comp (analyticAt_id.sub analyticAt_const)
    simpa only [ContinuousAt, sub_self, map_zero] using ha.continuousAt
  filter_upwards [hS.eventually hnear] with q hq
  intro A B hA hB hA0 hab
  let a : ((Fin m → ℂ) × ℂ) → ℂ := fun y ↦ A (T y)
  let b : ((Fin m → ℂ) × ℂ) → ℂ := fun y ↦ B (T y)
  have hqT : T (L (q - p)) = q := by simp [T]
  apply hq a b (hA.comp_of_eq (hT _) hqT) (hB.comp_of_eq (hT _) hqT)
    (by change A (T (L (q - p))) = 0; rw [hqT, hA0])
  have ht : Tendsto T (nhds (L (q - p))) (nhds q) := by
    simpa only [ContinuousAt, hqT] using (hT (L (q - p))).continuousAt
  filter_upwards [ht.eventually hab] with y hy
  simpa [a, b] using hy

/-- Reduced local equations can be shrunk to an open cover while retaining their germs.
Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, II.B,
local representatives of analytic germs. -/
theorem bh7_reduced_atlas_aux (n : ℕ) (S : Set (Fin n → ℂ))
    (hloc : ∀ p, ∃ (g : (Fin n → ℂ) → ℂ) (hg : AnalyticAt ℂ g p),
      Squarefree (⟨Germ.ofFun g, g, hg, rfl⟩ : AnalyticGermAt n p) ∧
      ∀ᶠ z in 𝓝 p, g z = 0 ↔ z ∈ S) :
    ∃ (U : (Fin n → ℂ) → Set (Fin n → ℂ))
      (g : (Fin n → ℂ) → (Fin n → ℂ) → ℂ),
      (∀ p, IsOpen (U p)) ∧ (∀ p, p ∈ U p) ∧
      ∃ hg : ∀ p, AnalyticOnNhd ℂ (g p) (U p),
        (∀ p q (hq : q ∈ U p),
          Squarefree (⟨Germ.ofFun (g p), g p, hg p q hq, rfl⟩ : AnalyticGermAt n q)) ∧
        (∀ p q, q ∈ U p → (g p q = 0 ↔ q ∈ S)) := by
  classical
  choose g hg hgr hzero using hloc
  have hnear : ∀ p, ∀ᶠ q in nhds p, IsSquareFreeAt (g p) q := by
    intro p
    have hsf : IsSquareFreeAt (g p) p :=
      (bh7_squarefree_iff_isSquareFreeAt (hg p)).mp (hgr p)
    have hsfa : ∀ᶠ q in nhds p, IsSquareFreeAt (g p) q := by
      cases n with
      | zero =>
          filter_upwards [] with q
          simpa [Subsingleton.elim q p] using hsf
      | succ m => exact bh7_eventually_isSquareFreeAt (hg p) hsf
    exact hsfa
  have hall : ∀ p, ∀ᶠ q in nhds p,
      ∃ ha : AnalyticAt ℂ (g p) q,
        Squarefree (⟨Germ.ofFun (g p), g p, ha, rfl⟩ : AnalyticGermAt n q) ∧
        (g p q = 0 ↔ q ∈ S) := by
    intro p
    filter_upwards [(hg p).eventually_analyticAt, hnear p, hzero p] with q ha hs hz
    exact ⟨ha, (bh7_squarefree_iff_isSquareFreeAt ha).mpr hs, hz⟩
  choose U hUsub hUopen hpU using fun p ↦ mem_nhds_iff.mp (hall p)
  refine ⟨U, g, hUopen, hpU, ?_, ?_, ?_⟩
  · intro p q hq
    exact (hUsub p hq).choose
  · intro p q hq
    exact (hUsub p hq).choose_spec.1
  · intro p q hq
    exact (hUsub p hq).choose_spec.2

/-- Locally associated nonzero analytic equations have unit ratios on their overlap.
Source: Gunning--Rossi, II.B, analytic unique factorization and shrinking. -/
theorem bh7_transition_units_aux (n : ℕ)
    (U : (Fin n → ℂ) → Set (Fin n → ℂ))
    (g : (Fin n → ℂ) → (Fin n → ℂ) → ℂ)
    (hU : ∀ p, IsOpen (U p))
    (hg : ∀ p, AnalyticOnNhd ℂ (g p) (U p))
    (hgn : ∀ p z (hz : z ∈ U p),
      (⟨Germ.ofFun (g p), g p, hg p z hz, rfl⟩ : AnalyticGermAt n z) ≠ 0)
    (hassoc : ∀ p q z, z ∈ U p ∩ U q → AreAssociatedAt (g p) (g q) z) :
    ∃ u : (Fin n → ℂ) → (Fin n → ℂ) → (Fin n → ℂ) → ℂ,
      (∀ p q, AnalyticOnNhd ℂ (u p q) (U p ∩ U q)) ∧
      (∀ p q z, z ∈ U p ∩ U q → u p q z ≠ 0) ∧
      (∀ p q z, z ∈ U p ∩ U q → g p z = u p q z * g q z) := by
  classical
  choose a ha han hae using hassoc
  let u : (Fin n → ℂ) → (Fin n → ℂ) → (Fin n → ℂ) → ℂ :=
    fun p q z ↦ if hz : z ∈ U p ∩ U q then a p q z hz z else 1
  refine ⟨u, ?_, ?_, ?_⟩
  · intro p q x hx
    have hax := ha p q x hx
    obtain ⟨s, hs, hso, hxs⟩ := mem_nhds_iff.mp (hae p q x hx)
    apply hax.congr
    filter_upwards [hax.eventually_analyticAt, hso.mem_nhds hxs,
      (hU p).mem_nhds hx.1, (hU q).mem_nhds hx.2] with y haxy hys hyp hyq
    simp only [u, dif_pos (show y ∈ U p ∩ U q from ⟨hyp, hyq⟩)]
    let A : AnalyticGermAt n y :=
      ⟨Germ.ofFun (a p q x hx), a p q x hx, haxy, rfl⟩
    let B : AnalyticGermAt n y :=
      ⟨Germ.ofFun (a p q y ⟨hyp, hyq⟩), a p q y ⟨hyp, hyq⟩,
        ha p q y ⟨hyp, hyq⟩, rfl⟩
    let G : AnalyticGermAt n y :=
      ⟨Germ.ofFun (g q), g q, hg q y hyq, rfl⟩
    obtain ⟨e, -, -⟩ :=
      AnalyticDivisorAlgebraic11.spec_germ_translation_equiv n y
    letI : UniqueFactorizationMonoid (AnalyticGermAt n y) :=
      e.symm.toMulEquiv.uniqueFactorizationMonoid
        (AnalyticDivisorAlgebraic6.spec_analyticGerm_ufd n)
    letI : IsCancelMulZero (AnalyticGermAt n y) :=
      UniqueFactorizationMonoid.toIsCancelMulZero
    have hAG : A * G = B * G := by
      apply Subtype.ext
      apply Germ.coe_eq.mpr
      filter_upwards [hso.mem_nhds hys, hae p q y ⟨hyp, hyq⟩] with w hws hby
      exact (hs hws).symm.trans hby
    have hAB : A = B := mul_right_cancel₀ (hgn q y hyq) hAG
    have hv := congrArg (analyticGermAtValue n y) hAB
    change (Germ.ofFun (a p q x hx)).value =
      (Germ.ofFun (a p q y ⟨hyp, hyq⟩)).value at hv
    simpa only [Germ.value_ofFun] using hv
  · intro p q z hz
    simpa only [u, dif_pos hz] using han p q z hz
  · intro p q z hz
    simpa only [u, dif_pos hz] using (hae p q z hz).self_of_nhds

/-- Unit ratios between fixed reduced equations are unique on overlaps.
Source: Gunning--Rossi, II.B, identity theorem and cancellation in analytic local rings. -/
theorem bh7_transition_unique_aux (n : ℕ)
    (U : (Fin n → ℂ) → Set (Fin n → ℂ))
    (g : (Fin n → ℂ) → (Fin n → ℂ) → ℂ)
    (u : (Fin n → ℂ) → (Fin n → ℂ) → (Fin n → ℂ) → ℂ)
    (hU : ∀ p, IsOpen (U p))
    (hg : ∀ p, AnalyticOnNhd ℂ (g p) (U p))
    (hgr : ∀ p z (hz : z ∈ U p),
      Squarefree (⟨Germ.ofFun (g p), g p, hg p z hz, rfl⟩ : AnalyticGermAt n z))
    (hgn : ∀ p z (hz : z ∈ U p),
      (⟨Germ.ofFun (g p), g p, hg p z hz, rfl⟩ : AnalyticGermAt n z) ≠ 0)
    (hu : ∀ p q, AnalyticOnNhd ℂ (u p q) (U p ∩ U q))
    (hun : ∀ p q z, z ∈ U p ∩ U q → u p q z ≠ 0)
    (he : ∀ p q z, z ∈ U p ∩ U q → g p z = u p q z * g q z) :
    (∀ p z, z ∈ U p → u p p z = 1) ∧
      (∀ p q r z, z ∈ U p ∩ U q ∩ U r → u p q z * u q r z = u p r z) := by
  constructor
  · intro p z hz
    obtain ⟨e, -, -⟩ :=
      AnalyticDivisorAlgebraic11.spec_germ_translation_equiv n z
    letI : UniqueFactorizationMonoid (AnalyticGermAt n z) :=
      e.symm.toMulEquiv.uniqueFactorizationMonoid
        (AnalyticDivisorAlgebraic6.spec_analyticGerm_ufd n)
    letI : IsCancelMulZero (AnalyticGermAt n z) :=
      UniqueFactorizationMonoid.toIsCancelMulZero
    let G : AnalyticGermAt n z :=
      ⟨Germ.ofFun (g p), g p, hg p z hz, rfl⟩
    let A : AnalyticGermAt n z :=
      ⟨Germ.ofFun (u p p), u p p, hu p p z ⟨hz, hz⟩, rfl⟩
    have hAG : A * G = 1 * G := by
      apply Subtype.ext
      apply Germ.coe_eq.mpr
      filter_upwards [(hU p).mem_nhds hz] with w hw
      simpa only [one_mul] using (he p p w ⟨hw, hw⟩).symm
    have hA : A = 1 := mul_right_cancel₀ (hgn p z hz) hAG
    have hv := congrArg (analyticGermAtValue n z) hA
    change (Germ.ofFun (u p p)).value = 1 at hv
    simpa only [Germ.value_ofFun] using hv
  · intro p q r z hz
    obtain ⟨e, -, -⟩ :=
      AnalyticDivisorAlgebraic11.spec_germ_translation_equiv n z
    letI : UniqueFactorizationMonoid (AnalyticGermAt n z) :=
      e.symm.toMulEquiv.uniqueFactorizationMonoid
        (AnalyticDivisorAlgebraic6.spec_analyticGerm_ufd n)
    letI : IsCancelMulZero (AnalyticGermAt n z) :=
      UniqueFactorizationMonoid.toIsCancelMulZero
    let G : AnalyticGermAt n z :=
      ⟨Germ.ofFun (g r), g r, hg r z hz.2, rfl⟩
    let A : AnalyticGermAt n z :=
      ⟨Germ.ofFun (fun w ↦ u p q w * u q r w), _,
        (hu p q z ⟨hz.1.1, hz.1.2⟩).mul (hu q r z ⟨hz.1.2, hz.2⟩), rfl⟩
    let B : AnalyticGermAt n z :=
      ⟨Germ.ofFun (u p r), u p r, hu p r z ⟨hz.1.1, hz.2⟩, rfl⟩
    have hAB : A * G = B * G := by
      apply Subtype.ext
      apply Germ.coe_eq.mpr
      filter_upwards [(hU p).mem_nhds hz.1.1, (hU q).mem_nhds hz.1.2,
        (hU r).mem_nhds hz.2] with w hp hq hr
      rw [mul_assoc, ← he q r w ⟨hq, hr⟩, ← he p q w ⟨hp, hq⟩,
        he p r w ⟨hp, hr⟩]
    have hA : A = B := mul_right_cancel₀ (hgn r z hz.2) hAB
    have hv := congrArg (analyticGermAtValue n z) hA
    change (Germ.ofFun (fun w ↦ u p q w * u q r w)).value =
      (Germ.ofFun (u p r)).value at hv
    simpa only [Germ.value_ofFun] using hv

/-- The reduced-atlas and uniqueness steps assemble the stage-five transition cocycle.
Source: Gunning--Rossi, II.B. -/
theorem bh7_unit_transition_cocycle_aux
    (n : ℕ) (S : Set (Fin n → ℂ))
    (hloc : ∀ p, ∃ (g : (Fin n → ℂ) → ℂ) (hg : AnalyticAt ℂ g p),
      Squarefree (⟨Germ.ofFun g, g, hg, rfl⟩ : AnalyticGermAt n p) ∧
      ∀ᶠ z in 𝓝 p, g z = 0 ↔ z ∈ S) :
    ∃ (U : (Fin n → ℂ) → Set (Fin n → ℂ))
      (g : (Fin n → ℂ) → (Fin n → ℂ) → ℂ)
      (u : (Fin n → ℂ) → (Fin n → ℂ) → (Fin n → ℂ) → ℂ),
      (∀ p, IsOpen (U p)) ∧ (∀ p, p ∈ U p) ∧
      ∃ hg : ∀ p, AnalyticOnNhd ℂ (g p) (U p),
        (∀ p q (hq : q ∈ U p),
          Squarefree (⟨Germ.ofFun (g p), g p, hg p q hq, rfl⟩ : AnalyticGermAt n q)) ∧
        (∀ p q, q ∈ U p → (g p q = 0 ↔ q ∈ S)) ∧
        (∀ p q, AnalyticOnNhd ℂ (u p q) (U p ∩ U q)) ∧
        (∀ p q z, z ∈ U p ∩ U q → u p q z ≠ 0) ∧
        (∀ p q z, z ∈ U p ∩ U q → g p z = u p q z * g q z) ∧
        (∀ p z, z ∈ U p → u p p z = 1) ∧
        (∀ p q r z, z ∈ U p ∩ U q ∩ U r → u p q z * u q r z = u p r z) := by
  obtain ⟨U, g, hU, hc, hg, hgr, hzero⟩ := bh7_reduced_atlas_aux n S hloc
  have hassoc : ∀ p q z, z ∈ U p ∩ U q → AreAssociatedAt (g p) (g q) z := by
    intro p q z hz
    apply AnalyticDivisorAlgebraic18.spec_reduced_zero_germs_associated n z
      (g p) (g q) (hg p z hz.1) (hg q z hz.2) (hgr p z hz.1) (hgr q z hz.2)
    filter_upwards [(hU p).mem_nhds hz.1, (hU q).mem_nhds hz.2] with w hp hq
    exact (hzero p w hp).trans (hzero q w hq).symm
  obtain ⟨u, hu, hun, he⟩ := bh7_transition_units_aux n U g hU hg
    (fun p z hz ↦ (hgr p z hz).ne_zero) hassoc
  obtain ⟨hd, ht⟩ := bh7_transition_unique_aux n U g u hU hg hgr
    (fun p z hz ↦ (hgr p z hz).ne_zero) hu hun he
  exact ⟨U, g, u, hU, hc, hg, hgr, hzero, hu, hun, he, hd, ht⟩

open scoped ContDiff in
/-- Step 1: a smooth partition of unity splits an analytic additive cocycle smoothly.
Source: Gunning--Rossi, Chapter VIII, the partition-of-unity construction for Cousin I. -/
private theorem bh7_cousin_step1 (n : ℕ)
    (U : (Fin n → ℂ) → Set (Fin n → ℂ))
    (hU : ∀ p, IsOpen (U p)) (hcover : ∀ p, p ∈ U p)
    (a : (Fin n → ℂ) → (Fin n → ℂ) → (Fin n → ℂ) → ℂ)
    (ha : ∀ p q, AnalyticOnNhd ℂ (a p q) (U p ∩ U q))
    (hcocycle : ∀ p q r z, z ∈ U p ∩ U q ∩ U r →
      a p q z + a q r z = a p r z) :
    ∃ b : (Fin n → ℂ) → (Fin n → ℂ) → ℂ,
      (∀ p z, z ∈ U p → ContDiffAt ℝ ∞ (b p) z) ∧
      (∀ p q z, z ∈ U p ∩ U q → a p q z = b q z - b p z) := by
  classical
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (modelWithCornersSelf ℝ (Fin n → ℂ)) isClosed_univ U hU
    (fun z _ ↦ mem_iUnion.mpr ⟨z, hcover z⟩)
  let b : (Fin n → ℂ) → (Fin n → ℂ) → ℂ :=
    fun p z ↦ ∑ᶠ r, ρ r z • a r p z
  refine ⟨b, ?_, ?_⟩
  · intro p z hz
    apply ρ.contDiffAt_finsum
    intro r hr
    exact (ha r p z ⟨hρ r hr, hz⟩).contDiffAt.restrict_scalars ℝ
  · intro p q z hz
    change a p q z = (∑ᶠ r, ρ r z • a r q z) - ∑ᶠ r, ρ r z • a r p z
    rw [← ρ.sum_finsupport_smul_eq_finsum z (fun r ↦ a r q),
      ← ρ.sum_finsupport_smul_eq_finsum z (fun r ↦ a r p), ← Finset.sum_sub_distrib]
    calc
      a p q z = (∑ r ∈ ρ.finsupport z, ρ r z) • a p q z := by
        rw [ρ.sum_finsupport z (mem_univ z), one_smul]
      _ = ∑ r ∈ ρ.finsupport z, ρ r z • a p q z := Finset.sum_smul
      _ = ∑ r ∈ ρ.finsupport z, (ρ r z • a r q z - ρ r z • a r p z) := by
        apply Finset.sum_congr rfl
        intro r hr
        have hrU : z ∈ U r := hρ r (subset_closure ((ρ.mem_finsupport z).mp hr))
        rw [← smul_sub, ← hcocycle r p q z ⟨⟨hrU, hz.1⟩, hz.2⟩,
          add_sub_cancel_left]

open scoped ContDiff in
/-- Step 2: the conjugate-linear derivatives of smooth potentials agree on overlaps.
Source: Gunning--Rossi, Chapter VIII, the Dolbeault construction for Cousin I. -/
private theorem bh7_cousin_step2 (n : ℕ)
    (U : (Fin n → ℂ) → Set (Fin n → ℂ)) (hU : ∀ p, IsOpen (U p))
    (a : (Fin n → ℂ) → (Fin n → ℂ) → (Fin n → ℂ) → ℂ)
    (ha : ∀ p q, AnalyticOnNhd ℂ (a p q) (U p ∩ U q))
    (b : (Fin n → ℂ) → (Fin n → ℂ) → ℂ)
    (hb : ∀ p z, z ∈ U p → ContDiffAt ℝ ∞ (b p) z)
    (he : ∀ p q z, z ∈ U p ∩ U q → a p q z = b q z - b p z)
    (p q z : Fin n → ℂ) (hz : z ∈ U p ∩ U q) :
    antiLinearPart (fderiv ℝ (b p) z) = antiLinearPart (fderiv ℝ (b q) z) := by
  have heq : a p q =ᶠ[𝓝 z] fun w ↦ b q w - b p w := by
    filter_upwards [((hU p).inter (hU q)).mem_nhds hz] with w hw
    exact he p q w hw
  have hz0 : antiLinearPart (fderiv ℝ (a p q) z) = 0 := by
    rw [(ha p q z hz).differentiableAt.fderiv_restrictScalars ℝ]
    exact antiLinearPart_restrictScalars _
  rw [heq.fderiv_eq, fderiv_fun_sub ((hb q z hz.2).differentiableAt (by simp))
    ((hb p z hz.1).differentiableAt (by simp)), map_sub] at hz0
  exact (sub_eq_zero.mp hz0).symm

open scoped ContDiff in
/-- Step 3: the local derivatives glue to a globally smooth conjugate-linear form.
Source: Gunning--Rossi, Chapter VIII, the Dolbeault construction for Cousin I. -/
private theorem bh7_cousin_step3 (n : ℕ)
    (U : (Fin n → ℂ) → Set (Fin n → ℂ))
    (hU : ∀ p, IsOpen (U p)) (hcover : ∀ p, p ∈ U p)
    (a : (Fin n → ℂ) → (Fin n → ℂ) → (Fin n → ℂ) → ℂ)
    (ha : ∀ p q, AnalyticOnNhd ℂ (a p q) (U p ∩ U q))
    (b : (Fin n → ℂ) → (Fin n → ℂ) → ℂ)
    (hb : ∀ p z, z ∈ U p → ContDiffAt ℝ ∞ (b p) z)
    (he : ∀ p q z, z ∈ U p ∩ U q → a p q z = b q z - b p z) :
    ∃ F : (Fin n → ℂ) → ((Fin n → ℂ) →L[ℝ] ℂ),
      ContDiff ℝ ∞ F ∧
      (∀ p z, z ∈ U p → F z = antiLinearPart (fderiv ℝ (b p) z)) ∧
      (∀ z, antiLinearPart (F z) = F z) := by
  let F : (Fin n → ℂ) → ((Fin n → ℂ) →L[ℝ] ℂ) :=
    fun z ↦ antiLinearPart (fderiv ℝ (b z) z)
  have hF : ∀ p z, z ∈ U p → F z = antiLinearPart (fderiv ℝ (b p) z) := by
    intro p z hz
    exact bh7_cousin_step2 n U hU a ha b hb he z p z ⟨hcover z, hz⟩
  refine ⟨F, contDiff_iff_contDiffAt.mpr ?_, hF, ?_⟩
  · intro z
    have heq : F =ᶠ[𝓝 z] fun w ↦ antiLinearPart (fderiv ℝ (b z) w) := by
      filter_upwards [(hU z).mem_nhds (hcover z)] with w hw
      exact hF z w hw
    exact (antiLinearPart.contDiff.contDiffAt.comp z
      ((hb z z (hcover z)).fderiv_right (by simp))).congr_of_eventuallyEq heq
  · intro z
    exact antiLinearPart_antiLinearPart _

open scoped ContDiff in
/-- Step 4: a conjugate-linear differential is closed, by symmetry of second derivatives.
The displayed identity is the vanishing of its exterior conjugate-linear derivative.
Source: Gunning--Rossi, Chapter VIII, the identity ∂̄² = 0. -/
private theorem bh7_cousin_step4 (n : ℕ) (f : (Fin n → ℂ) → ℂ)
    (z : Fin n → ℂ) (hf : ContDiffAt ℝ ∞ f z) (v w : Fin n → ℂ) :
    fderiv ℝ (fun x ↦ antiLinearPart (fderiv ℝ f x)) z v w +
        Complex.I * fderiv ℝ (fun x ↦ antiLinearPart (fderiv ℝ f x)) z
          (Complex.I • v) w =
      fderiv ℝ (fun x ↦ antiLinearPart (fderiv ℝ f x)) z w v +
        Complex.I * fderiv ℝ (fun x ↦ antiLinearPart (fderiv ℝ f x)) z
          (Complex.I • w) v := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := 1) (by simp)).differentiableAt one_ne_zero
  have hD : fderiv ℝ (fun x ↦ antiLinearPart (fderiv ℝ f x)) z =
      antiLinearPart ∘L fderiv ℝ (fderiv ℝ f) z :=
    (antiLinearPart.hasFDerivAt.comp z hd.hasFDerivAt).fderiv
  have hs := hf.isSymmSndFDerivAt (by simp)
  simp only [hD, ContinuousLinearMap.comp_apply, antiLinearPart_apply, Complex.real_smul]
  rw [hs v w, hs v (Complex.I • w), hs (Complex.I • v) w,
    hs (Complex.I • v) (Complex.I • w)]
  ring

open scoped ContDiff in
/-- Step 5: the global form obtained by gluing local differentials is closed.
Source: Gunning--Rossi, Chapter VIII, the Dolbeault construction for Cousin I. -/
private theorem bh7_cousin_step5 (n : ℕ)
    (U : (Fin n → ℂ) → Set (Fin n → ℂ))
    (hU : ∀ p, IsOpen (U p)) (hcover : ∀ p, p ∈ U p)
    (b : (Fin n → ℂ) → (Fin n → ℂ) → ℂ)
    (hb : ∀ p z, z ∈ U p → ContDiffAt ℝ ∞ (b p) z)
    (F : (Fin n → ℂ) → ((Fin n → ℂ) →L[ℝ] ℂ))
    (hF : ∀ p z, z ∈ U p → F z = antiLinearPart (fderiv ℝ (b p) z))
    (z v w : Fin n → ℂ) :
    fderiv ℝ F z v w + Complex.I * fderiv ℝ F z (Complex.I • v) w =
      fderiv ℝ F z w v + Complex.I * fderiv ℝ F z (Complex.I • w) v := by
  have heq : F =ᶠ[𝓝 z] fun x ↦ antiLinearPart (fderiv ℝ (b z) x) := by
    filter_upwards [(hU z).mem_nhds (hcover z)] with x hx
    exact hF z x hx
  rw [heq.fderiv_eq]
  exact bh7_cousin_step4 n (b z) z (hb z z (hcover z)) v w

open scoped ContDiff in
/-- Step 6: subtracting a global solution of the conjugate-linear derivative equation
makes the local potentials holomorphic while preserving their differences.
Source: Gunning--Rossi, Chapter VIII, the Dolbeault construction for Cousin I. -/
private theorem bh7_cousin_step6 (n : ℕ)
    (U : (Fin n → ℂ) → Set (Fin n → ℂ)) (hU : ∀ p, IsOpen (U p))
    (a : (Fin n → ℂ) → (Fin n → ℂ) → (Fin n → ℂ) → ℂ)
    (b : (Fin n → ℂ) → (Fin n → ℂ) → ℂ)
    (hb : ∀ p z, z ∈ U p → ContDiffAt ℝ ∞ (b p) z)
    (he : ∀ p q z, z ∈ U p ∩ U q → a p q z = b q z - b p z)
    (u : (Fin n → ℂ) → ℂ) (hu : Differentiable ℝ u)
    (hdu : ∀ p z, z ∈ U p →
      antiLinearPart (fderiv ℝ u z) = antiLinearPart (fderiv ℝ (b p) z)) :
    (∀ p, AnalyticOnNhd ℂ (fun z ↦ b p z - u z) (U p)) ∧
    (∀ p q z, z ∈ U p ∩ U q →
      a p q z = (b q z - u z) - (b p z - u z)) := by
  constructor
  · intro p
    apply AnalyticDivisorAlgebraic2.spec_analyticOnNhd_of_differentiableOn_fin (hU p)
    intro z hz
    have hbp := (hb p z hz).differentiableAt (by simp)
    have hreal := hbp.sub (hu z)
    have hz0 : antiLinearPart (fderiv ℝ (fun x ↦ b p x - u x) z) = 0 := by
      rw [fderiv_fun_sub hbp (hu z), map_sub, hdu p z hz, sub_self]
    obtain ⟨L, hL⟩ := exists_restrictScalars_eq_of_antiLinearPart_eq_zero _ hz0
    exact (hasFDerivAt_of_restrictScalars ℝ hreal.hasFDerivAt hL).differentiableAt.differentiableWithinAt
  · intro p q z hz
    rw [he p q z hz]
    ring

open scoped ContDiff in
/-- Step 7: a scalar Wirtinger primitive gives a primitive of a conjugate-linear form on ℂ¹.
Source: Hörmander, An Introduction to Complex Analysis in Several Variables, §1.1. -/
private theorem bh7_cousin_step7
    (F : (Fin 1 → ℂ) → ((Fin 1 → ℂ) →L[ℝ] ℂ))
    (hFa : ∀ z, antiLinearPart (F z) = F z)
    (u : ℂ → ℂ) (hu : Differentiable ℝ u)
    (hdu : ∀ z, wirtingerDbar u z = F (fun _ ↦ z) (fun _ ↦ 1)) :
    ∀ z, antiLinearPart (fderiv ℝ (fun x : Fin 1 → ℂ ↦ u (x 0)) z) = F z := by
  intro z
  let π : (Fin 1 → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj 0
  have hd : fderiv ℝ (fun x : Fin 1 → ℂ ↦ u (x 0)) z =
      fderiv ℝ u (z 0) ∘L π.restrictScalars ℝ := by
    exact ((hu (z 0)).hasFDerivAt.comp z
      (π.restrictScalars ℝ).hasFDerivAt).fderiv
  rw [hd, antiLinearPart_comp_clm]
  ext v
  rw [apply_eq_of_antiLinearPart_eq (hFa z) v, ContinuousLinearMap.comp_apply]
  change antiLinearPart (fderiv ℝ u (z 0)) (v 0) = _
  have hv : v 0 = v 0 • (1 : ℂ) := by simp only [smul_eq_mul, mul_one]
  conv_lhs => rw [hv, apply_smul_of_antiLinearPart_eq (antiLinearPart_antiLinearPart _)]
  have hz : (fun _ : Fin 1 ↦ z 0) = z := by
    funext i
    exact congrArg z (Subsingleton.elim _ _)
  change starRingEnd ℂ (v 0) * wirtingerDbar u (z 0) = _
  rw [hdu, hz]

open scoped ContDiff in
/-- Step 8: the Cauchy transform solves the form equation on ℂ¹ for compactly supported
coefficients.
Source: Hörmander, An Introduction to Complex Analysis in Several Variables, Theorem 1.2.2. -/
private theorem bh7_cousin_step8
    (F : (Fin 1 → ℂ) → ((Fin 1 → ℂ) →L[ℝ] ℂ))
    (hF : ContDiff ℝ ∞ F)
    (hFa : ∀ z, antiLinearPart (F z) = F z)
    (hc : HasCompactSupport (fun z : ℂ ↦ F (fun _ ↦ z) (fun _ ↦ 1))) :
    ∃ u : (Fin 1 → ℂ) → ℂ, ContDiff ℝ ∞ u ∧
      ∀ z, antiLinearPart (fderiv ℝ u z) = F z := by
  let g : ℂ → ℂ := fun z ↦ F (fun _ ↦ z) (fun _ ↦ 1)
  have hg : ContDiff ℝ ∞ g :=
    (hF.comp (contDiff_pi.mpr (fun _ ↦ contDiff_id))).clm_apply contDiff_const
  have hu : ContDiff ℝ ∞ (cauchyTransform g) :=
    spec_contDiff_cauchyTransform (n := ⊤) hg hc
  refine ⟨fun x ↦ cauchyTransform g (x 0),
    hu.comp (contDiff_apply ℝ ℂ (0 : Fin 1)), ?_⟩
  exact bh7_cousin_step7 F hFa (cauchyTransform g) (hu.differentiable (by simp))
    (spec_wirtingerDbar_cauchyTransform (hg.of_le (by simp)) hc)
open scoped ContDiff in
/-- Step 9: cutting off the coefficient gives a smooth primitive on any closed disc in ℂ¹.
Source: Hörmander, An Introduction to Complex Analysis in Several Variables, Theorem 1.2.2. -/
private theorem bh7_cousin_step9
    (F : (Fin 1 → ℂ) → ((Fin 1 → ℂ) →L[ℝ] ℂ))
    (hF : ContDiff ℝ ∞ F)
    (hFa : ∀ z, antiLinearPart (F z) = F z)
    (R : ℝ) (hR : 0 < R) :
    ∃ u : (Fin 1 → ℂ) → ℂ, ContDiff ℝ ∞ u ∧
      ∀ z, ‖z 0‖ ≤ R → antiLinearPart (fderiv ℝ u z) = F z := by
  let χ : ContDiffBump (0 : ℂ) := ⟨R, R + 1, hR, by linarith⟩
  let G : (Fin 1 → ℂ) → ((Fin 1 → ℂ) →L[ℝ] ℂ) :=
    fun z ↦ χ (z 0) • F z
  have hG : ContDiff ℝ ∞ G :=
    (χ.contDiff.comp (contDiff_apply ℝ ℂ (0 : Fin 1))).smul hF
  have hGa : ∀ z, antiLinearPart (G z) = G z := by
    intro z
    dsimp only [G]
    rw [map_smul, hFa]
  have hGc : HasCompactSupport (fun z : ℂ ↦ G (fun _ ↦ z) (fun _ ↦ 1)) := by
    exact χ.hasCompactSupport.smul_right
  obtain ⟨u, hu, hdu⟩ := bh7_cousin_step8 G hG hGa hGc
  refine ⟨u, hu, ?_⟩
  intro z hz
  rw [hdu]
  change χ (z 0) • F z = F z
  rw [χ.one_of_mem_closedBall (by simpa only [Metric.mem_closedBall, dist_zero_right] using hz),
    one_smul]

open scoped NNReal in
/-- Step 10: Taylor polynomials approximate a holomorphic function on a smaller disc.
Source: Hörmander, An Introduction to Complex Analysis in Several Variables, §1.2. -/
private theorem bh7_cousin_step10 (f : ℂ → ℂ) (r R : ℝ≥0) (hrR : r < R)
    (hf : DifferentiableOn ℂ f (Metric.closedBall 0 R))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p : ℂ → ℂ, Differentiable ℂ p ∧
      ∀ z, ‖z‖ < r → ‖f z - p z‖ < ε := by
  have hR : 0 < R := lt_of_le_of_lt (show 0 ≤ r from bot_le) hrR
  have hs := hf.hasFPowerSeriesOnBall hR
  have ht := hs.tendstoUniformlyOn (r' := r) (by exact_mod_cast hrR)
  obtain ⟨N, hN⟩ := (Metric.tendstoUniformlyOn_iff.mp ht ε hε).exists
  refine ⟨(cauchyPowerSeries f 0 R).partialSum N, ?_, ?_⟩
  · unfold FormalMultilinearSeries.partialSum
    apply Differentiable.fun_sum
    intro k hk
    simp only [cauchyPowerSeries, ContinuousMultilinearMap.mkPiRing_apply, Fin.prod_const]
    fun_prop
  · intro z hz
    simpa only [zero_add, dist_eq_norm] using
      hN z (by simpa only [Metric.mem_ball, dist_zero_right] using hz)

/-- Step 11: equal conjugate derivatives imply that the difference is holomorphic.
Source: Hörmander, An Introduction to Complex Analysis in Several Variables, §1.1. -/
private theorem bh7_cousin_step11 (u v : ℂ → ℂ) (s : Set ℂ)
    (hu : Differentiable ℝ u) (hv : Differentiable ℝ v)
    (he : ∀ z ∈ s, wirtingerDbar u z = wirtingerDbar v z) :
    DifferentiableOn ℂ (fun z ↦ u z - v z) s := by
  intro z hz
  have hd := (hu z).sub (hv z)
  have he0 : antiLinearPart (fderiv ℝ (fun z ↦ u z - v z) z) 1 = 0 := by
    rw [fderiv_fun_sub (hu z) (hv z), map_sub, ContinuousLinearMap.sub_apply]
    exact sub_eq_zero.mpr (he z hz)
  have hzero : antiLinearPart (fderiv ℝ (fun z ↦ u z - v z) z) = 0 := by
    ext w
    have hw : w = w • (1 : ℂ) := by simp only [smul_eq_mul, mul_one]
    conv_lhs => rw [hw, apply_smul_of_antiLinearPart_eq (antiLinearPart_antiLinearPart _)]
    rw [he0, mul_zero, ContinuousLinearMap.zero_apply]
  obtain ⟨L, hL⟩ := exists_restrictScalars_eq_of_antiLinearPart_eq_zero _ hzero
  exact (hasFDerivAt_of_restrictScalars ℝ hd.hasFDerivAt hL).differentiableAt.differentiableWithinAt

open scoped NNReal in
/-- Step 12: an entire correction makes two primitives close on a smaller disc.
Source: Hörmander, An Introduction to Complex Analysis in Several Variables, §1.4,
exhaustion by discs and polynomial approximation. -/
private theorem bh7_cousin_step12 (u v : ℂ → ℂ) (r R : ℝ≥0) (hrR : r < R)
    (hu : Differentiable ℝ u) (hv : Differentiable ℝ v)
    (he : ∀ z ∈ Metric.closedBall (0 : ℂ) R,
      wirtingerDbar v z = wirtingerDbar u z)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ w : ℂ → ℂ, Differentiable ℝ w ∧
      (∀ z, wirtingerDbar w z = wirtingerDbar v z) ∧
      (∀ z, ‖z‖ < r → ‖w z - u z‖ < ε) := by
  obtain ⟨p, hp, happrox⟩ := bh7_cousin_step10 (fun z ↦ v z - u z) r R hrR
    (bh7_cousin_step11 v u _ hv hu he) ε hε
  have hpr : Differentiable ℝ p := hp.restrictScalars ℝ
  refine ⟨fun z ↦ v z - p z, hv.sub hpr, ?_, ?_⟩
  · intro z
    unfold wirtingerDbar
    rw [fderiv_fun_sub (hv z) (hpr z), map_sub,
      (hp z).fderiv_restrictScalars ℝ, antiLinearPart_restrictScalars,
      sub_zero]
  · intro z hz
    convert happrox z hz using 2 <;> ring

open scoped ContDiff in
/-- Step 13: arbitrary smooth scalar data have primitives on each closed disc.
Source: Hörmander, An Introduction to Complex Analysis in Several Variables, Theorem 1.2.2. -/
private theorem bh7_cousin_step13 (g : ℂ → ℂ) (hg : ContDiff ℝ ∞ g)
    (R : ℝ) (hR : 0 < R) :
    ∃ u : ℂ → ℂ, Differentiable ℝ u ∧
      ∀ z, ‖z‖ ≤ R → wirtingerDbar u z = g z := by
  let χ : ContDiffBump (0 : ℂ) := ⟨R, R + 1, hR, by linarith⟩
  let f : ℂ → ℂ := fun z ↦ χ z • g z
  have hf : ContDiff ℝ ∞ f := χ.contDiff.smul hg
  have hc : HasCompactSupport f := χ.hasCompactSupport.smul_right
  refine ⟨cauchyTransform f,
    (spec_contDiff_cauchyTransform (n := ⊤) hf hc).differentiable (by simp), ?_⟩
  intro z hz
  rw [spec_wirtingerDbar_cauchyTransform (hf.of_le (by simp)) hc]
  change χ z • g z = g z
  rw [χ.one_of_mem_closedBall (by simpa only [Metric.mem_closedBall, dist_zero_right] using hz),
    one_smul]

open scoped ContDiff NNReal in
/-- Step 14: choose primitives on an exhaustion with geometrically small successive differences.
Source: Hörmander, An Introduction to Complex Analysis in Several Variables, §1.4. -/
private theorem bh7_cousin_step14 (g : ℂ → ℂ) (hg : ContDiff ℝ ∞ g) :
    ∃ u : ℕ → ℂ → ℂ,
      (∀ n, Differentiable ℝ (u n)) ∧
      (∀ (n : ℕ) z, ‖z‖ ≤ (n : ℝ) + 2 → wirtingerDbar (u n) z = g z) ∧
      (∀ (n : ℕ) z, ‖z‖ < (n : ℝ) + 1 → ‖u (n + 1) z - u n z‖ < (1 / 2 : ℝ) ^ n) := by
  have hs (n : ℕ) (u : ℂ → ℂ) (hu : Differentiable ℝ u)
      (he : ∀ z, ‖z‖ ≤ (n : ℝ) + 2 → wirtingerDbar u z = g z) :
      ∃ v : ℂ → ℂ, Differentiable ℝ v ∧
        (∀ z, ‖z‖ ≤ ((n + 1 : ℕ) : ℝ) + 2 → wirtingerDbar v z = g z) ∧
        (∀ z, ‖z‖ < (n : ℝ) + 1 → ‖v z - u z‖ < (1 / 2 : ℝ) ^ n) := by
    obtain ⟨v, hv, he'⟩ := bh7_cousin_step13 g hg ((n : ℝ) + 3) (by positivity)
    obtain ⟨w, hw, hwe, hclose⟩ := bh7_cousin_step12 u v
      ⟨(n : ℝ) + 1, by positivity⟩ ⟨(n : ℝ) + 2, by positivity⟩
      (by change (n : ℝ) + 1 < (n : ℝ) + 2; linarith) hu hv
      (by
        intro z hz
        have hz' : ‖z‖ ≤ (n : ℝ) + 2 := by
          rw [Metric.mem_closedBall, dist_zero_right] at hz
          exact hz
        rw [he' z (by linarith), he z hz'])
      ((1 / 2 : ℝ) ^ n) (by positivity)
    refine ⟨w, hw, ?_, hclose⟩
    intro z hz
    rw [hwe, he' z (by push_cast at hz; linarith)]
  choose v hv he hc using hs
  obtain ⟨u₀, hu₀, he₀⟩ := bh7_cousin_step13 g hg 2 (by norm_num)
  let u : (n : ℕ) → {f : ℂ → ℂ // Differentiable ℝ f ∧
      ∀ z, ‖z‖ ≤ (n : ℝ) + 2 → wirtingerDbar f z = g z} :=
    Nat.rec ⟨u₀, hu₀, by simpa only [Nat.cast_zero, zero_add] using he₀⟩
      (fun n f ↦ ⟨v n f.1 f.2.1 f.2.2, hv n f.1 f.2.1 f.2.2,
        he n f.1 f.2.1 f.2.2⟩)
  exact ⟨fun n ↦ (u n).1, fun n ↦ (u n).2.1, fun n ↦ (u n).2.2,
    fun n ↦ hc n (u n).1 (u n).2.1 (u n).2.2⟩

/-- Step 15: the controlled exhaustion converges to a global scalar primitive.
Source: Hörmander, An Introduction to Complex Analysis in Several Variables, §1.4. -/
private theorem bh7_cousin_step15 (g : ℂ → ℂ) (u : ℕ → ℂ → ℂ)
    (hu : ∀ n, Differentiable ℝ (u n))
    (he : ∀ (n : ℕ) z, ‖z‖ ≤ (n : ℝ) + 2 → wirtingerDbar (u n) z = g z)
    (hc : ∀ (n : ℕ) z, ‖z‖ < (n : ℝ) + 1 →
      ‖u (n + 1) z - u n z‖ < (1 / 2 : ℝ) ^ n) :
    ∃ v : ℂ → ℂ, Differentiable ℝ v ∧ ∀ z, wirtingerDbar v z = g z := by
  let d : ℕ → ℂ → ℂ := fun k z ↦ u (k + 1) z - u k z
  have hgeom : Summable (fun k : ℕ ↦ (1 / 2 : ℝ) ^ k) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hb (N k : ℕ) (z : ℂ) (hz : ‖z‖ < (N : ℝ) + 1) :
      ‖d (k + N) z‖ ≤ (1 / 2 : ℝ) ^ k := by
    have hh := (hc (k + N) z (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) k])).le
    apply hh.trans
    rw [pow_add]
    exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ (by norm_num) (by norm_num))
  have hsum (z : ℂ) : Summable (fun k ↦ d k z) := by
    obtain ⟨N, hN⟩ := exists_nat_gt ‖z‖
    exact (summable_nat_add_iff N).mp
      (hgeom.of_norm_bounded (fun k ↦ hb N k z (by linarith)))
  let v : ℂ → ℂ := fun z ↦ u 0 z + ∑' k, d k z
  have hv (N : ℕ) : v = fun z ↦ u N z + ∑' k, d (k + N) z := by
    funext z
    dsimp only [v]
    rw [← (hsum z).sum_add_tsum_nat_add N]
    have ht : ∑ k ∈ Finset.range N, d k z = u N z - u 0 z :=
      Finset.sum_range_sub (fun k ↦ u k z) N
    rw [ht]
    ring
  have hlocal (z : ℂ) : DifferentiableAt ℝ v z ∧ wirtingerDbar v z = g z := by
    obtain ⟨N, hN⟩ := exists_nat_gt ‖z‖
    have hz : z ∈ Metric.ball (0 : ℂ) ((N : ℝ) + 1) := by
      simpa only [Metric.mem_ball, dist_zero_right] using (show ‖z‖ < (N : ℝ) + 1 by linarith)
    have ht : DifferentiableOn ℂ (fun w ↦ ∑' k, d (k + N) w)
        (Metric.ball 0 ((N : ℝ) + 1)) := by
      refine Complex.differentiableOn_tsum_of_summable_norm hgeom ?_ Metric.isOpen_ball ?_
      · intro k
        apply bh7_cousin_step11 _ _ _ (hu (k + N + 1)) (hu (k + N))
        intro w hw
        have hw' : ‖w‖ < (N : ℝ) + 1 := by
          simpa only [Metric.mem_ball, dist_zero_right] using hw
        rw [he _ w (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) k]),
          he _ w (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) k])]
      · intro k w hw
        exact hb N k w (by simpa only [Metric.mem_ball, dist_zero_right] using hw)
    have htz := ht.differentiableAt (Metric.isOpen_ball.mem_nhds hz)
    have htr := htz.restrictScalars ℝ
    rw [hv N]
    refine ⟨(hu N z).add htr, ?_⟩
    unfold wirtingerDbar
    rw [fderiv_fun_add (hu N z) htr, map_add, htz.fderiv_restrictScalars ℝ,
      antiLinearPart_restrictScalars, add_zero]
    exact he N z (by linarith)
  exact ⟨v, fun z ↦ (hlocal z).1, fun z ↦ (hlocal z).2⟩

/-- Additive holomorphic cocycles on affine complex space are coboundaries.
Source: Gunning--Rossi, Chapter VIII, Cartan theorem B and the first Cousin problem. -/
theorem bh7_cousin_additive_aux (n : ℕ)
    (U : (Fin n → ℂ) → Set (Fin n → ℂ))
    (hU : ∀ p, IsOpen (U p)) (hcover : ∀ p, p ∈ U p)
    (a : (Fin n → ℂ) → (Fin n → ℂ) → (Fin n → ℂ) → ℂ)
    (ha : ∀ p q, AnalyticOnNhd ℂ (a p q) (U p ∩ U q))
    (hdiag : ∀ p z, z ∈ U p → a p p z = 0)
    (hcocycle : ∀ p q r z, z ∈ U p ∩ U q ∩ U r → a p q z + a q r z = a p r z) :
    ∃ b : (Fin n → ℂ) → (Fin n → ℂ) → ℂ,
      (∀ p, AnalyticOnNhd ℂ (b p) (U p)) ∧
      (∀ p q z, z ∈ U p ∩ U q → a p q z = b q z - b p z) := by
  exact dbar_cousin_additive n U hU hcover a ha hdiag hcocycle

/-- A nonvanishing analytic germ has a local analytic logarithm.
Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, I.C,
the local logarithm theorem. -/
theorem bh7_local_analytic_log {n : ℕ} {f : (Fin n → ℂ) → ℂ} {x : Fin n → ℂ}
    (hf : AnalyticAt ℂ f x) (hne : f x ≠ 0) :
    ∃ g : (Fin n → ℂ) → ℂ, AnalyticAt ℂ g x ∧
      ∀ᶠ z in 𝓝 x, Complex.exp (g z) = f z := by
  let t : (Fin n → ℂ) → ℂ := fun z ↦ f z / f x
  let g : (Fin n → ℂ) → ℂ := fun z ↦ Complex.log (t z) + Complex.log (f x)
  have ht : AnalyticAt ℂ t x := hf.div_const
  have htx : t x = 1 := by simp [t, hne]
  have hlog : AnalyticAt ℂ Complex.log 1 := by
    apply DifferentiableOn.analyticAt (s := Complex.slitPlane)
    · intro z hz
      exact (Complex.differentiableAt_log hz).differentiableWithinAt
    · exact Complex.isOpen_slitPlane.mem_nhds Complex.one_mem_slitPlane
  have hg : AnalyticAt ℂ g x := (hlog.comp_of_eq ht htx).add analyticAt_const
  refine ⟨g, hg, ?_⟩
  have ht_ne : ∀ᶠ z in nhds x, t z ≠ 0 :=
    ht.continuousAt.eventually_ne (by rw [htx]; exact one_ne_zero)
  filter_upwards [ht_ne] with z hz
  rw [show Complex.exp (g z) = Complex.exp (Complex.log (t z)) *
      Complex.exp (Complex.log (f x)) by simp only [g, Complex.exp_add]]
  rw [Complex.exp_log hz, Complex.exp_log hne]
  exact div_mul_cancel₀ (f z) hne

/-- A multiplicative cocycle has an additive logarithmic lift after refinement.
The integral obstruction vanishes on contractible affine space; no additive potential is returned.
Source: Gunning--Rossi, Chapter VIII, exponential sequence and Cousin II. -/
theorem bh7_exponential_trivialization_aux (n : ℕ)
    (U : (Fin n → ℂ) → Set (Fin n → ℂ))
    (hU : ∀ p, IsOpen (U p)) (hcover : ∀ p, p ∈ U p)
    (u : (Fin n → ℂ) → (Fin n → ℂ) → (Fin n → ℂ) → ℂ)
    (hu : ∀ p q, AnalyticOnNhd ℂ (u p q) (U p ∩ U q))
    (hun : ∀ p q z, z ∈ U p ∩ U q → u p q z ≠ 0)
    (hdiag : ∀ p z, z ∈ U p → u p p z = 1)
    (hcocycle : ∀ p q r z, z ∈ U p ∩ U q ∩ U r → u p q z * u q r z = u p r z) :
    ∃ (V : (Fin n → ℂ) → Set (Fin n → ℂ)) (r : (Fin n → ℂ) → (Fin n → ℂ))
      (a : (Fin n → ℂ) → (Fin n → ℂ) → (Fin n → ℂ) → ℂ),
      (∀ p, IsOpen (V p)) ∧ (∀ p, p ∈ V p) ∧ (∀ p, V p ⊆ U (r p)) ∧
      (∀ p q, AnalyticOnNhd ℂ (a p q) (V p ∩ V q)) ∧
      (∀ p z, z ∈ V p → a p p z = 0) ∧
      (∀ p q t z, z ∈ V p ∩ V q ∩ V t → a p q z + a q t z = a p t z) ∧
      (∀ p q z, z ∈ V p ∩ V q → Complex.exp (a p q z) = u (r p) (r q) z) := by
  exact cech_exponential_trivialization n U hU hcover u hu hun hdiag hcocycle

/-- Logarithmic lifting, additive Cousin and descent give the stage-five trivialization.
Source: Gunning--Rossi, Chapter VIII, Cousin II. -/
theorem bh7_cousin_trivialization_aux (n : ℕ)
    (U : (Fin n → ℂ) → Set (Fin n → ℂ))
    (hU : ∀ p, IsOpen (U p)) (hcover : ∀ p, p ∈ U p)
    (u : (Fin n → ℂ) → (Fin n → ℂ) → (Fin n → ℂ) → ℂ)
    (hu : ∀ p q, AnalyticOnNhd ℂ (u p q) (U p ∩ U q))
    (hun : ∀ p q z, z ∈ U p ∩ U q → u p q z ≠ 0)
    (hdiag : ∀ p z, z ∈ U p → u p p z = 1)
    (hcocycle : ∀ p q r z, z ∈ U p ∩ U q ∩ U r → u p q z * u q r z = u p r z) :
    ∃ v : (Fin n → ℂ) → (Fin n → ℂ) → ℂ,
      (∀ p, AnalyticOnNhd ℂ (v p) (U p)) ∧
      (∀ p z, z ∈ U p → v p z ≠ 0) ∧
      (∀ p q z, z ∈ U p ∩ U q → v p z * u p q z = v q z) := by
  classical
  obtain ⟨V, r, a, hV, hcV, hsub, ha, had, hac, hea⟩ :=
    bh7_exponential_trivialization_aux n U hU hcover u hu hun hdiag hcocycle
  obtain ⟨b, hb, heb⟩ := bh7_cousin_additive_aux n V hV hcV a ha had hac
  have hmul : ∀ p q z, z ∈ V p ∩ V q →
      Complex.exp (b p z) * u (r p) (r q) z = Complex.exp (b q z) := by
    intro p q z hz
    rw [← hea p q z hz, heb p q z hz, ← Complex.exp_add]
    congr 1
    ring
  let v : (Fin n → ℂ) → (Fin n → ℂ) → ℂ :=
    fun p z ↦ Complex.exp (b z z) * u (r z) p z
  have hlocal : ∀ p q z, z ∈ U p → z ∈ V q →
      v p z = Complex.exp (b q z) * u (r q) p z := by
    intro p q z hp hq
    dsimp [v]
    rw [← hmul q z z ⟨hq, hcV z⟩, mul_assoc,
      hcocycle (r q) (r z) p z ⟨⟨hsub q hq, hsub z (hcV z)⟩, hp⟩]
  refine ⟨v, ?_, ?_, ?_⟩
  · intro p z hz
    have heq : v p =ᶠ[𝓝 z] fun w ↦ Complex.exp (b z w) * u (r z) p w := by
      filter_upwards [(hU p).mem_nhds hz, (hV z).mem_nhds (hcV z)] with w hp hw
      exact hlocal p z w hp hw
    exact (((hb z z (hcV z)).cexp).mul
      (hu (r z) p z ⟨hsub z (hcV z), hz⟩)).congr heq.symm
  · intro p z hz
    exact mul_ne_zero (Complex.exp_ne_zero _) (hun (r z) p z ⟨hsub z (hcV z), hz⟩)
  · intro p q z hz
    dsimp [v]
    rw [mul_assoc, hcocycle (r z) p q z ⟨⟨hsub z (hcV z), hz.1⟩, hz.2⟩]

/-- The analytic-stratification endpoint supplies the stage-five countable chart interface.
Source: Gunning--Rossi, Chapter III. -/
theorem bh7_analytic_stratification_aux (n : ℕ) (hn : 0 < n)
    (Z : Set (Fin n → ℂ)) (hZ : IsClosedAnalytic (Fin n → ℂ) Z) (hp : Z ≠ univ) :
    ∃ (d : ℕ → ℕ) (U : ∀ j, Set (Fin (d j) → ℂ))
      (f : ∀ j, (Fin (d j) → ℂ) → (Fin n → ℂ)),
      (∀ j, d j < n) ∧ (∀ j, IsOpen (U j)) ∧
      (∀ j, DifferentiableOn ℂ (f j) (U j)) ∧ Z = ⋃ j, f j '' U j := by
  exact astrat_analytic_stratification n hn Z hZ hp

end HodgeLean.Adapters
