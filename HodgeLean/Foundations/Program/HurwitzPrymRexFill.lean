import HodgeLean.Foundations.Program.HurwitzPrymRexPunct

set_option maxHeartbeats 400000

/-! # Track B4, lane `b4-rex`: coordinate discs at the punctures

Around a point `b` of a Riemann surface `Y` (charts in a one-dimensional `E'`, identified with `ℂ`
by `κ'`), the chart gives a coordinate `ψ_b = κ' (φ_b - φ_b b)` with inverse `ξ_b`. For small `r`
the disc `ξ_b (B(0, r))` meets the finite set `B` only in `b`; restricted to the punctured disc it
is a `Datum` for the covering `p : U → Y ∖ B`.
HC no distance; AV milestone no distance.
-/

noncomputable section

open Topology Metric Set Complex

namespace HodgeLean.Foundations.Program

namespace HurwitzPrymRexFill

variable {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℂ E']
variable {Y : Type} [TopologicalSpace Y] [ChartedSpace E' Y]
variable (κ' : E' ≃L[ℂ] ℂ)

/-- **The disc coordinate inverse** `ξ_b z = φ_b⁻¹ (φ_b b + κ'⁻¹ z)`.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §1 (coordinate discs). -/
def ξY (b : Y) (z : ℂ) : Y := (chartAt E' b).symm (chartAt E' b b + κ'.symm z)

/-- **The disc coordinate** `ψ_b y = κ' (φ_b y - φ_b b)`.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §1. -/
def ψY (b : Y) (y : Y) : ℂ := κ' (chartAt E' b y - chartAt E' b b)

example (b : Y) : ψY κ' b b = 0 := by simp [ψY]

/-- The coordinate domain: `φ_b b + κ'⁻¹ z` lies in the chart target.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §1 (coordinate discs). -/
def Tgt (b : Y) : Set ℂ := {z | chartAt E' b b + κ'.symm z ∈ (chartAt E' b).target}

variable {κ'}

theorem isOpen_Tgt (b : Y) : IsOpen (Tgt κ' b) :=
  (chartAt E' b).open_target.preimage (continuous_const.add κ'.symm.continuous)

theorem zero_mem_Tgt (b : Y) : (0 : ℂ) ∈ Tgt κ' b := by
  simp [Tgt, (chartAt E' b).map_source (mem_chart_source E' b)]

example (b : Y) : (0 : ℂ) ∈ Tgt κ' b := zero_mem_Tgt b

theorem ξY_zero (b : Y) : ξY κ' b 0 = b := by
  simp [ξY, (chartAt E' b).left_inv (mem_chart_source E' b)]

theorem ξY_mem_source {b : Y} {z : ℂ} (hz : z ∈ Tgt κ' b) : ξY κ' b z ∈ (chartAt E' b).source :=
  (chartAt E' b).map_target hz

example (b : Y) : ξY κ' b 0 = b := ξY_zero b

theorem ψY_ξY {b : Y} {z : ℂ} (hz : z ∈ Tgt κ' b) : ψY κ' b (ξY κ' b z) = z := by
  simp [ψY, ξY, (chartAt E' b).right_inv hz]

theorem ξY_ψY {b y : Y} (hy : y ∈ (chartAt E' b).source) : ξY κ' b (ψY κ' b y) = y := by
  simp [ψY, ξY, (chartAt E' b).left_inv hy]

theorem continuousOn_ξY (b : Y) : ContinuousOn (ξY κ' b) (Tgt κ' b) :=
  (chartAt E' b).continuousOn_symm.comp (continuous_const.add κ'.symm.continuous).continuousOn
    fun _ hz ↦ hz

theorem continuousOn_ψY (b : Y) : ContinuousOn (ψY κ' b) (chartAt E' b).source :=
  κ'.continuous.comp_continuousOn ((chartAt E' b).continuousOn.sub continuousOn_const)

theorem injOn_ξY (b : Y) : InjOn (ξY κ' b) (Tgt κ' b) := fun z hz z' hz' h ↦ by
  rw [← ψY_ξY hz, h, ψY_ξY hz']

/-- The image of a coordinate disc inside the coordinate domain is open. -/
theorem image_ξY_eq {b : Y} {S : Set ℂ} (hS : S ⊆ Tgt κ' b) :
    ξY κ' b '' S = (chartAt E' b).source ∩ ψY κ' b ⁻¹' S := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨ξY_mem_source (hS hz), by rw [mem_preimage, ψY_ξY (hS hz)]; exact hz⟩
  · rintro ⟨hy, hyS⟩
    exact ⟨_, hyS, ξY_ψY hy⟩

theorem isOpen_image_ξY {b : Y} {S : Set ℂ} (hS : S ⊆ Tgt κ' b) (hSo : IsOpen S) :
    IsOpen (ξY κ' b '' S) := by
  rw [image_ξY_eq hS]
  exact (continuousOn_ψY b).isOpen_inter_preimage (chartAt E' b).open_source hSo

/-- **Small coordinate discs**: inside the coordinate domain and inside any neighborhood of `b`. -/
theorem exists_radius (b : Y) {O : Set Y} (hO : O ∈ 𝓝 b) :
    ∃ r > 0, ball (0 : ℂ) r ⊆ Tgt κ' b ∧ ∀ z ∈ ball (0 : ℂ) r, ξY κ' b z ∈ O := by
  have hc : ContinuousAt (ξY κ' b) 0 :=
    (continuousOn_ξY b).continuousAt ((isOpen_Tgt b).mem_nhds (zero_mem_Tgt b))
  have h1 : Tgt κ' b ∩ ξY κ' b ⁻¹' O ∈ 𝓝 (0 : ℂ) :=
    Filter.inter_mem ((isOpen_Tgt b).mem_nhds (zero_mem_Tgt b))
      (hc.preimage_mem_nhds (by rwa [ξY_zero]))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 h1
  exact ⟨r, hr, fun z hz ↦ (hball hz).1, fun z hz ↦ (hball hz).2⟩

/-! ## The puncture datum -/

section Datum

open HurwitzPrymRexPunct

variable {B : Set Y} {G U : Type} [Group G] [TopologicalSpace U] [MulAction G U]
variable {p : U → {y : Y // y ∉ B}}

theorem isInducing_val (B : Set Y) : Topology.IsInducing (Subtype.val : {y : Y // y ∉ B} → Y) :=
  ⟨rfl⟩

open scoped Classical in
/-- The disc map into `Y ∖ B` (junk at the centre).
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §1 (coordinate discs). -/
def ξB (κ' : E' ≃L[ℂ] ℂ) (B : Set Y) (y₀ : {y : Y // y ∉ B}) (b : Y) (z : ℂ) : {y : Y // y ∉ B} :=
  if h : ξY κ' b z ∈ B then y₀ else ⟨ξY κ' b z, h⟩

theorem ξB_val {y₀ : {y : Y // y ∉ B}} {b : Y} {z : ℂ} (h : ξY κ' b z ∉ B) :
    (ξB κ' B y₀ b z : Y) = ξY κ' b z := by
  simp [ξB, h]

variable {r : ℝ} {b : Y}

example (y₀ : {y : Y // y ∉ B}) (z : ℂ) (h : ξY κ' b z ∉ B) :
    (ξB κ' B y₀ b z : Y) = ξY κ' b z := ξB_val h

theorem ξY_not_mem (havoid : ∀ z ∈ ball (0 : ℂ) r, ξY κ' b z ∈ B → z = 0) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) r \ {0}) : ξY κ' b z ∉ B := fun h ↦ hz.2 (havoid z hz.1 h)

theorem continuousOn_ξB (y₀ : {y : Y // y ∉ B}) (hTgt : ball (0 : ℂ) r ⊆ Tgt κ' b)
    (havoid : ∀ z ∈ ball (0 : ℂ) r, ξY κ' b z ∈ B → z = 0) :
    ContinuousOn (ξB κ' B y₀ b) (ball 0 r \ {0}) := by
  rw [(isInducing_val B).continuousOn_iff]
  refine ((continuousOn_ξY b).mono fun z hz ↦ hTgt hz.1).congr fun z hz ↦ ?_
  exact ξB_val (ξY_not_mem havoid hz)

theorem image_ξB (y₀ : {y : Y // y ∉ B}) (hTgt : ball (0 : ℂ) r ⊆ Tgt κ' b)
    (havoid : ∀ z ∈ ball (0 : ℂ) r, ξY κ' b z ∈ B → z = 0) :
    ξB κ' B y₀ b '' (ball 0 r \ {0}) = Subtype.val ⁻¹' (ξY κ' b '' (ball 0 r \ {0})) := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, (ξB_val (ξY_not_mem havoid hz)).symm⟩
  · rintro ⟨z, hz, hzx⟩
    exact ⟨z, hz, Subtype.ext ((ξB_val (ξY_not_mem havoid hz)).trans hzx)⟩

/-- **The puncture datum at `b`**, from a coordinate disc of radius `r` meeting `B` only at `b`.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §8.4 (filling in the punctures of an
unbranched covering). -/
def mkDatum (hp : IsQuotientCoveringMap p G) (κ' : E' ≃L[ℂ] ℂ) (b : Y) (r : ℝ) (hr : 0 < r)
    (hTgt : ball (0 : ℂ) r ⊆ Tgt κ' b) (havoid : ∀ z ∈ ball (0 : ℂ) r, ξY κ' b z ∈ B → z = 0)
    (u₀ : U) : Datum p G :=
  let y₀ := p u₀
  let ε : C(HP (Real.log r), {y : Y // y ∉ B}) :=
    ⟨fun w ↦ ξB κ' B y₀ b (exp w),
      (continuousOn_ξB y₀ hTgt havoid).comp_continuous
        (continuous_exp.comp continuous_subtype_val) fun w ↦ by
          refine ⟨mem_ball_zero_iff.2 ?_, exp_ne_zero _⟩
          rw [norm_exp]
          calc Real.exp (w : ℂ).re < Real.exp (Real.log r) := Real.exp_lt_exp.2 w.2
            _ = r := Real.exp_log hr⟩
  have hper : ∀ w, ε (shift _ 1 w) = ε w := fun w ↦ by
    change ξB κ' B y₀ b (exp ((w : ℂ) + ((1 : ℤ) : ℂ) * (2 * Real.pi * I))) = ξB κ' B y₀ b (exp w)
    rw [Int.cast_one, one_mul, exp_add, exp_two_pi_mul_I, mul_one]
  let w₀ : HP (Real.log r) := ⟨(Real.log r - 1 : ℝ), by simp [HP]⟩
  have hsurj := hp.surjective
  let u₁ := (hsurj (ε w₀)).choose
  have hu₁ : p u₁ = ε w₀ := (hsurj (ε w₀)).choose_spec
  have hex := exists_lift ε hp hper w₀ u₁ hu₁
  { r := r
    hr := hr
    ξ := ξB κ' B y₀ b
    ψ := fun x ↦ ψY κ' b x.1
    ξ_cont := continuousOn_ξB y₀ hTgt havoid
    ψ_cont := by
      rw [image_ξB y₀ hTgt havoid]
      refine (continuousOn_ψY b).comp continuous_subtype_val.continuousOn ?_
      rintro x ⟨z, hz, hzx⟩
      rw [← hzx]
      exact ξY_mem_source (hTgt hz.1)
    ψ_ξ := fun z hz ↦ by
      change ψY κ' b (ξB κ' B y₀ b z : Y) = z
      rw [ξB_val (ξY_not_mem havoid hz), ψY_ξY (hTgt hz.1)]
    isOpen_image := by
      rw [image_ξB y₀ hTgt havoid]
      exact (isOpen_image_ξY (fun z hz ↦ hTgt hz.1) (isOpen_ball.sdiff isClosed_singleton)).preimage
        continuous_subtype_val
    L := hex.choose
    h := hex.choose_spec.choose
    lifts := fun w ↦ congrFun hex.choose_spec.choose_spec.1 w
    shift_eq := hex.choose_spec.choose_spec.2.2 }

example (hp : IsQuotientCoveringMap p G) (κ' : E' ≃L[ℂ] ℂ) (b : Y) (r : ℝ) (hr : 0 < r)
    (hTgt : ball (0 : ℂ) r ⊆ Tgt κ' b) (havoid : ∀ z ∈ ball (0 : ℂ) r, ξY κ' b z ∈ B → z = 0)
    (u₀ : U) : (mkDatum hp κ' b r hr hTgt havoid u₀).r = r := rfl

end Datum

end HurwitzPrymRexFill

end HodgeLean.Foundations.Program
