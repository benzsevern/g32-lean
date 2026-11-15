import HodgeLean.Foundations.Curves.AbelTheorem.WeightedCutoffStokes
import HodgeLean.Foundations.Curves.AbelTheorem.RadialCutoffNeighborhoods
import HodgeLean.Foundations.Curves.AbelTheorem.FormsLocalization

noncomputable section
open HodgeLean.Foundations.Program
open Set Filter Manifold ContinuousAlternatingMap MeasureTheory Metric
open scoped Topology ContDiff BigOperators
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C] [T2Space C] [CompactSpace C]
  [MeasurableSpace E] [BorelSpace E]
attribute [local instance] b3Forms_isManifold_real

theorem weighted_residue_stokes_of_constant_germs (hE : Module.finrank ℂ E = 1)
    (w : b4c_MeroForm E C hE) (g : C → ℝ)
    (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g)
    (hconstant : ∀ x, meromorphicOrderAt (HurwitzPrymRR_loc hE w x) 0 < 0 →
      g =ᶠ[𝓝 x] fun _ => g x) (P : ℂ →L[ℝ] ℝ) :
    b3Forms_integral (b4c_residue_basis hE)
      (b3Forms_wedgeForm (b3Forms_d (b3Forms_fun (E := E) g))
        (b4c_residue_realForm hE (b4c_residue_normalizedForm hE w) P)) =
      -∑ x ∈ (b4c_residue_poles_finite hE w).toFinset,
        g x * P (2 * (Real.pi : ℂ) * Complex.I * b4c_res (hE := hE) w x) := by
  classical
  let s := (b4c_residue_poles_finite hE w).toFinset
  let U : C → Set C := fun x => if x ∈ s then interior {y | g y = g x} else Set.univ
  have hU : ∀ x, U x ∈ 𝓝 x := by
    intro x
    by_cases hx : x ∈ s
    · have hc := hconstant x ((b4c_residue_poles_finite hE w).mem_toFinset.mp hx)
      have he : {y | g y = g x} ∈ 𝓝 x := hc
      simpa only [U, if_pos hx] using interior_mem_nhds.mpr he
    · simp only [U, if_neg hx, Filter.univ_mem]
  choose R hR hA hlocal using fun x : C ↦ b4c_residue_local_data hE w x
  obtain ⟨a, b, hab, hχ, hχc, hχU, hχchart, hχone, hd, hball⟩ :=
    radial_cutoffs_in_neighborhoods hE (s : Set C) s.finite_toSet U hU R hR
  let χ : C → C → ℝ := fun x ↦ b4c_residue_chartFunction hE x
    (fun z ↦ b4c_residue_profile (a x) (b x) ‖z‖)
  let ψ : C → C → ℝ := fun x ↦ b4c_residue_chartFunction hE x
    (fun z ↦ b4c_residue_profile (a x / 2) (a x) ‖z‖)
  let μ : C → ℝ := fun y ↦ 1 - ∑ i ∈ s, ψ i y
  have hψ : ∀ i ∈ s, ContMDiff (modelWithCornersSelf ℝ E)
      (modelWithCornersSelf ℝ ℝ) ∞ (ψ i) := by
    intro i hi
    apply b4c_residue_chartFunction_smooth hE i
    · exact b4c_residue_profile_radial_smooth (by positivity [ (hab i).1 ])
        (by linarith [(hab i).1])
    · exact b4c_residue_profile_radial_compact (by linarith [(hab i).1])
    · intro z hz
      apply hball i z
      have hzle : ‖z‖ ≤ a i := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using
          b4c_residue_profile_radial_support (by linarith [(hab i).1]) hz
      exact hzle.trans (hab i).2.1.le
  have hψone : ∀ i ∈ s, ψ i =ᶠ[nhds i] fun _ ↦ (1 : ℝ) := by
    intro i hi
    exact b4c_residue_chartFunction_one hE i _
      (b4c_residue_profile_radial_one (by positivity [ (hab i).1 ])
        (by linarith [(hab i).1]))
  have hone : ∀ i ∈ s, ∀ y ∈ tsupport (ψ i), χ i y = 1 := by
    intro i hi
    exact b4c_residue_nested_cutoffs hE i (hab i).1 (hab i).2.1 (hball i)
  have hsub : ∀ i ∈ s, tsupport (ψ i) ⊆ tsupport (χ i) := by
    intro i hi y hy
    exact subset_tsupport _ (by simp [hone i hi y hy])
  have hψd : (s : Set C).PairwiseDisjoint (fun i ↦ tsupport (ψ i)) := by
    intro i hi j hj hij
    exact (hd hi hj hij).mono (hsub i hi) (hsub j hj)
  have hμ : ContMDiff (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ ℝ) ∞ μ :=
    contMDiff_const.sub (ContMDiff.sum hψ)
  have hpoles : ∀ x, meromorphicOrderAt (HurwitzPrymRR_loc hE w x) 0 < 0 →
      μ =ᶠ[nhds x] 0 := by
    intro x hx
    apply b4c_residue_cutoff_vanishes s ψ hψone hψd
    exact (b4c_residue_poles_finite hE w).mem_toFinset.mpr hx
  have hgc : ∀ i ∈ s, ∀ y ∈ tsupport (χ i), g =ᶠ[𝓝 y] fun _ => g i := by
    intro i hi y hy
    have hu := hχU i hy
    change y ∈ U i at hu
    simp only [U, if_pos hi] at hu
    exact mem_interior_iff_mem_nhds.mp hu
  have hform : b3Forms_wedgeForm (b3Forms_d (b3Forms_fun (E := E) g))
      (b4c_residue_realForm hE (b4c_residue_normalizedForm hE w) P) =
      b3Forms_wedgeForm (b3Forms_d (b3Forms_fun (E := E) g))
        (b4c_residue_realForm hE
          (fun v => (μ v.proj : ℂ) * b4c_residue_normalizedForm hE w v) P) := by
    funext y
    by_cases hy : ∃ i ∈ s, y ∈ tsupport (ψ i)
    · obtain ⟨i, hi, hy⟩ := hy
      have hz := real_differential_zero_of_constant_germ (E := E) g y (g i) (hgc i hi y (hsub i hi hy))
      ext v
      simp only [b3Forms_wedgeForm, hz, b3Forms_wedge_apply,
        ContinuousAlternatingMap.coe_zero, Pi.zero_apply, zero_mul, sub_self]
    · have hzero : ∀ i ∈ s, ψ i y = 0 := by
        intro i hi
        apply image_eq_zero_of_notMem_tsupport
        exact fun hz => hy ⟨i, hi, hz⟩
      have hm : μ y = 1 := by simp only [μ, Finset.sum_eq_zero hzero, sub_zero]
      simp only [b3Forms_wedgeForm, b4c_residue_realForm, hm, Complex.ofReal_one, one_mul]
  rw [hform]
  have he := weighted_cutoff_stokes hE w s χ ψ (fun i _ => hχ i) hψ
    (fun i _ => hχchart i) hd hone hpoles g hg g
    (fun i hi y hy => (hgc i hi y hy).self_of_nhds) P
  rw [he]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  have ha2 : 0 < a i / 2 := div_pos (hab i).1 (by norm_num)
  have haa : a i / 2 < a i := by linarith [(hab i).1]
  have haR : a i < R i := (hab i).2.1.trans (hab i).2.2
  have hLi := hlocal i (a i / 2) (a i) ha2 haa haR
  simp_rw [b4c_residue_profile_density ha2 haa] at hLi
  exact b4c_residue_chartIntegral_eq hE w μ hμ hpoles i
    (hab i).1 (hab i).2.1 (hball i)
    (fun z hz => hA i z (hz.trans (hab i).2.2))
    (fun y hy => b4c_residue_multiplier_germ s χ ψ hd hone hi hy) hLi P

end HodgeLean.Foundations.Curves.AbelTheorem
