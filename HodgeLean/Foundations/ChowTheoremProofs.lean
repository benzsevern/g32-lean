import HodgeLean.Foundations.AnalyticSubset

/-! # Analytic cones: proof obligations

The first affine segment of the projective cone route.
HC no distance; AV milestone no distance.
-/

noncomputable section
namespace HodgeLean.Foundations
open Set Filter Topology

private noncomputable def diagonalPolynomial {n d : ℕ}
    (A : ContinuousMultilinearMap ℂ (fun _ : Fin d ↦ Fin n → ℂ) ℂ) :
    MvPolynomial (Fin n) ℂ :=
  ∑ r : Fin d → Fin n,
    MvPolynomial.C (A (fun j ↦ Pi.basisFun ℂ (Fin n) (r j))) *
      ∏ j, MvPolynomial.X (r j)

private theorem diagonalPolynomial_isHomogeneous {n d : ℕ}
    (A : ContinuousMultilinearMap ℂ (fun _ : Fin d ↦ Fin n → ℂ) ℂ) :
    (diagonalPolynomial A).IsHomogeneous d := by
  classical
  apply MvPolynomial.IsHomogeneous.sum
  intro r _
  apply MvPolynomial.IsHomogeneous.C_mul
  simpa using MvPolynomial.IsHomogeneous.prod Finset.univ _ _
    (fun j _ ↦ MvPolynomial.isHomogeneous_X ℂ (r j))

private theorem eval_diagonalPolynomial {n d : ℕ}
    (A : ContinuousMultilinearMap ℂ (fun _ : Fin d ↦ Fin n → ℂ) ℂ)
    (z : Fin n → ℂ) :
    MvPolynomial.eval z (diagonalPolynomial A) = A (fun _ ↦ z) := by
  classical
  simp only [diagonalPolynomial, map_sum, MvPolynomial.eval_mul, MvPolynomial.eval_C,
    MvPolynomial.eval_prod, MvPolynomial.eval_X]
  calc
    _ = A (fun j ↦ ∑ i, z i • Pi.basisFun ℂ (Fin n) i) := by
      simpa [MultilinearMap.map_smul_univ, mul_comm] using
        (A.toMultilinearMap.map_sum (fun _ i ↦ z i • Pi.basisFun ℂ (Fin n) i)).symm
    _ = A (fun _ ↦ z) := by
      congr 1
      funext j
      simpa [Pi.basisFun_repr] using (Pi.basisFun ℂ (Fin n)).sum_repr z

private theorem exists_ne_zero_of_eventually {p : ℂ → Prop} (hp : ∀ᶠ t in nhds (0 : ℂ), p t) :
    ∃ t : ℂ, t ≠ 0 ∧ p t := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hp
  let t : ℂ := (ε / 2 : ℝ)
  refine ⟨t, by simp [t, hε.ne'], hball ?_⟩
  simp only [dist_zero_right, Complex.norm_real, t]
  rw [Real.norm_of_nonneg (le_of_lt (half_pos hε))]
  exact half_lt_self hε

/-- A point outside a closed analytic cone is separated by a homogeneous polynomial.
Source: Griffiths--Harris, Principles of Algebraic Geometry, Chapter 1 §3,
proof of Chow's theorem by homogeneous Taylor terms. -/
theorem chow_cone_separation_aux (n : ℕ) (Z : Set (Fin n → ℂ))
    (hZ : IsClosedAnalytic (Fin n → ℂ) Z)
    (hscale : ∀ (t : ℂ) (z : Fin n → ℂ), z ∈ Z → t • z ∈ Z)
    (x : Fin n → ℂ) (hx : x ∉ Z) :
    ∃ (d : ℕ) (P : MvPolynomial (Fin n) ℂ), P.IsHomogeneous d ∧
      (∀ z ∈ Z, MvPolynomial.eval z P = 0) ∧ MvPolynomial.eval x P ≠ 0 := by
  classical
  by_cases hZe : Z = ∅
  · refine ⟨0, 1, MvPolynomial.isHomogeneous_one (Fin n) ℂ, ?_, ?_⟩
    · simp [hZe]
    · simp
  obtain ⟨z₀, hz₀⟩ := Set.nonempty_iff_ne_empty.2 hZe
  have h0Z : (0 : Fin n → ℂ) ∈ Z := by simpa using hscale 0 z₀ hz₀
  obtain ⟨U, hUo, h0U, -, m, f, hf, hZf⟩ := hZ.2 0 h0Z
  simp only [chartAt_self_eq, OpenPartialHomeomorph.refl_apply,
    OpenPartialHomeomorph.refl_symm, id_eq] at h0U hZf
  choose p hp using fun i ↦ hf i 0 h0U
  have hline_zero (i : Fin m) (z : Fin n → ℂ) (hz : z ∈ Z) :
      (p i).compContinuousLinearMap (ContinuousLinearMap.toSpanSingleton ℂ z) = 0 := by
    apply HasFPowerSeriesAt.eq_zero_of_eventually
    · have hp' : HasFPowerSeriesAt (f i) (p i)
          ((ContinuousLinearMap.toSpanSingleton ℂ z) 0) := by simpa using hp i
      exact hp'.compContinuousLinearMap
    have hc : Tendsto (ContinuousLinearMap.toSpanSingleton ℂ z) (nhds 0) (nhds 0) := by
      simpa using (ContinuousLinearMap.toSpanSingleton ℂ z).continuous.tendsto 0
    have hnear : ∀ᶠ t : ℂ in nhds 0, t • z ∈ U := by
      exact (hc.eventually (hUo.mem_nhds h0U)).mono fun t ht ↦ ht
    filter_upwards [hnear] with t ht
    exact (hZf _ ht).1 (hscale t z hz) i
  have hdiag_zero (i : Fin m) (d : ℕ) (z : Fin n → ℂ) (hz : z ∈ Z) :
      p i d (fun _ ↦ z) = 0 := by
    have h' := congrArg (fun q : FormalMultilinearSeries ℂ ℂ ℂ ↦
      q d (fun _ : Fin d ↦ (1 : ℂ))) (hline_zero i z hz)
    unfold FormalMultilinearSeries.coeff at h'
    simp only [FormalMultilinearSeries.compContinuousLinearMap_apply] at h'
    have heq : ((⇑(ContinuousLinearMap.toSpanSingleton ℂ z)) ∘
        (fun _ : Fin d ↦ (1 : ℂ))) = (fun _ ↦ z) := by
      funext j
      simp
    rw [heq] at h'
    simpa using h'
  have hgood : ∀ᶠ t : ℂ in nhds 0,
      t • x ∈ U ∧ ∀ i : Fin m,
        HasSum (fun d : ℕ ↦ p i d (fun _ : Fin d ↦ t • x)) (f i (t • x)) := by
    have hc : Tendsto (fun t : ℂ ↦ t • x) (nhds 0) (nhds 0) := by
      have hcont : Continuous (fun t : ℂ ↦ t • x) := by fun_prop
      have hz : (0 : ℂ) • x = (0 : Fin n → ℂ) := zero_smul ℂ x
      have hh := (hcont.continuousAt : ContinuousAt (fun t : ℂ ↦ t • x) 0).tendsto
      rw [hz] at hh
      exact hh
    have hU : ∀ᶠ t : ℂ in nhds 0, t • x ∈ U := hc.eventually (hUo.mem_nhds h0U)
    have hs : ∀ i : Fin m, ∀ᶠ t : ℂ in nhds 0,
        HasSum (fun d : ℕ ↦ p i d (fun _ : Fin d ↦ t • x)) (f i (t • x)) := by
      intro i
      filter_upwards [hc (hp i).eventually_hasSum_sub] with t ht
      change HasSum (fun d : ℕ ↦ p i d (fun _ : Fin d ↦ t • x - 0)) (f i (t • x)) at ht
      simpa only [sub_zero] using ht
    filter_upwards [hU, eventually_all.mpr hs] with t htU htS
    exact ⟨htU, htS⟩
  obtain ⟨t, ht0, htU, htSum⟩ := exists_ne_zero_of_eventually hgood
  have htx : t • x ∉ Z := by
    intro hmem
    have := hscale t⁻¹ (t • x) hmem
    exact hx (by simpa [smul_smul, ht0] using this)
  obtain ⟨i, hi⟩ : ∃ i : Fin m, f i (t • x) ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact htx ((hZf _ htU).2 hall)
  obtain ⟨d, hd⟩ : ∃ d : ℕ, p i d (fun _ : Fin d ↦ t • x) ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply hi
    apply (htSum i).unique
    simpa [hall] using (hasSum_zero : HasSum (fun _ : ℕ ↦ (0 : ℂ)) 0)
  refine ⟨d, diagonalPolynomial (p i d), diagonalPolynomial_isHomogeneous _, ?_, ?_⟩
  · intro z hz
    rw [eval_diagonalPolynomial]
    exact hdiag_zero i d z hz
  · rw [eval_diagonalPolynomial]
    intro hx0
    apply hd
    simpa [hx0] using
      ((p i d).map_smul_univ (fun _ ↦ t) (fun _ : Fin d ↦ x))

/-- A closed analytic cone has finitely many homogeneous polynomial equations.
Source: Griffiths--Harris, Principles of Algebraic Geometry, Chapter 1 §3,
proof of Chow's theorem; Hilbert's basis theorem applied to the separating polynomials. -/
theorem chow_cone_algebraic_aux (n : ℕ) (Z : Set (Fin n → ℂ))
    (hZ : IsClosedAnalytic (Fin n → ℂ) Z)
    (hscale : ∀ (t : ℂ) (z : Fin n → ℂ), z ∈ Z → t • z ∈ Z) :
    ∃ (m : ℕ) (d : Fin m → ℕ) (P : Fin m → MvPolynomial (Fin n) ℂ),
      (∀ i, (P i).IsHomogeneous (d i)) ∧
      Z = {z | ∀ i, MvPolynomial.eval z (P i) = 0} := by
  classical
  let S : Set (MvPolynomial (Fin n) ℂ) :=
    {P | ∃ d, P.IsHomogeneous d ∧ ∀ z ∈ Z, MvPolynomial.eval z P = 0}
  have hfg : (Ideal.span S).FG := IsNoetherian.noetherian (Ideal.span S)
  obtain ⟨s, hsS, hspan⟩ :=
    (Submodule.fg_span_iff_fg_span_finset_subset S).mp hfg
  let e : Fin s.card ≃ {P // P ∈ s} := s.equivFin.symm
  let P : Fin s.card → MvPolynomial (Fin n) ℂ := fun i ↦ (e i).1
  have hPS (i : Fin s.card) : P i ∈ S := hsS (e i).2
  choose d hd hvan using fun i ↦ hPS i
  refine ⟨s.card, d, P, hd, Set.Subset.antisymm ?_ ?_⟩
  · intro z hz i
    exact hvan i z hz
  · intro z hz
    by_contra hzZ
    obtain ⟨qd, q, hqhom, hqZ, hqz⟩ :=
      chow_cone_separation_aux n Z hZ hscale z hzZ
    have hqS : q ∈ S := by
      exact ⟨qd, hqhom, hqZ⟩
    have hqspan : q ∈ Ideal.span (s : Set (MvPolynomial (Fin n) ℂ)) := by
      change q ∈ Submodule.span (MvPolynomial (Fin n) ℂ)
        (s : Set (MvPolynomial (Fin n) ℂ))
      rw [← hspan]
      exact Ideal.subset_span hqS
    have hsKer : Ideal.span (s : Set (MvPolynomial (Fin n) ℂ)) ≤
        RingHom.ker (MvPolynomial.eval₂Hom (RingHom.id ℂ) z) := by
      apply Ideal.span_le.mpr
      intro p hp
      change MvPolynomial.eval z p = 0
      obtain ⟨i, hi⟩ := e.surjective ⟨p, hp⟩
      have hip : P i = p := congrArg Subtype.val hi
      rw [← hip]
      exact hz i
    exact hqz (hsKer hqspan)

end HodgeLean.Foundations
