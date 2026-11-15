import HodgeLean.Foundations.Curves.AbelTheorem.ArcSupport

noncomputable section
open HodgeLean.Foundations.Program
open Set Filter Manifold ContinuousAlternatingMap MeasureTheory Metric
open scoped Topology ContDiff ComplexConjugate
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C] [T2Space C] [CompactSpace C]
  [MeasurableSpace E] [BorelSpace E]
attribute [local instance] b3Forms_isManifold_real
variable (hE : Module.finrank ℂ E = 1) {P : ℝ → C} (K : b3Rest_Cover E P)

theorem exists_arc_dual_of_local_primitives (hP : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 P)
    (hper : Function.Periodic P 1) {D : Set C} (hDc : IsClosed D)
    (hw : ∀ k : ℤ, P (k / K.N) ∉ D) :
    ∃ ε₀ > 0, ∀ ε, 0 < ε → ε < ε₀ → ∃ κ : Fin K.N → C → E [⋀^Fin 1]→L[ℝ] ℝ,
      (∀ i : Fin K.N, b3Forms_IsSmooth (b3Rest2_arcPiece hE K ε i)) ∧
      (∀ i : Fin K.N, tsupport (b3Rest2_arcPiece hE K ε i) ⊆
        (chartAt E (K.x i)).symm '' ball (chartAt E (K.x i) (K.x i)) (K.r i)) ∧
      (∀ i, b3Forms_IsSmooth (κ i)) ∧ (∀ i, tsupport (κ i) ⊆ (chartAt E (K.x i)).symm ''
        ball (chartAt E (K.x i) (K.x i)) (K.r i)) ∧
      (∀ i, ∀ p ∈ tsupport (κ i), p ∉ D) ∧
      b3Forms_IsSmooth ((∫ z, b3Rest_rho ε z)⁻¹ •
        ∑ i : Fin K.N, (b3Rest2_arcPiece hE K ε i + κ i)) ∧
      ∀ α : C → E [⋀^Fin 1]→L[ℝ] ℝ, b3Forms_IsSmooth α →
        ∀ h' : ℤ → E → ℝ, (∀ k, ∀ u ∈ ball (chartAt E (K.x k) (K.x k)) (K.r k),
          HasFDerivAt (h' k) (b3Forms_toCLM (b3Forms_loc α (K.x k) u)) u) →
        b3Forms_integral (b3Rest_b hE) (b3Forms_wedgeForm α ((∫ z, b3Rest_rho ε z)⁻¹ •
          ∑ i : Fin K.N, (b3Rest2_arcPiece hE K ε i + κ i))) = b3Forms_lineIntegral α P 0 1 := by
  have hN : (0 : ℝ) < K.N := Nat.cast_pos.2 K.pos
  have hw1 : ∀ k : ℤ, P (k / K.N) ∈ (chartAt E (K.x (k - 1))).source ∧
      chartAt E (K.x (k - 1)) (P (k / K.N)) ∈
        ball (chartAt E (K.x (k - 1)) (K.x (k - 1))) (K.r (k - 1)) := by
    intro k
    have := K.mem (k - 1) 1 ⟨zero_le_one, le_rfl⟩
    rwa [show ((k - 1 : ℤ) : ℝ) + 1 = (k : ℝ) by push_cast; ring] at this
  set Uy : ℤ → Set E := fun k ↦ ball (chartAt E (K.x k) (K.x k)) (K.r k) ∩
    ((chartAt E (K.x k)).target ∩ (chartAt E (K.x k)).symm ⁻¹' Dᶜ)
  have hUyo : ∀ k, IsOpen (Uy k) := fun k ↦ isOpen_ball.inter
    ((chartAt E (K.x k)).continuousOn_symm.isOpen_inter_preimage
      (chartAt E (K.x k)).open_target hDc.isOpen_compl)
  have hUyt : ∀ k, Uy k ⊆ (chartAt E (K.x k)).target := fun k u hu ↦ hu.2.1
  have hwUy : ∀ k : ℤ, chartAt E (K.x k) (P (k / K.N)) ∈ Uy k := fun k ↦
    ⟨(K.mem_zero k).2, (chartAt E (K.x k)).map_source (K.mem_zero k).1, by
      show (chartAt E (K.x k)).symm (chartAt E (K.x k) (P (k / K.N))) ∉ D
      rw [(chartAt E (K.x k)).left_inv (K.mem_zero k).1]
      exact hw k⟩
  choose ε₀ hε₀ hJ using fun k : ℤ ↦ b3Rest_junction hE (x := K.x (k - 1)) (y := K.x k)
    (w := P (k / K.N)) (hw1 k).1 (K.mem_zero k).1 isOpen_ball (hUyo k) (K.ball_sub (k - 1))
    (hUyt k) (hw1 k).2 (hwUy k)
  set ca : ℤ → ℝ → ℂ := fun k ↦ b3Rest2_arcC hE (K.x k) P (k / K.N) ((k + 1) / K.N)
  set ca' : ℤ → ℝ → ℂ := fun k ↦ b3Rest2_arcC' hE (K.x k) P (k / K.N) ((k + 1) / K.N)
  have hsrc : ∀ k : ℤ, ∀ t ∈ Icc ((k : ℝ) / K.N) ((k + 1) / K.N),
      P t ∈ (chartAt E (K.x k)).source := fun k t ht ↦ (b3Rest2_cover_mem K ht).1
  have hcac : ∀ k, Continuous (ca k) := fun k ↦
    b3Rest2_continuous_arcC hE (K.x k) hP (b3Rest2_cover_le K) (hsrc k)
  have hcac' : ∀ k, Continuous (ca' k) := fun k ↦
    b3Rest2_continuous_arcC' hE (K.x k) hP (b3Rest2_cover_le K) (hsrc k)
  have hcad : ∀ k : ℤ, ∀ t ∈ Ioo ((k : ℝ) / K.N) ((k + 1) / K.N),
      HasDerivAt (ca k) (ca' k t) t := fun k t ht ↦
    b3Rest2_hasDerivAt_arcC hE (K.x k) hP (b3Rest2_cover_le K) (hsrc k) ht
  have hS : ∀ k : ℤ, ∃ δ > 0, ∀ z ∈ cthickening δ (ca k '' Icc ((k : ℝ) / K.N) ((k + 1) / K.N)),
      b3Rest_ζ hE (K.x k) z ∈ ball (chartAt E (K.x k) (K.x k)) (K.r k) := by
    intro k
    have hc : IsCompact (ca k '' Icc ((k : ℝ) / K.N) ((k + 1) / K.N)) :=
      isCompact_Icc.image (hcac k)
    obtain ⟨δ, hδ, hsub⟩ := hc.exists_cthickening_subset_open
      (isOpen_ball.preimage (b3Rest_continuous_ζ hE (K.x k))) (by
        rintro _ ⟨t, ht, rfl⟩
        rw [mem_preimage, show ca k t = b3Rest_pt hE (K.x k) (P t) from b3Rest2_arcC_of_mem hE (K.x k) ht,
          b3Rest_ζ_pt]
        exact (b3Rest2_cover_mem K ht).2)
    exact ⟨δ, hδ, fun z hz ↦ hsub hz⟩
  choose δs hδs hδseg using hS
  obtain ⟨ε₁, hε₁, hε₁lt⟩ := b3Rest_exists_pos_lt (Finset.range K.N)
    (fun i : ℕ ↦ min (ε₀ i) (δs i)) fun i _ ↦ lt_min (hε₀ i) (hδs i)
  refine ⟨ε₁, hε₁, fun ε hε hεlt ↦ ?_⟩
  have hεJ : ∀ i : Fin K.N, ε < ε₀ i := fun i ↦
    hεlt.trans ((hε₁lt i (Finset.mem_range.2 i.2)).trans_le (min_le_left _ _))
  have hεS : ∀ i : Fin K.N, ∀ z ∈ cthickening ε (ca i '' Icc (((i : ℤ) : ℝ) / K.N)
      ((((i : ℤ) : ℝ) + 1) / K.N)),
      b3Rest_ζ hE (K.x i) z ∈ ball (chartAt E (K.x i) (K.x i)) (K.r i) := fun i z hz ↦
    hδseg i z (cthickening_mono ((hεlt.trans (hε₁lt i (Finset.mem_range.2 i.2))).le.trans
      (min_le_right _ _)) _ hz)
  choose κ hκs hκt hκ using fun i : Fin K.N ↦ hJ i ε hε (hεJ i)
  set m := ∫ z, b3Rest_rho ε z
  have hm : 0 < m := b3Rest_integral_rho_pos hε
  set σ : Fin K.N → C → E [⋀^Fin 1]→L[ℝ] ℝ := fun i ↦ b3Rest2_arcPiece hE K ε i
  have hσ : ∀ i : Fin K.N, b3Forms_IsSmooth (σ i) := fun i ↦
    b3Rest_isSmooth_arcForm hE (K.x i) hε (hcac i) (hcac' i) (b3Rest2_cover_le K)
      fun z hz ↦ K.ball_sub i (hεS i z hz)
  have hσt : ∀ i : Fin K.N, tsupport (σ i) ⊆
      (chartAt E (K.x i)).symm '' ball (chartAt E (K.x i) (K.x i)) (K.r i) := fun i ↦
    arc_form_support_of_thickening hE (K.x i) hε (hcac i) (hcac' i)
      (b3Rest2_cover_le K) _ (K.ball_sub i) (hεS i)
  set η := ∑ i : Fin K.N, (σ i + κ i)
  have hη : b3Forms_IsSmooth η :=
    (b3Forms_Ω E C 1).sum_mem fun i _ ↦ (hσ i).add (hκs i)
  refine ⟨κ, hσ, hσt, hκs, (fun i p hp => by
    obtain ⟨u, hu, rfl⟩ := hκt i hp
    exact ⟨u, hu.1, rfl⟩), fun i p hp hpD ↦ ?_, hη.smul _, fun α hα h' hh' ↦ ?_⟩
  · obtain ⟨u, hu, rfl⟩ := hκt i hp
    exact hu.2.2 hpD
  set h : ℤ → E → ℝ := fun k ↦ h' (k % K.N)
  have hh : ∀ k, ∀ u ∈ ball (chartAt E (K.x k) (K.x k)) (K.r k),
      HasFDerivAt (h k) (b3Forms_toCLM (b3Forms_loc α (K.x k) u)) u := by
    intro k
    have := hh' (k % K.N)
    rwa [b3Rest_periodic_emod K.x_add, b3Rest_periodic_emod K.r_add] at this
  have hhN : ∀ k, h (k + K.N) = h k := fun k ↦ by
    show h' ((k + K.N) % K.N) = h' (k % K.N)
    rw [Int.add_emod_right]
  have hPN : ∀ j : ℤ, P (((j + K.N : ℤ) : ℝ) / K.N) = P ((j : ℝ) / K.N) := fun j ↦ by
    rw [show (((j + K.N : ℤ) : ℝ) / K.N) = (j : ℝ) / K.N + 1 by push_cast; field_simp]
    exact hper _
  have hPN1 : ∀ j : ℤ, P ((((j + K.N : ℤ) : ℝ) + 1) / K.N) = P (((j : ℝ) + 1) / K.N) := fun j ↦ by
    rw [show ((((j + K.N : ℤ) : ℝ) + 1) / K.N) = ((j : ℝ) + 1) / K.N + 1 by
      push_cast; field_simp; ring]
    exact hper _
  set T : ℤ → ℝ := fun j ↦
    ∫ z, b3Rest_rho ε z * h j (b3Rest_ζ hE (K.x j) (z + b3Rest_pt hE (K.x j) (P ((j + 1) / K.N))))
  have hTN : ∀ j, T (j + K.N) = T j := fun j ↦ by
    simp only [T, hhN, K.x_add, hPN1]
  set g : ℤ → ℝ := fun j ↦ h j (chartAt E (K.x j) (P ((j + 1) / K.N)))
  have hgN : ∀ j, g (j + K.N) = g j := fun j ↦ by
    simp only [g, hhN, K.x_add, hPN1]
  have hpair : ∀ i : Fin K.N, b3Forms_integral (b3Rest_b hE) (b3Forms_wedgeForm α (σ i + κ i)) =
      (T i - T ((i : ℤ) - 1)) + m * (g ((i : ℤ) - 1) -
        h i (chartAt E (K.x i) (P (((i : ℤ) : ℝ) / K.N)))) := by
    intro i
    rw [b3Rest_wedgeForm_add, b3Forms_integral_add _ (hα.wedgeForm (hσ i)) (hα.wedgeForm (hκs i))]
    erw [b3Rest_integral_wedge_arcForm hE hα (K.x i) isOpen_ball (K.ball_sub i) (hh i) hε
        (hcac i) (hcac' i) (b3Rest2_cover_le K) (hcad i) (hεS i),
      hκ i α hα (h ((i : ℤ) - 1)) (h i) (hh ((i : ℤ) - 1)) (fun u hu ↦ hh i u hu.1)]
    have e0 : ca i (((i : ℤ) : ℝ) / K.N) = b3Rest_pt hE (K.x i) (P (((i : ℤ) : ℝ) / K.N)) :=
      b3Rest2_arcC_of_mem hE (K.x i) ⟨le_rfl, b3Rest2_cover_le K⟩
    have e1 : ca i ((((i : ℤ) : ℝ) + 1) / K.N) =
        b3Rest_pt hE (K.x i) (P ((((i : ℤ) : ℝ) + 1) / K.N)) :=
      b3Rest2_arcC_of_mem hE (K.x i) ⟨b3Rest2_cover_le K, le_rfl⟩
    have e2 : T ((i : ℤ) - 1) = ∫ z, b3Rest_rho ε z * h ((i : ℤ) - 1)
        (b3Rest_ζ hE (K.x ((i : ℤ) - 1)) (z + b3Rest_pt hE (K.x ((i : ℤ) - 1))
          (P (((i : ℤ) : ℝ) / K.N)))) := by
      have : ((((i : ℤ) - 1 : ℤ) : ℝ) + 1) = ((i : ℤ) : ℝ) := by push_cast; ring
      simp only [T, this]
    have e3 : g ((i : ℤ) - 1) = h ((i : ℤ) - 1) (chartAt E (K.x ((i : ℤ) - 1))
        (P (((i : ℤ) : ℝ) / K.N))) := by
      have : ((((i : ℤ) - 1 : ℤ) : ℝ) + 1) = ((i : ℤ) : ℝ) := by push_cast; ring
      simp only [g, this]
    rw [e0, e1, e2, e3]
    simp only [T]
    ring
  rw [b3Rest_wedgeForm_smul, b3Forms_integral_smul, b3Rest_wedgeForm_sum,
    b3Forms_integral_finsetSum _ _ fun i _ ↦ hα.wedgeForm ((hσ i).add (hκs i))]
  simp only [hpair]
  rw [b3Rest2_lineIntegral_eq_sum K hP hα h hh, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  have hF : ∀ F : ℤ → ℝ, ∑ i : Fin K.N, F i = ∑ i ∈ Finset.range K.N, F i := fun F ↦
    Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ F i) K.N
  have hF' : ∀ F : ℤ → ℝ, ∑ i : Fin K.N, F ((i : ℤ) - 1) =
      ∑ i ∈ Finset.range K.N, F ((i : ℤ) - 1) := fun F ↦
    Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ F ((i : ℤ) - 1)) K.N
  rw [hF T, hF' T, hF' g, hF (fun j ↦ h j (chartAt E (K.x j) (P (j / K.N)))),
    b3Rest_sum_shift K.pos hTN, b3Rest_sum_shift K.pos hgN, sub_self, zero_add, ← mul_assoc,
    inv_mul_cancel₀ hm.ne', one_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [g]
  push_cast
  rfl


end HodgeLean.Foundations.Curves.AbelTheorem
