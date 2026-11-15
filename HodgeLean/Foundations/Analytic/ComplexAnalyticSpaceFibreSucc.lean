import HodgeLean.Foundations.Analytic.ComplexAnalyticSpaceFibreCut

/-! # Cartan–Remmert in `ℂⁿ`: positive fibre dimension

The Euclidean Cartan–Remmert loci `ancr_fibreLocus A G k` (the points of `A` whose `G`-fibre has
local dimension at least `k`) have local holomorphic equations. Helpers are prefixed `ancrs_`.

The proof, by induction on the dimension, after reducing a holomorphic `G` to a linear projection
`P` through the graph:

* near a point, `A` is a finite union of components, irreducible at the point and pure
  dimensional near it (`anrem_decomp`), and the locus of `A` is the union of the loci of the
  components (`ancrs_fibreLocus_union`);
* for a component `C` let `m` be the least fibre dimension attained in every neighbourhood of
  the point: the locus for `k ≤ m` is `C`, and for `k > m` it lies in `D = C ∩ {h = 0}` for the cut
  function `h` of `ancrs_cut`, which does not vanish on `C`; `D` has smaller dimension, and the
  locus of `C` is that of `D` because each fibre meets the locus in a set of the same dimension
  (`ancrs_bigFibre`).

Source: Fischer, *Complex Analytic Geometry*, LNM 538, §3.6; Łojasiewicz, *Introduction to
Complex Analytic Geometry*, Ch. V.3.
HC no distance; AV milestone no distance.
-/

noncomputable section

open Set Filter Topology

namespace HodgeLean.Foundations.Analytic

open HodgeLean.Foundations HodgeLean.Foundations.AnalyticDivisorAlgebraic6

/-! ### The Euclidean statement -/

section Euclid

variable {n p : ℕ}

/-- `A` has local holomorphic equations at every point of `O`: near each `z ∈ O`, on an open
`W ⊆ O`, it is the common zero set of finitely many functions holomorphic on `W`. In particular
`A ∩ O` is relatively closed in `O`.
Source: Grauert–Remmert, *Coherent Analytic Sheaves*, §1.1.1 and §1.1.6 (analytic sets in a
domain of `ℂⁿ`). -/
def ancr_LocEqOn (O A : Set (Fin n → ℂ)) : Prop :=
  ∀ z ∈ O, ∃ W : Set (Fin n → ℂ), IsOpen W ∧ z ∈ W ∧ W ⊆ O ∧
    ∃ s : Finset ((Fin n → ℂ) → ℂ), (∀ h ∈ s, AnalyticOnNhd ℂ h W) ∧
      ∀ w ∈ W, (w ∈ A ↔ ∀ h ∈ s, h w = 0)

/-- The Euclidean Cartan–Remmert locus: the points `z ∈ A` at which the fibre
`A ∩ G⁻¹(G z)` has local dimension at least `k`.
Source: Fischer, *Complex Analytic Geometry*, LNM 538, §3.6 (the sets `E_k(f)`). -/
def ancr_fibreLocus (A : Set (Fin n → ℂ)) (G : (Fin n → ℂ) → (Fin p → ℂ)) (k : ℕ) :
    Set (Fin n → ℂ) :=
  {z | z ∈ A ∧ ((k : ℕ∞) : WithBot ℕ∞) ≤ adim2_dimension n (adim2_germ n (A ∩ G ⁻¹' {G z}) z)}

/-- The germ of a nonempty set at one of its points has nonnegative dimension. -/
theorem ancr_dimension_nonneg (A : Set (Fin n → ℂ)) {z : Fin n → ℂ} (hz : z ∈ A) :
    (0 : WithBot ℕ∞) ≤ adim2_dimension n (adim2_germ n A z) := by
  have := Ideal.Quotient.nontrivial_iff.mpr (adim9b_germ_ideal_ne_top n A z hz)
  exact ringKrullDim_nonneg_of_nontrivial

/-- The locus `k = 0` is `A` itself. -/
theorem ancr_fibreLocus_zero (A : Set (Fin n → ℂ)) (G : (Fin n → ℂ) → (Fin p → ℂ)) :
    ancr_fibreLocus A G 0 = A := by
  ext z
  refine ⟨fun h ↦ h.1, fun hz ↦ ⟨hz, ?_⟩⟩
  exact ancr_dimension_nonneg _ ⟨hz, rfl⟩

end Euclid

/-! ### Germ dimension tools -/

section Tools

variable {N : ℕ}

/-- **The large part of a fibre.** If `X` has dimension at least `k` at `z`, so does the set of
the points of `X` at which `X` has dimension at least `k`: it contains a component of `X` at `z`
of dimension at least `k`, pure dimensional near `z`. -/
theorem ancrs_bigFibre {X : Set (Fin N → ℂ)} {z : Fin N → ℂ} (hz : z ∈ X)
    (hloc : anrem_LocEq X z) {k : ℕ}
    (hk : (k : WithBot ℕ∞) ≤ adim2_dimension N (adim2_germ N X z)) :
    (k : WithBot ℕ∞) ≤ adim2_dimension N
      (adim2_germ N {w | w ∈ X ∧ (k : WithBot ℕ∞) ≤ adim2_dimension N (adim2_germ N X w)} z) := by
  obtain ⟨Q, hQ, hkQ⟩ := anrem_exists_minimalPrime_ge hk
  obtain ⟨e', he'⟩ := anrem_quotient_dim_cases Q hQ.1.1
  obtain ⟨C', hzC', hC'X, -, hpure, -⟩ := anrem_component hz hloc hQ he'
  have hC'X' : ∀ᶠ w in 𝓝 z, ∀ᶠ w' in 𝓝 w, w' ∈ C' → w' ∈ X := hC'X.eventually_nhds
  have hsub : ∀ᶠ w in 𝓝 z, w ∈ C' →
      w ∈ {w | w ∈ X ∧ (k : WithBot ℕ∞) ≤ adim2_dimension N (adim2_germ N X w)} := by
    filter_upwards [hC'X, hC'X', hpure] with w hwX hwX' hwp hwC'
    refine ⟨hwX hwC', ?_⟩
    have h1 := anrem_dimension_mono hwX'
    rw [anrem_dimension_eq_of_pure hwC' (hwp hwC')] at h1
    exact (hkQ.trans_eq he').trans h1
  have h2 := anrem_dimension_mono hsub
  rw [anrem_dimension_eq_of_pure hzC' (hpure.self_of_nhds hzC')] at h2
  exact (hkQ.trans_eq he').trans h2

/-- **Dimension drop off a cut.** If `D ⊆ C` has local equations at `y` and its germ ideal
contains a germ outside the prime `Q = I(C, y)` of dimension `e`, then `D` has dimension `< e` at
its points near `y`. -/
theorem ancrs_dims_lt_of_cut {C D : Set (Fin N → ℂ)} {y : Fin N → ℂ} (hDC : D ⊆ C)
    (hlocD : anrem_LocEq D y) {Q : Ideal (AnalyticGerm N)} (hQ : Q.IsPrime)
    (hI : adim2_ideal N (adim2_germ N C y) = Q) {e : ℕ}
    (he : ringKrullDim (AnalyticGerm N ⧸ Q) = (e : WithBot ℕ∞)) {g : AnalyticGerm N}
    (hgD : g ∈ adim2_ideal N (adim2_germ N D y)) (hgQ : g ∉ Q) :
    ∀ᶠ z in 𝓝 y, z ∈ D → adim2_dimension N (adim2_germ N D z) < (e : WithBot ℕ∞) := by
  have hQJ : Q ≤ adim2_ideal N (adim2_germ N D y) := hI ▸ anr_ideal_anti hDC y
  have hdrop := ancrs_dim_sup_lt (P := Q) hgD hgQ
  rw [sup_eq_right.2 hQJ, he] at hdrop
  by_cases hyD : y ∈ D
  · obtain ⟨j, -, hj⟩ := ancrs_dimension_cases hyD
    have hje : j + 1 ≤ e := by
      have : ((j : ℕ) : WithBot ℕ∞) + 1 ≤ (e : WithBot ℕ∞) := by
        change adim2_dimension N (adim2_germ N D y) + 1 ≤ _ at hdrop
        rwa [hj] at hdrop
      exact_mod_cast this
    filter_upwards [anrem_dimension_upper hlocD (e := j) hj.le] with z hz _
    exact lt_of_le_of_lt hz (by exact_mod_cast (show j < e by omega))
  · filter_upwards [ancrs_eventually_not_mem hlocD hyD] with z hz hzD using absurd hzD hz

/-- A natural-valued germ dimension below `k + 1` is at most `k`. -/
theorem ancrs_le_of_not_succ_le {A : Set (Fin N → ℂ)} {z : Fin N → ℂ} (hz : z ∈ A) {k : ℕ}
    (h : ¬ ((k + 1 : ℕ) : WithBot ℕ∞) ≤ adim2_dimension N (adim2_germ N A z)) :
    adim2_dimension N (adim2_germ N A z) ≤ (k : WithBot ℕ∞) := by
  obtain ⟨j, -, hj⟩ := ancrs_dimension_cases hz
  rw [hj] at h ⊢
  have : ¬ k + 1 ≤ j := fun h' ↦ h (by exact_mod_cast h')
  exact_mod_cast (show j ≤ k by omega)

end Tools

/-! ### Fibre loci of linear maps -/

section Locus

variable {N mP : ℕ} (P : (Fin N → ℂ) →L[ℂ] (Fin mP → ℂ))

/-- The fibre locus of a linear map, with a natural-number threshold. -/
theorem ancrs_mem_fibreLocus {A : Set (Fin N → ℂ)} {k : ℕ} {z : Fin N → ℂ} :
    z ∈ ancr_fibreLocus A P k ↔ z ∈ A ∧
      (k : WithBot ℕ∞) ≤ adim2_dimension N (adim2_germ N (A ∩ P ⁻¹' {P z}) z) := Iff.rfl

/-- **Loci of a finite union.** Near `y`, the fibre locus of a finite union of sets with local
equations is the union of their fibre loci. -/
theorem ancrs_fibreLocus_union {ι : Type*} (F : Finset ι) {A : Set (Fin N → ℂ)}
    {C : ι → Set (Fin N → ℂ)} {y : Fin N → ℂ}
    (hcov : ∀ᶠ z in 𝓝 y, z ∈ A ↔ ∃ i ∈ F, z ∈ C i)
    (hloc : ∀ᶠ z in 𝓝 y, ∀ i ∈ F, anrem_LocEq (C i) z) (k : ℕ) :
    ∀ᶠ z in 𝓝 y, z ∈ ancr_fibreLocus A P k ↔ z ∈ ⋃ i ∈ F, ancr_fibreLocus (C i) P k := by
  obtain ⟨W, hW, hWo, hyW⟩ := eventually_nhds_iff.1 (hcov.and hloc)
  filter_upwards [hWo.mem_nhds hyW] with z hzW
  have hcovz : ∀ᶠ w in 𝓝 z, w ∈ A ↔ ∃ i ∈ F, w ∈ C i := by
    filter_upwards [hWo.mem_nhds hzW] with w hw using (hW w hw).1
  have hgerm : adim2_germ N (A ∩ P ⁻¹' {P z}) z =
      adim2_germ N (⋃ i ∈ F, (C i ∩ P ⁻¹' {P z})) z := by
    refine anrem_germ_congr ?_
    filter_upwards [hcovz] with w hw
    simp only [mem_inter_iff, mem_iUnion, exists_prop, hw]
    constructor
    · rintro ⟨⟨i, hi, hwi⟩, hwP⟩; exact ⟨i, hi, hwi, hwP⟩
    · rintro ⟨i, hi, hwi, hwP⟩; exact ⟨⟨i, hi, hwi⟩, hwP⟩
  simp only [mem_iUnion, exists_prop, ancrs_mem_fibreLocus]
  constructor
  · rintro ⟨hzA, hzd⟩
    obtain ⟨i₀, hi₀, hzi₀⟩ := ((hW z hzW).1).1 hzA
    rcases k with _ | k
    · exact ⟨i₀, hi₀, hzi₀, by simpa using ancr_dimension_nonneg _ (⟨hzi₀, rfl⟩ :
        z ∈ C i₀ ∩ P ⁻¹' {P z})⟩
    by_contra hno
    push Not at hno
    have hle : adim2_dimension N (adim2_germ N (⋃ i ∈ F, (C i ∩ P ⁻¹' {P z})) z) ≤
        (k : WithBot ℕ∞) := by
      refine anrem_dimension_biUnion_le F (fun i hi ↦ anrem_locEq_inter ((hW z hzW).2 i hi)
        (ancrs_locEq_level P _ z)) fun i hi hzi ↦ ?_
      exact ancrs_le_of_not_succ_le hzi (fun h ↦ (hno i hi hzi.1).not_ge (by exact_mod_cast h))
    rw [← hgerm] at hle
    have := (show ((k + 1 : ℕ) : WithBot ℕ∞) ≤ _ by exact_mod_cast hzd).trans hle
    norm_cast at this
    omega
  · rintro ⟨i, hi, hzi, hzd⟩
    refine ⟨((hW z hzW).1).2 ⟨i, hi, hzi⟩, hzd.trans (anrem_dimension_mono ?_)⟩
    filter_upwards [hcovz] with w hw hwC
    exact ⟨hw.2 ⟨i, hi, hwC.1⟩, hwC.2⟩

end Locus

/-! ### The induction on dimension -/

section Induction

variable {N mP : ℕ} (P : (Fin N → ℂ) →L[ℂ] (Fin mP → ℂ))

/-- **The step for a component.** Let `C` be, near `y`, a component irreducible at `y` (its germ
the zero germ of the prime `Q = I(C, y)` of dimension `e ≤ d`), pure of dimension `e` near `y`. If
the fibre loci of all sets of dimension `< d` near `y` have local equations at `y`, so do those of
`C`. -/
theorem ancrs_component_step {y : Fin N → ℂ} {d : ℕ}
    (IH : ∀ D : Set (Fin N → ℂ), (∀ᶠ z in 𝓝 y, anrem_LocEq D z) →
      (∀ᶠ z in 𝓝 y, z ∈ D → adim2_dimension N (adim2_germ N D z) < (d : WithBot ℕ∞)) →
      ∀ k, anrem_LocEq (ancr_fibreLocus D P k) y)
    {C : Set (Fin N → ℂ)} (hyC : y ∈ C) (hlocC : ∀ᶠ z in 𝓝 y, anrem_LocEq C z)
    {Q : Ideal (AnalyticGerm N)} (hQ : Q.IsPrime) (hI : adim2_ideal N (adim2_germ N C y) = Q)
    (hZ : adim2_germ N C y = adim2_zeroSet N Q) {e : ℕ}
    (he : ringKrullDim (AnalyticGerm N ⧸ Q) = (e : WithBot ℕ∞)) (hed : e ≤ d)
    (hpure : ∀ᶠ z in 𝓝 y, z ∈ C → adim2_dimension N (adim2_germ N C z) = (e : WithBot ℕ∞))
    (k : ℕ) : anrem_LocEq (ancr_fibreLocus C P k) y := by
  classical
  -- the least fibre dimension attained in every neighbourhood of `y`
  set S : Set ℕ := {j | ∃ U ∈ 𝓝 y, ∀ z ∈ C ∩ U,
    (j : WithBot ℕ∞) ≤ adim2_dimension N (adim2_germ N (C ∩ P ⁻¹' {P z}) z)}
  have hS0 : 0 ∈ S := ⟨univ, univ_mem, fun z hz ↦ by
    simpa using ancr_dimension_nonneg _ (⟨hz.1, rfl⟩ : z ∈ C ∩ P ⁻¹' {P z})⟩
  have hSb : BddAbove S := by
    refine ⟨N, fun j hj ↦ ?_⟩
    obtain ⟨U, hU, hjU⟩ := hj
    have h1 := hjU y ⟨hyC, mem_of_mem_nhds hU⟩
    obtain ⟨i, hiN, hi⟩ := ancrs_dimension_cases (A := C ∩ P ⁻¹' {P y}) (y := y) ⟨hyC, rfl⟩
    rw [hi] at h1
    have : j ≤ i := by exact_mod_cast h1
    omega
  set m := sSup S
  have hmS : m ∈ S := Nat.sSup_mem ⟨0, hS0⟩ hSb
  obtain ⟨U₁, hU₁, hm1⟩ := hmS
  have hm2 : ∀ U ∈ 𝓝 y, ∃ z ∈ C ∩ U,
      adim2_dimension N (adim2_germ N (C ∩ P ⁻¹' {P z}) z) ≤ (m : WithBot ℕ∞) := by
    intro U hU
    by_contra hno
    push Not at hno
    have hm1S : m + 1 ∈ S := ⟨U, hU, fun z hz ↦ by
      have h1 := hno z hz
      obtain ⟨i, -, hi⟩ := ancrs_dimension_cases (A := C ∩ P ⁻¹' {P z}) (y := z) ⟨hz.1, rfl⟩
      rw [hi] at h1 ⊢
      have : m < i := by exact_mod_cast h1
      exact_mod_cast (show m + 1 ≤ i by omega)⟩
    have := le_csSup hSb hm1S
    omega
  by_cases hk : k ≤ m
  · -- the locus is `C` near `y`
    refine ancrs_locEq_congr ?_ hlocC.self_of_nhds
    filter_upwards [hU₁] with z hzU
    constructor
    · intro hzC
      exact ⟨hzC, (show (k : WithBot ℕ∞) ≤ (m : WithBot ℕ∞) by exact_mod_cast hk).trans
        (hm1 z ⟨hzC, hzU⟩)⟩
    · exact fun h ↦ h.1
  push Not at hk
  have hmk : ((m + 1 : ℕ) : WithBot ℕ∞) ≤ (k : WithBot ℕ∞) := by exact_mod_cast hk
  obtain ⟨h, han, hnv, hvan⟩ := ancrs_cut hlocC.self_of_nhds hQ hI hZ he hpure P m hm2
  set D := C ∩ {z | h z = 0} with hDdef
  have hlocD : ∀ᶠ z in 𝓝 y, anrem_LocEq D z := by
    filter_upwards [hlocC, han.eventually_analyticAt] with z hz hza
    exact anrem_locEq_inter hz (ancrs_locEq_zero hza)
  have han0 : AnalyticAt ℂ (fun v ↦ h (y + v)) 0 :=
    AnalyticAt.comp_of_eq (g := h) (f := fun v ↦ y + v) han
      (analyticAt_const.add analyticAt_id) (by simp)
  let g : AnalyticGerm N := ⟨Filter.Germ.ofFun (fun v ↦ h (y + v)), _, han0, rfl⟩
  have hgD : g ∈ adim2_ideal N (adim2_germ N D y) := by
    rw [anrem_mem_ideal_iff D y g _ rfl]
    exact Eventually.of_forall fun v hv ↦ hv.2
  have hgQ : g ∉ Q := by
    rw [← hI, anrem_mem_ideal_iff C y g _ rfl]
    intro hall
    apply hnv
    have ht : Tendsto (fun z : Fin N → ℂ ↦ z - y) (𝓝 y) (𝓝 0) :=
      tendsto_sub_nhds_zero_iff.2 tendsto_id
    filter_upwards [ht.eventually hall] with z hz hzC
    simpa using hz (by simpa using hzC)
  have hdims := ancrs_dims_lt_of_cut inter_subset_left hlocD.self_of_nhds hQ hI he hgD hgQ
  have hdimsd : ∀ᶠ z in 𝓝 y, z ∈ D → adim2_dimension N (adim2_germ N D z) < (d : WithBot ℕ∞) := by
    filter_upwards [hdims] with z hz hzD
    exact (hz hzD).trans_le (by exact_mod_cast hed)
  have hIH := IH D hlocD hdimsd k
  obtain ⟨W, hW, hWo, hyW⟩ := eventually_nhds_iff.1 (hvan.and hlocC)
  refine ancrs_locEq_congr ?_ hIH
  filter_upwards [hWo.mem_nhds hyW] with z hzW
  constructor
  · rintro ⟨⟨hzC, -⟩, hzd⟩
    exact ⟨hzC, hzd.trans (anrem_dimension_mono (Eventually.of_forall fun w hw ↦
      ⟨hw.1.1, hw.2⟩))⟩
  · rintro ⟨hzC, hzd⟩
    have hz0 : h z = 0 := (hW z hzW).1 hzC (hmk.trans hzd)
    refine ⟨⟨hzC, hz0⟩, ?_⟩
    have hX : anrem_LocEq (C ∩ P ⁻¹' {P z}) z :=
      anrem_locEq_inter (hW z hzW).2 (ancrs_locEq_level P _ z)
    have hbig := ancrs_bigFibre (⟨hzC, rfl⟩ : z ∈ C ∩ P ⁻¹' {P z}) hX hzd
    refine hbig.trans (anrem_dimension_mono ?_)
    filter_upwards [hWo.mem_nhds hzW] with w hwW hw
    obtain ⟨hwX, hwd⟩ := hw
    have hPw : P w = P z := hwX.2
    have hfd : adim2_germ N (C ∩ P ⁻¹' {P w}) w = adim2_germ N (C ∩ P ⁻¹' {P z}) w := by
      rw [hPw]
    have hw0 : h w = 0 := (hW w hwW).1 hwX.1 (hmk.trans (hfd ▸ hwd))
    exact ⟨⟨hwX.1, hw0⟩, hwX.2⟩

/-- **The induction on dimension.** For every `d`, the fibre loci of a set with local equations
near `y` and of dimension `< d` at its points near `y` have local equations at `y`. -/
theorem ancrs_locus_induction (d : ℕ) : ∀ (Γ : Set (Fin N → ℂ)) (y : Fin N → ℂ),
    (∀ᶠ z in 𝓝 y, anrem_LocEq Γ z) →
    (∀ᶠ z in 𝓝 y, z ∈ Γ → adim2_dimension N (adim2_germ N Γ z) < (d : WithBot ℕ∞)) →
    ∀ k, anrem_LocEq (ancr_fibreLocus Γ P k) y := by
  classical
  induction d with
  | zero =>
    intro Γ y hloc hdim k
    apply ancrs_locEq_of_eventually_not_mem
    filter_upwards [hdim] with z hz hzE
    have h1 := hz hzE.1
    have h2 := ancr_dimension_nonneg Γ hzE.1
    exact absurd (h2.trans_lt h1) (by simp)
  | succ d ih =>
    intro Γ y hloc hdim k
    by_cases hy : y ∈ Γ
    swap
    · apply ancrs_locEq_of_eventually_not_mem
      filter_upwards [ancrs_eventually_not_mem hloc.self_of_nhds hy] with z hz hzE
      exact hz hzE.1
    obtain ⟨F, e, Cs, hF, hFe, hFC, hFloc, hFpure, hFcov⟩ := anrem_decomp hy hloc.self_of_nhds
    have hgermΓ : adim2_germ N Γ y = F.sup (adim2_zeroSet N) := by
      calc adim2_germ N Γ y = adim2_germ N (⋃ Q ∈ F, Cs Q) y := by
            refine anrem_germ_congr ?_
            filter_upwards [hFcov] with z hz
            simpa using hz
        _ = F.sup (fun Q ↦ adim2_germ N (Cs Q) y) := by
            simp only [adim2_germ]
            rw [ancrs_germ_finset_sup F (fun Q v ↦ y + v ∈ Cs Q)]
            congr 1
            funext v
            simp
        _ = F.sup (adim2_zeroSet N) := Finset.sup_congr rfl fun Q hQ ↦ (hFC Q hQ).2
    have hFset : (F : Set (Ideal (AnalyticGerm N))) =
        (adim2_ideal N (adim2_germ N Γ y)).minimalPrimes := by
      ext Q; exact hF Q
    have hcomp : ∀ Q ∈ F, anrem_LocEq (ancr_fibreLocus (Cs Q) P k) y := by
      intro Q hQF
      have hQmin := (hF Q).1 hQF
      have hI : adim2_ideal N (adim2_germ N (Cs Q) y) = Q := by
        rw [(hFC Q hQF).2]
        exact adim9b_minimal_component_ideal N (adim2_germ N Γ y) F hFset hgermΓ Q hQF
      have hed : e Q ≤ d := by
        have h1 := anr_minimal_le_dim (adim2_germ N Γ y) Q hQmin
        rw [hFe Q hQF] at h1
        have h2 := h1.trans_lt (hdim.self_of_nhds hy)
        have : e Q < d + 1 := by exact_mod_cast h2
        omega
      have hpureQ : ∀ᶠ z in 𝓝 y, z ∈ Cs Q →
          adim2_dimension N (adim2_germ N (Cs Q) z) = (e Q : WithBot ℕ∞) := by
        filter_upwards [hFpure] with z hz hzC
        exact anrem_dimension_eq_of_pure hzC (hz Q hQF hzC)
      have hlocQ : ∀ᶠ z in 𝓝 y, anrem_LocEq (Cs Q) z := by
        filter_upwards [hFloc] with z hz using hz Q hQF
      exact ancrs_component_step P (fun D hD hDd ↦ ih D y hD hDd) (hFC Q hQF).1 hlocQ
        hQmin.1.1 hI (hFC Q hQF).2 (hFe Q hQF) hed hpureQ k
    have hU := ancrs_fibreLocus_union P F hFcov hFloc k
    refine ancrs_locEq_congr ?_ (anrem_locEq_biUnion F hcomp)
    filter_upwards [hU] with z hz using hz.symm

end Induction

/-! ### From holomorphic maps to linear projections -/

section Graph

variable {n p : ℕ}

/-- Local equations on `O` give local equations at each point of `O`. -/
theorem ancrs_locEq_of_locEqOn {O A : Set (Fin n → ℂ)} (hA : ancr_LocEqOn O A) {z : Fin n → ℂ}
    (hz : z ∈ O) : anrem_LocEq A z := by
  classical
  obtain ⟨W, hW, hzW, -, s, hs, hsA⟩ := hA z hz
  refine ⟨W, hW, hzW, s.card, fun j ↦ (s.equivFin.symm j).1, fun j ↦ hs _ (s.equivFin.symm j).2,
    fun w hw ↦ ?_⟩
  rw [hsA w hw]
  constructor
  · intro h j; exact h _ (s.equivFin.symm j).2
  · intro h g hg; simpa using h (s.equivFin ⟨g, hg⟩)

/-- The graph meets a fibre of the second projection in the graph of the fibre. -/
theorem ancrs_graph_inter_fibre (A : Set (Fin n → ℂ)) (G : (Fin n → ℂ) → (Fin p → ℂ))
    (t : Fin p → ℂ) :
    anrem_graph A G ∩ (anrem_snd : (Fin (n + p) → ℂ) →L[ℂ] (Fin p → ℂ)) ⁻¹' {t} =
      anrem_graph (A ∩ G ⁻¹' {t}) G := by
  ext u
  simp only [anrem_graph, mem_inter_iff, mem_ofPred_eq, mem_preimage, mem_singleton_iff]
  constructor
  · rintro ⟨⟨hA, hG⟩, ht⟩; exact ⟨⟨hA, hG ▸ ht⟩, hG⟩
  · rintro ⟨⟨hA, ht⟩, hG⟩; exact ⟨⟨hA, hG⟩, hG ▸ ht⟩

/-- The graph of a map holomorphic on `O` over a set with local equations on `O` has local
equations at the points over `O`. -/
theorem ancrs_locEq_graph {O A : Set (Fin n → ℂ)} (hA : ancr_LocEqOn O A)
    {G : (Fin n → ℂ) → (Fin p → ℂ)} (hG : AnalyticOnNhd ℂ G O) {u : Fin (n + p) → ℂ}
    (hu : anrem_fst u ∈ O) : anrem_LocEq (anrem_graph A G) u := by
  have h1 : anrem_LocEq ((anrem_fst : (Fin (n + p) → ℂ) →L[ℂ] (Fin n → ℂ)) ⁻¹' A) u := by
    have := anrem_locEq_prod (ancrs_locEq_of_locEqOn hA hu) (anrem_snd u)
    rwa [anrem_append_fst_snd] at this
  have hOo : IsOpen ((anrem_fst : (Fin (n + p) → ℂ) →L[ℂ] (Fin n → ℂ)) ⁻¹'
      {z | AnalyticAt ℂ G z}) :=
    (isOpen_analyticAt ℂ G).preimage anrem_fst.continuous
  have h2 : anrem_LocEq {u' : Fin (n + p) → ℂ | anrem_snd u' = G (anrem_fst u')} u := by
    refine ⟨_, hOo, hG _ hu, p, fun i u' ↦ anrem_snd u' i - G (anrem_fst u') i,
      fun i u' hu' ↦ ?_, fun u' _ ↦ ?_⟩
    · have hGi : AnalyticAt ℂ (fun z ↦ G z i) (anrem_fst u') :=
        ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin p ↦ ℂ) i).analyticAt _).comp hu'
      exact (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin p ↦ ℂ) i).comp
        anrem_snd).analyticAt _).sub (hGi.comp (anrem_fst.analyticAt _))
    · simp only [mem_ofPred_eq, sub_eq_zero]
      exact ⟨fun h i ↦ by rw [h], fun h ↦ funext h⟩
  have h3 := anrem_locEq_inter h1 h2
  convert h3 using 1
  ext u'
  simp [anrem_graph]

/-- **Cartan–Remmert in `ℂⁿ`, all thresholds.** For `A` with local holomorphic equations on an
open `O ⊆ ℂⁿ` and `G` holomorphic on `O`, the fibre loci `ancr_fibreLocus A G k` have local
holomorphic equations on `O`: through the graph of `G` they are the fibre loci of the second
projection, which `ancrs_locus_induction` cuts out.
Source: Fischer, *Complex Analytic Geometry*, LNM 538, §3.6. -/
theorem ancrs_locEqOn_fibreLocus (O : Set (Fin n → ℂ)) (hO : IsOpen O)
    (A : Set (Fin n → ℂ)) (hA : ancr_LocEqOn O A) (G : (Fin n → ℂ) → (Fin p → ℂ))
    (hG : AnalyticOnNhd ℂ G O) (k : ℕ) :
    ancr_LocEqOn O (ancr_fibreLocus A G k) := by
  classical
  intro z hz
  set Γ := anrem_graph A G
  set P : (Fin (n + p) → ℂ) →L[ℂ] (Fin p → ℂ) := anrem_snd
  set φ : (Fin n → ℂ) → (Fin (n + p) → ℂ) := fun w ↦ Fin.append w (G w)
  have hφa : ∀ w ∈ O, AnalyticAt ℂ φ w := fun w hw ↦
    anrem_analyticAt_append analyticAt_id (hG w hw)
  -- the loci correspond through `φ`
  have hkey : ∀ w ∈ O, (w ∈ ancr_fibreLocus A G k ↔ φ w ∈ ancr_fibreLocus Γ P k) := by
    intro w hw
    have hmem : φ w ∈ Γ ↔ w ∈ A := by simp [φ, Γ, anrem_graph]
    have hP : P (φ w) = G w := by simp [φ, P]
    have hdim : adim2_dimension (n + p) (adim2_germ (n + p) (Γ ∩ P ⁻¹' {P (φ w)}) (φ w)) =
        adim2_dimension n (adim2_germ n (A ∩ G ⁻¹' {G w}) w) := by
      rw [hP, ancrs_graph_inter_fibre]
      exact anrem_graph_dimension (A ∩ G ⁻¹' {G w}) G w (hG w hw)
    change (w ∈ A ∧ _) ↔ (φ w ∈ Γ ∧ _)
    rw [hmem, hdim]
  -- local equations of the graph and the dimension bound
  have hfstO : IsOpen ((anrem_fst : (Fin (n + p) → ℂ) →L[ℂ] (Fin n → ℂ)) ⁻¹' O) :=
    hO.preimage anrem_fst.continuous
  have hφz : anrem_fst (φ z) ∈ O := by simpa [φ] using hz
  have hloc : ∀ᶠ u in 𝓝 (φ z), anrem_LocEq Γ u := by
    filter_upwards [hfstO.mem_nhds hφz] with u hu using ancrs_locEq_graph hA hG hu
  have hdim : ∀ᶠ u in 𝓝 (φ z), u ∈ Γ →
      adim2_dimension (n + p) (adim2_germ (n + p) Γ u) < ((n + p + 1 : ℕ) : WithBot ℕ∞) := by
    refine Eventually.of_forall fun u hu ↦ ?_
    obtain ⟨j, hj, hjd⟩ := ancrs_dimension_cases hu
    rw [hjd]
    exact_mod_cast Nat.lt_succ_of_le hj
  obtain ⟨U, hU, hφU, m, f, hf, hfU⟩ := ancrs_locus_induction P (n + p + 1) Γ (φ z) hloc hdim k
  have hφc : ContinuousOn φ O := fun w hw ↦ (hφa w hw).continuousAt.continuousWithinAt
  refine ⟨O ∩ φ ⁻¹' U, hφc.isOpen_inter_preimage hO hU, ⟨hz, hφU⟩, inter_subset_left,
    Finset.univ.image fun j ↦ f j ∘ φ, ?_, fun w hw ↦ ?_⟩
  · intro h hh w hw
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hh
    exact (hf j (φ w) hw.2).comp (hφa w hw.1)
  · rw [hkey w hw.1, hfU (φ w) hw.2]
    simp only [Finset.mem_image, Finset.mem_univ, true_and, forall_exists_index,
      forall_apply_eq_imp_iff, Function.comp_apply]

end Graph

end HodgeLean.Foundations.Analytic
