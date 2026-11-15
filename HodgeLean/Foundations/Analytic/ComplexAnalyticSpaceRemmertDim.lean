import HodgeLean.Foundations.Analytic.ComplexAnalyticSpaceRemmert
import HodgeLean.Foundations.Analytic.ComplexAnalyticSpaceRemmertStein

/-! # Germ dimension tools for Remmert's proper mapping theorem

Lane `an-rem`, prefix `anrem_`. Transfer of germ ideals, minimal primes and Krull dimension along
an analytic map with an analytic retraction (graphs of analytic maps in particular); dimension
bounds for linear maps with isolated fibres, linear images (through Hausdorff dimension) and products
with `ℂʲ`; and openness of a linear map at a point isolated in its fibre on a component of full
dimension. HC no distance; AV milestone no distance.
-/

noncomputable section

open Set Filter Topology

namespace HodgeLean.Foundations.Analytic

open HodgeLean.Foundations HodgeLean.Foundations.AnalyticDivisorAlgebraic6

/-- Membership in the ideal of a set germ, read on a representative. -/
theorem anrem_mem_ideal_iff {n : ℕ} (A : Set (Fin n → ℂ)) (w : Fin n → ℂ)
    (h : AnalyticGerm n) (φ : (Fin n → ℂ) → ℂ) (hφ : Germ.ofFun φ = h.val) :
    h ∈ adim2_ideal n (adim2_germ n A w) ↔ ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), w + z ∈ A → φ z = 0 := by
  change adim2_germ n A w ≤ h.val.map (· = 0) ↔ _
  rw [← hφ, adim2_germ, Germ.map_coe, Germ.coe_le]
  rfl

/-- **Transfer of germ ideals** along an analytic map with an analytic retraction which carries
one set onto the other near the base points. -/
theorem anrem_germ_transfer_comap {n N : ℕ} (A : Set (Fin n → ℂ)) (B : Set (Fin N → ℂ))
    (w : Fin n → ℂ) (γ : Fin N → ℂ) (g : (Fin n → ℂ) → (Fin N → ℂ)) (hg : AnalyticAt ℂ g 0)
    (hg0 : g 0 = 0) (π : (Fin N → ℂ) → (Fin n → ℂ)) (hπ : ContinuousAt π 0) (hπ0 : π 0 = 0)
    (hAB : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), w + z ∈ A → γ + g z ∈ B)
    (hBA : ∀ᶠ u in 𝓝 (0 : Fin N → ℂ), γ + u ∈ B → w + π u ∈ A ∧ g (π u) = u) :
    Ideal.comap (adim9b_germPullback g hg hg0) (adim2_ideal n (adim2_germ n A w)) =
      adim2_ideal N (adim2_germ N B γ) := by
  ext h
  obtain ⟨φ, -, hφ⟩ := h.2
  rw [Ideal.mem_comap, anrem_mem_ideal_iff A w _ (φ ∘ g)
    ((adim9b_germPullback_rep g hg hg0 h φ hφ).symm), anrem_mem_ideal_iff B γ h φ hφ]
  have hgt : Tendsto g (𝓝 0) (𝓝 0) := hg0 ▸ hg.continuousAt.tendsto
  have hπt : Tendsto π (𝓝 0) (𝓝 0) := hπ0 ▸ hπ.tendsto
  constructor
  · intro E
    filter_upwards [hBA, hπt.eventually E] with u h1 h2 hu
    obtain ⟨hA, hgu⟩ := h1 hu
    rw [← hgu]
    exact h2 hA
  · intro E
    filter_upwards [hAB, hgt.eventually E] with z h1 h2 hz
    exact h2 (h1 hz)

/-- The quotient rings of transferred germs are isomorphic. -/
def anrem_germ_transfer_equiv {n N : ℕ} (A : Set (Fin n → ℂ)) (B : Set (Fin N → ℂ))
    (w : Fin n → ℂ) (γ : Fin N → ℂ) (g : (Fin n → ℂ) → (Fin N → ℂ)) (hg : AnalyticAt ℂ g 0)
    (hg0 : g 0 = 0) (π : (Fin N → ℂ) → (Fin n → ℂ)) (hπ : AnalyticAt ℂ π 0) (hπ0 : π 0 = 0)
    (hsec : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), π (g z) = z)
    (hAB : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), w + z ∈ A → γ + g z ∈ B)
    (hBA : ∀ᶠ u in 𝓝 (0 : Fin N → ℂ), γ + u ∈ B → w + π u ∈ A ∧ g (π u) = u) :
    (AnalyticGerm N ⧸ adim2_ideal N (adim2_germ N B γ)) ≃+*
      (AnalyticGerm n ⧸ adim2_ideal n (adim2_germ n A w)) :=
  have hsurj : Function.Surjective ((Ideal.Quotient.mk (adim2_ideal n (adim2_germ n A w))).comp
      (adim9b_germPullback g hg hg0)) :=
    Ideal.Quotient.mk_surjective.comp (adim9b_germPullback_surjective g hg hg0 π hπ hπ0 hsec)
  have hker : RingHom.ker ((Ideal.Quotient.mk (adim2_ideal n (adim2_germ n A w))).comp
      (adim9b_germPullback g hg hg0)) = adim2_ideal N (adim2_germ N B γ) := by
    rw [← RingHom.comap_ker, Ideal.mk_ker]
    exact anrem_germ_transfer_comap A B w γ g hg hg0 π hπ.continuousAt hπ0 hAB hBA
  (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj)

theorem anrem_germ_transfer_dimension {n N : ℕ} (A : Set (Fin n → ℂ)) (B : Set (Fin N → ℂ))
    (w : Fin n → ℂ) (γ : Fin N → ℂ) (g : (Fin n → ℂ) → (Fin N → ℂ)) (hg : AnalyticAt ℂ g 0)
    (hg0 : g 0 = 0) (π : (Fin N → ℂ) → (Fin n → ℂ)) (hπ : AnalyticAt ℂ π 0) (hπ0 : π 0 = 0)
    (hsec : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), π (g z) = z)
    (hAB : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), w + z ∈ A → γ + g z ∈ B)
    (hBA : ∀ᶠ u in 𝓝 (0 : Fin N → ℂ), γ + u ∈ B → w + π u ∈ A ∧ g (π u) = u) :
    adim2_dimension N (adim2_germ N B γ) = adim2_dimension n (adim2_germ n A w) :=
  ringKrullDim_eq_of_ringEquiv
    (anrem_germ_transfer_equiv A B w γ g hg hg0 π hπ hπ0 hsec hAB hBA)

/-- Minimal primes of transferred germs correspond, with the same quotient dimensions. -/
theorem anrem_germ_transfer_minimalPrimes {n N : ℕ} (A : Set (Fin n → ℂ)) (B : Set (Fin N → ℂ))
    (w : Fin n → ℂ) (γ : Fin N → ℂ) (g : (Fin n → ℂ) → (Fin N → ℂ)) (hg : AnalyticAt ℂ g 0)
    (hg0 : g 0 = 0) (π : (Fin N → ℂ) → (Fin n → ℂ)) (hπ : AnalyticAt ℂ π 0) (hπ0 : π 0 = 0)
    (hsec : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), π (g z) = z)
    (hAB : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), w + z ∈ A → γ + g z ∈ B)
    (hBA : ∀ᶠ u in 𝓝 (0 : Fin N → ℂ), γ + u ∈ B → w + π u ∈ A ∧ g (π u) = u)
    (e : WithBot ℕ∞) :
    (∀ Q ∈ (adim2_ideal n (adim2_germ n A w)).minimalPrimes,
      ringKrullDim (AnalyticGerm n ⧸ Q) ≤ e) ↔
    (∀ Q ∈ (adim2_ideal N (adim2_germ N B γ)).minimalPrimes,
      ringKrullDim (AnalyticGerm N ⧸ Q) ≤ e) := by
  set φ := adim9b_germPullback g hg hg0
  have hsurj : Function.Surjective φ := adim9b_germPullback_surjective g hg hg0 π hπ hπ0 hsec
  have hcomap := anrem_germ_transfer_comap A B w γ g hg hg0 π hπ.continuousAt hπ0 hAB hBA
  have hdimP : ∀ P : Ideal (AnalyticGerm n),
      ringKrullDim (AnalyticGerm N ⧸ P.comap φ) = ringKrullDim (AnalyticGerm n ⧸ P) := by
    intro P
    have hs : Function.Surjective ((Ideal.Quotient.mk P).comp φ) :=
      Ideal.Quotient.mk_surjective.comp hsurj
    have hk : RingHom.ker ((Ideal.Quotient.mk P).comp φ) = P.comap φ := by
      rw [← RingHom.comap_ker, Ideal.mk_ker]
    exact ringKrullDim_eq_of_ringEquiv
      ((Ideal.quotEquivOfEq hk.symm).trans (RingHom.quotientKerEquivOfSurjective hs))
  rw [← hcomap, Ideal.comap_minimalPrimes_eq_of_surjective hsurj]
  constructor
  · rintro h _ ⟨P, hP, rfl⟩
    rw [hdimP]; exact h P hP
  · intro h P hP
    rw [← hdimP]; exact h _ ⟨P, hP, rfl⟩


/-! ### Graphs -/

section Graph

variable {n m : ℕ}

/-- The first block of coordinates of `ℂ^(n+m)`. -/
def anrem_fst : (Fin (n + m) → ℂ) →L[ℂ] (Fin n → ℂ) :=
  ContinuousLinearMap.pi fun i ↦ ContinuousLinearMap.proj (Fin.castAdd m i)

/-- The second block of coordinates of `ℂ^(n+m)`. -/
def anrem_snd : (Fin (n + m) → ℂ) →L[ℂ] (Fin m → ℂ) :=
  ContinuousLinearMap.pi fun j ↦ ContinuousLinearMap.proj (Fin.natAdd n j)

@[simp] theorem anrem_fst_append (a : Fin n → ℂ) (b : Fin m → ℂ) :
    anrem_fst (Fin.append a b) = a := by
  funext i; simp [anrem_fst]

@[simp] theorem anrem_snd_append (a : Fin n → ℂ) (b : Fin m → ℂ) :
    anrem_snd (Fin.append a b) = b := by
  funext j; simp [anrem_snd]

@[simp] theorem anrem_append_fst_snd (u : Fin (n + m) → ℂ) :
    Fin.append (anrem_fst u) (anrem_snd u) = u := by
  funext i
  refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) i
  · simp [anrem_fst]
  · simp [anrem_snd]

theorem anrem_append_add (a a' : Fin n → ℂ) (b b' : Fin m → ℂ) :
    Fin.append (a + a') (b + b') = Fin.append a b + Fin.append a' b' := by
  funext i
  refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) i <;> simp

@[simp] theorem anrem_append_zero : Fin.append (0 : Fin n → ℂ) (0 : Fin m → ℂ) = 0 := by
  funext i
  refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) i <;> simp

theorem anrem_analyticAt_append {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {p : E → Fin n → ℂ} {q : E → Fin m → ℂ} {x : E} (hp : AnalyticAt ℂ p x)
    (hq : AnalyticAt ℂ q x) : AnalyticAt ℂ (fun e ↦ Fin.append (p e) (q e)) x := by
  rw [analyticAt_pi_iff]
  intro i
  refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) i
  · simp only [Fin.append_left]
    exact (analyticAt_pi_iff.1 hp) i
  · simp only [Fin.append_right]
    exact (analyticAt_pi_iff.1 hq) j

/-- The graph of a map over a subset of `ℂⁿ`, inside `ℂ^(n+m)`. -/
def anrem_graph (A : Set (Fin n → ℂ)) (F : (Fin n → ℂ) → (Fin m → ℂ)) :
    Set (Fin (n + m) → ℂ) :=
  {u | anrem_fst u ∈ A ∧ anrem_snd u = F (anrem_fst u)}

theorem anrem_append_mem_graph {A : Set (Fin n → ℂ)} {F : (Fin n → ℂ) → (Fin m → ℂ)}
    {z : Fin n → ℂ} (hz : z ∈ A) : Fin.append z (F z) ∈ anrem_graph A F := by
  simp [anrem_graph, hz]

/-- The data transferring germs at `w` of `A` to germs of its graph. -/
theorem anrem_graph_transfer_data (A : Set (Fin n → ℂ)) (F : (Fin n → ℂ) → (Fin m → ℂ))
    (w : Fin n → ℂ) :
    (∀ z, anrem_fst (Fin.append z (F (w + z) - F w)) = z) ∧
    (∀ z, w + z ∈ A → Fin.append w (F w) + Fin.append z (F (w + z) - F w) ∈ anrem_graph A F) ∧
    (∀ u, Fin.append w (F w) + u ∈ anrem_graph A F →
      w + anrem_fst u ∈ A ∧ Fin.append (anrem_fst u) (F (w + anrem_fst u) - F w) = u) := by
  refine ⟨fun z ↦ by simp, fun z hz ↦ ?_, fun u hu ↦ ?_⟩
  · rw [← anrem_append_add]
    simp only [add_sub_cancel]
    exact anrem_append_mem_graph hz
  · obtain ⟨h1, h2⟩ := hu
    simp only [map_add, anrem_fst_append, anrem_snd_append] at h1 h2
    refine ⟨h1, ?_⟩
    conv_rhs => rw [← anrem_append_fst_snd u]
    congr 1
    rw [← h2]; abel

theorem anrem_graph_minimalPrimes (A : Set (Fin n → ℂ)) (F : (Fin n → ℂ) → (Fin m → ℂ))
    (w : Fin n → ℂ) (hF : AnalyticAt ℂ F w) (e : WithBot ℕ∞) :
    (∀ Q ∈ (adim2_ideal n (adim2_germ n A w)).minimalPrimes,
      ringKrullDim (AnalyticGerm n ⧸ Q) ≤ e) ↔
    (∀ Q ∈ (adim2_ideal (n + m) (adim2_germ (n + m) (anrem_graph A F)
      (Fin.append w (F w)))).minimalPrimes, ringKrullDim (AnalyticGerm (n + m) ⧸ Q) ≤ e) := by
  obtain ⟨hsec, hAB, hBA⟩ := anrem_graph_transfer_data A F w
  have hg : AnalyticAt ℂ (fun z ↦ Fin.append z (F (w + z) - F w)) 0 :=
    anrem_analyticAt_append analyticAt_id
      ((hF.comp_of_eq (analyticAt_const.add analyticAt_id) (by simp)).sub analyticAt_const)
  exact anrem_germ_transfer_minimalPrimes A _ w _ _ hg (by simp) anrem_fst
    (anrem_fst.analyticAt 0) (map_zero _) (Eventually.of_forall hsec)
    (Eventually.of_forall hAB) (Eventually.of_forall hBA) e

theorem anrem_graph_dimension (A : Set (Fin n → ℂ)) (F : (Fin n → ℂ) → (Fin m → ℂ))
    (w : Fin n → ℂ) (hF : AnalyticAt ℂ F w) :
    adim2_dimension (n + m) (adim2_germ (n + m) (anrem_graph A F) (Fin.append w (F w))) =
      adim2_dimension n (adim2_germ n A w) := by
  obtain ⟨hsec, hAB, hBA⟩ := anrem_graph_transfer_data A F w
  have hg : AnalyticAt ℂ (fun z ↦ Fin.append z (F (w + z) - F w)) 0 :=
    anrem_analyticAt_append analyticAt_id
      ((hF.comp_of_eq (analyticAt_const.add analyticAt_id) (by simp)).sub analyticAt_const)
  exact anrem_germ_transfer_dimension A _ w _ _ hg (by simp) anrem_fst
    (anrem_fst.analyticAt 0) (map_zero _) (Eventually.of_forall hsec)
    (Eventually.of_forall hAB) (Eventually.of_forall hBA)

end Graph


open private adim9_ringKrullDim_eq_of_finite_injective adim9_local_onto adim9_analytic_dimH_le
  adim9_krullDim_drop adim9_le_pred_of_succ_le
  from HodgeLean.Foundations.AnalyticGermRSAssemblyProofs

/-! ### Dimension and linear maps -/

/-- The germ of a set does not see what happens away from the base point. -/
theorem anrem_germ_inter_nhds {n : ℕ} (A O : Set (Fin n → ℂ)) (y : Fin n → ℂ) (hO : O ∈ 𝓝 y) :
    adim2_germ n (A ∩ O) y = adim2_germ n A y := by
  apply Germ.coe_eq.2
  have ht : Tendsto (fun z : Fin n → ℂ ↦ y + z) (𝓝 0) (𝓝 y) := by
    simpa using (tendsto_id (x := 𝓝 (0 : Fin n → ℂ))).const_add y
  filter_upwards [ht.eventually hO] with z hz
  exact propext ⟨fun h ↦ h.1, fun h ↦ ⟨h, hz⟩⟩

/-- An isolated point of a set has germ dimension at most zero. -/
theorem anrem_dimension_le_zero_of_isolated {n : ℕ} {C : Set (Fin n → ℂ)} {y : Fin n → ℂ}
    (hiso : ∀ᶠ z in 𝓝 y, z ∈ C → z = y) : adim2_dimension n (adim2_germ n C y) ≤ 0 := by
  have hm : analyticGermMaximalIdeal n ≤ adim2_ideal n (adim2_germ n C y) := by
    intro a ha
    obtain ⟨φ, -, hφ⟩ := a.2
    have h0 : φ 0 = 0 := by
      have : analyticGermValue n a = 0 := ha
      change a.1.value = 0 at this
      rwa [← hφ] at this
    rw [anrem_mem_ideal_iff C y a φ hφ]
    have ht : Tendsto (fun z : Fin n → ℂ ↦ y + z) (𝓝 0) (𝓝 y) := by
      simpa using (tendsto_id (x := 𝓝 (0 : Fin n → ℂ))).const_add y
    filter_upwards [ht.eventually hiso] with z hz hzC
    have : y + z = y := hz hzC
    have hz0 : z = 0 := by simpa using this
    rw [hz0, h0]
  have hmax : (analyticGermMaximalIdeal n).IsMaximal := by
    apply RingHom.ker_isMaximal_of_surjective
    intro c
    exact ⟨⟨Germ.ofFun (fun _ ↦ c), fun _ ↦ c, analyticAt_const, rfl⟩, rfl⟩
  calc adim2_dimension n (adim2_germ n C y)
      ≤ ringKrullDim (AnalyticGerm n ⧸ analyticGermMaximalIdeal n) := anr_dim_le_of_le hm
    _ = 0 := ringKrullDim_eq_zero_of_isField ((Ideal.Quotient.maximal_ideal_iff_isField_quotient
        _).1 hmax)

/-- Minimal primes bound the germ dimension. -/
theorem anrem_dimension_le_iff {n : ℕ} (A : Set (Fin n → ℂ)) (y : Fin n → ℂ) (e : WithBot ℕ∞) :
    adim2_dimension n (adim2_germ n A y) ≤ e ↔
      ∀ Q ∈ (adim2_ideal n (adim2_germ n A y)).minimalPrimes,
        ringKrullDim (AnalyticGerm n ⧸ Q) ≤ e :=
  ⟨fun h Q hQ ↦ (anr_minimal_le_dim _ Q hQ).trans h,
    fun h ↦ anr_ringKrullDim_quotient_le_of_minimalPrimes _ e h⟩

/-- A point isolated in its fibre under a linear map to `ℂᵖ` has germ dimension at most `p`. -/
theorem anrem_dimension_le_of_isolated_linear {n p : ℕ} {C : Set (Fin n → ℂ)} {y : Fin n → ℂ}
    (hy : y ∈ C) (hloc : anrem_LocEq C y) (L : (Fin n → ℂ) →L[ℂ] (Fin p → ℂ))
    (hiso : ∀ᶠ z in 𝓝 y, z ∈ C → L z = L y → z = y) :
    adim2_dimension n (adim2_germ n C y) ≤ p := by
  rcases n with _ | N
  · refine (anrem_dimension_le_zero_of_isolated (Eventually.of_forall fun z _ ↦
      Subsingleton.elim z y)).trans ?_
    exact_mod_cast Nat.zero_le p
  rcases p with _ | d
  · refine anrem_dimension_le_zero_of_isolated ?_
    filter_upwards [hiso] with z hz hzC
    exact hz hzC (Subsingleton.elim _ _)
  obtain ⟨U, hU, hyU, m, f, hf, hUC⟩ := hloc
  refine (anrem_dimension_le_iff C y _).2 fun Q hQ ↦ ?_
  obtain ⟨θ, hθ, -⟩ := anr_finpar N d C y hy U hU hyU m f hf hUC L hiso Q hQ
  exact adim9b_dimension_le_of_finite_parameters (N + 1) (d + 1) Q θ hθ

/-- **Finite linear maps do not lower dimension.** If `y` is isolated in its fibre under a
linear map `L`, every minimal prime of the germ of `C` at `y` has dimension at most that of the
germ at `L y` of any set containing the image of `C` near `y`. -/
theorem anrem_minimalPrime_le_image {n p : ℕ} {C : Set (Fin n → ℂ)} {y : Fin n → ℂ}
    (hy : y ∈ C) (hloc : anrem_LocEq C y) (L : (Fin n → ℂ) →L[ℂ] (Fin p → ℂ))
    (hiso : ∀ᶠ z in 𝓝 y, z ∈ C → L z = L y → z = y) (S : Set (Fin p → ℂ))
    (hS : ∀ᶠ z in 𝓝 y, z ∈ C → L z ∈ S) (Q : Ideal (AnalyticGerm n))
    (hQ : Q ∈ (adim2_ideal n (adim2_germ n C y)).minimalPrimes) :
    ringKrullDim (AnalyticGerm n ⧸ Q) ≤ adim2_dimension p (adim2_germ p S (L y)) := by
  rcases n with _ | N
  · have h0 : ringKrullDim (AnalyticGerm 0 ⧸ Q) ≤ 0 := by
      have := (anrem_dimension_le_iff C y 0).1 (anrem_dimension_le_zero_of_isolated
        (Eventually.of_forall fun z _ ↦ Subsingleton.elim z y)) Q hQ
      exact this
    refine h0.trans ?_
    have hne : adim2_ideal p (adim2_germ p S (L y)) ≠ ⊤ := by
      have hyS : L y ∈ S := hS.self_of_nhds hy
      exact adim9b_germ_ideal_ne_top p S (L y) hyS
    have : Nontrivial (AnalyticGerm p ⧸ adim2_ideal p (adim2_germ p S (L y))) :=
      Ideal.Quotient.nontrivial_iff.2 hne
    exact ringKrullDim_nonneg_of_nontrivial
  rcases p with _ | d
  · have h0 : ringKrullDim (AnalyticGerm (N + 1) ⧸ Q) ≤ 0 :=
      (anrem_dimension_le_iff C y 0).1 (anrem_dimension_le_zero_of_isolated (by
        filter_upwards [hiso] with z hz hzC
        exact hz hzC (Subsingleton.elim _ _))) Q hQ
    refine h0.trans ?_
    have hyS : L y ∈ S := hS.self_of_nhds hy
    have : Nontrivial (AnalyticGerm 0 ⧸ adim2_ideal 0 (adim2_germ 0 S (L y))) :=
      Ideal.Quotient.nontrivial_iff.2 (adim9b_germ_ideal_ne_top 0 S (L y) hyS)
    exact ringKrullDim_nonneg_of_nontrivial
  obtain ⟨U, hU, hyU, m, f, hf, hUC⟩ := hloc
  obtain ⟨θ, hθ, hcomp⟩ := anr_finpar N d C y hy U hU hyU m f hf hUC L hiso Q hQ
  have hQp : Q.IsPrime := hQ.1.1
  have hIQ := hQ.1.2
  have hfin : (RingHom.kerLift θ).Finite :=
    RingHom.Finite.of_comp_finite (f := Ideal.Quotient.mk (RingHom.ker θ)) hθ
  have heq := adim9_ringKrullDim_eq_of_finite_injective _ hfin (RingHom.kerLift_injective θ)
  rw [← heq]
  refine anr_dim_le_of_le fun a ha ↦ ?_
  obtain ⟨h, hh, hha⟩ := a.2
  have hb : AnalyticAt ℂ (fun z ↦ h (L (y + z) - L y)) 0 :=
    hh.comp_of_eq ((L.analyticAt _).comp_of_eq (analyticAt_const.add analyticAt_id) rfl
      |>.sub analyticAt_const) (by simp)
  let b : AnalyticGerm (N + 1) := ⟨Germ.ofFun (fun z ↦ h (L (y + z) - L y)), _, hb, rfl⟩
  rw [RingHom.mem_ker, hcomp a h hh hha b rfl, Ideal.Quotient.eq_zero_iff_mem]
  refine hIQ ?_
  rw [anrem_mem_ideal_iff C y b _ rfl]
  rw [anrem_mem_ideal_iff S (L y) a h hha] at ha
  have ht : Tendsto (fun z : Fin (N + 1) → ℂ ↦ y + z) (𝓝 0) (𝓝 y) := by
    simpa using (tendsto_id (x := 𝓝 (0 : Fin (N + 1) → ℂ))).const_add y
  have hLt : Tendsto (fun z : Fin (N + 1) → ℂ ↦ L (y + z) - L y) (𝓝 0) (𝓝 0) := by
    have := ((L.continuous.tendsto y).comp ht).sub_const (L y)
    simpa using this
  filter_upwards [ht.eventually hS, hLt.eventually ha] with z h1 h2 hzC
  have := h2 (by rw [add_sub_cancel]; exact h1 hzC)
  exact this


/-! ### Hausdorff dimension bounds -/

/-- Germ dimension of a locally analytic set is bounded by half the Hausdorff dimension of any
neighbourhood piece. -/
theorem anrem_dimension_le_of_dimH {p : ℕ} {S : Set (Fin p → ℂ)} {b : Fin p → ℂ}
    (hloc : anrem_LocEq S b) {O : Set (Fin p → ℂ)} (hO : O ∈ 𝓝 b) (e : ℕ)
    (hdim : dimH (S ∩ O) ≤ ((2 * e : ℕ) : ENNReal)) :
    adim2_dimension p (adim2_germ p S b) ≤ e := by
  refine (anrem_dimension_le_iff S b _).2 fun Q hQ ↦ ?_
  obtain ⟨U, hU, hbU, m, f, hf, hUS⟩ := hloc
  classical
  have hsub : adim2_zeroSet p Q ≤ adim2_germ p S b := by
    refine adim9b_zeroSet_le_germ_of_equations Q S b (Finset.univ.image f)
      (fun h hh ↦ ?_) ?_ (fun h hh ↦ ?_)
    · obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hh
      exact hf j b hbU
    · filter_upwards [hU.mem_nhds hbU] with z hz
      rw [hUS z hz]
      simp
    · obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hh
      refine hQ.1.2 ?_
      rw [anrem_mem_ideal_iff S b _ _ rfl]
      have ht : Tendsto (fun z : Fin p → ℂ ↦ b + z) (𝓝 0) (𝓝 b) := by
        simpa using (tendsto_id (x := 𝓝 (0 : Fin p → ℂ))).const_add b
      filter_upwards [ht.eventually (hU.mem_nhds hbU)] with z hz hzS
      exact (hUS _ hz).1 hzS j
  have hsub' : adim2_zeroSet p Q ≤ adim2_germ p {v | b + v ∈ S ∩ O} 0 := by
    have : adim2_germ p {v | b + v ∈ S ∩ O} 0 = adim2_germ p (S ∩ O) b := by
      unfold adim2_germ; congr 1; funext z; simp
    rw [this, anrem_germ_inter_nhds S O b hO]
    exact hsub
  refine adim9b_prime_dimension_le_of_dimH p e _ Q hQ.1.1 hsub' ?_
  have : {v | b + v ∈ S ∩ O} = (fun v ↦ b + v) ⁻¹' (S ∩ O) := rfl
  rw [this]
  exact ((isometry_add_left b).antilipschitzWith.dimH_preimage_le (S ∩ O)).trans hdim


/-- Hausdorff dimension of a locally analytic piece of dimension at most `e`. -/
theorem anrem_dimH_le {n : ℕ} (C V : Set (Fin n → ℂ)) (hV : IsOpen V) (e : ℕ)
    (h : ∀ z ∈ C ∩ V, anrem_LocEq C z ∧ adim2_dimension n (adim2_germ n C z) ≤ e) :
    dimH (C ∩ V) ≤ ((2 * e : ℕ) : ENNReal) := by
  rcases n with _ | N
  · rw [(Set.subsingleton_of_subsingleton : (C ∩ V).Subsingleton).dimH_zero]
    exact zero_le
  refine adim9_analytic_dimH_le N e (C ∩ V) (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · obtain ⟨U, hU, hxU, m, f, hf, hUC⟩ := (h x hx).1
    refine ⟨U ∩ V, hU.inter hV, ⟨hxU, hx.2⟩, m, f, fun j ↦ (hf j).mono inter_subset_left,
      fun z hz ↦ ?_⟩
    rw [← hUC z hz.1]
    exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, hz.2⟩⟩
  · rw [anrem_germ_inter_nhds C V x (hV.mem_nhds hx.2)]
    exact (anrem_dimension_le_iff C x _).1 (h x hx).2

/-- **Linear images do not raise dimension.** -/
theorem anrem_dimension_image_le {n p : ℕ} {S : Set (Fin p → ℂ)} {b : Fin p → ℂ}
    (hloc : anrem_LocEq S b) {O : Set (Fin p → ℂ)} (hO : O ∈ 𝓝 b)
    (C V : Set (Fin n → ℂ)) (hV : IsOpen V) (L : (Fin n → ℂ) →L[ℂ] (Fin p → ℂ))
    (hSO : S ∩ O ⊆ L '' (C ∩ V)) (e : ℕ)
    (h : ∀ z ∈ C ∩ V, anrem_LocEq C z ∧ adim2_dimension n (adim2_germ n C z) ≤ e) :
    adim2_dimension p (adim2_germ p S b) ≤ e :=
  anrem_dimension_le_of_dimH hloc hO e
    ((dimH_mono hSO).trans ((L.lipschitzWith.dimH_image_le _).trans (anrem_dimH_le C V hV e h)))

/-! ### Products with a Euclidean factor -/

/-- The linear map with the given blocks of coordinates. -/
def anrem_appendL {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {p q : ℕ}
    (P : E →L[ℂ] (Fin p → ℂ)) (Q : E →L[ℂ] (Fin q → ℂ)) : E →L[ℂ] (Fin (p + q) → ℂ) :=
  ContinuousLinearMap.pi fun i ↦ Fin.addCases (motive := fun _ ↦ E →L[ℂ] ℂ)
    (fun i ↦ (ContinuousLinearMap.proj i).comp P) (fun j ↦ (ContinuousLinearMap.proj j).comp Q) i

@[simp] theorem anrem_appendL_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {p q : ℕ} (P : E →L[ℂ] (Fin p → ℂ)) (Q : E →L[ℂ] (Fin q → ℂ)) (x : E) :
    anrem_appendL P Q x = Fin.append (P x) (Q x) := by
  funext i
  refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) i <;> simp [anrem_appendL]

theorem anrem_append_inj {p q : ℕ} {a a' : Fin p → ℂ} {b b' : Fin q → ℂ}
    (h : Fin.append a b = Fin.append a' b') : a = a' ∧ b = b' := by
  constructor
  · simpa using congrArg anrem_fst h
  · simpa using congrArg anrem_snd h

/-- Local equations of a product with `ℂʲ`. -/
theorem anrem_locEq_prod {m j : ℕ} {A : Set (Fin m → ℂ)} {b : Fin m → ℂ} (hA : anrem_LocEq A b)
    (s : Fin j → ℂ) : anrem_LocEq (anrem_fst ⁻¹' A : Set (Fin (m + j) → ℂ)) (Fin.append b s) := by
  obtain ⟨U, hU, hbU, k, f, hf, hUA⟩ := hA
  refine ⟨anrem_fst ⁻¹' U, hU.preimage anrem_fst.continuous, by simpa using hbU, k,
    fun i u ↦ f i (anrem_fst u), fun i u hu ↦ (hf i _ hu).comp (anrem_fst.analyticAt u),
    fun u hu ↦ hUA _ hu⟩

/-- **The dimension of a product with `ℂʲ`** is at most the dimension plus `j`. -/
theorem anrem_dimension_prod_le {m j : ℕ} {A : Set (Fin m → ℂ)} {b : Fin m → ℂ} (hb : b ∈ A)
    {U : Set (Fin m → ℂ)} (hU : IsOpen U) (hbU : b ∈ U) {k : ℕ} {f : Fin k → (Fin m → ℂ) → ℂ}
    (hf : ∀ i, AnalyticOnNhd ℂ (f i) U) (hUA : ∀ z ∈ U, (z ∈ A ↔ ∀ i, f i z = 0)) (e : ℕ)
    (hdim : ∀ z ∈ A ∩ U, adim2_dimension m (adim2_germ m A z) ≤ e) (s : Fin j → ℂ) :
    adim2_dimension (m + j) (adim2_germ (m + j) (anrem_fst ⁻¹' A) (Fin.append b s)) ≤
      ((e + j : ℕ) : WithBot ℕ∞) := by
  have hloc : ∀ y ∈ A ∩ U, ∃ U' : Set (Fin m → ℂ), IsOpen U' ∧ y ∈ U' ∧ ∃ (k' : ℕ)
      (f' : Fin k' → (Fin m → ℂ) → ℂ), (∀ i, AnalyticOnNhd ℂ (f' i) U') ∧
        ∀ z ∈ U', (z ∈ A ∩ U ↔ ∀ i, f' i z = 0) := by
    intro y hy
    refine ⟨U, hU, hy.2, k, f, hf, fun z hz ↦ ?_⟩
    rw [← hUA z hz]
    exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, hz⟩⟩
  obtain ⟨lam, hlam⟩ := anr_slice (fun _ : Unit ↦ A ∩ U) (fun _ ↦ b) (fun _ ↦ e)
    (fun _ ↦ hloc) (fun _ y hy ↦ by
      rw [anrem_germ_inter_nhds A U y (hU.mem_nhds hy.2)]
      exact (anrem_dimension_le_iff A y _).1 (hdim y hy)) e
  have hiso0 : ∀ᶠ z in 𝓝 b, z ∈ A ∩ U ∩ {z | lam z = lam b} → z = b := by
    refine anr_isolated_of_dims _ b ⟨⟨hb, hbU⟩, rfl⟩ fun Q hQ ↦ ?_
    have := hlam () b ⟨⟨hb, hbU⟩, rfl⟩ Q hQ
    simpa using this
  set Λ : (Fin (m + j) → ℂ) →L[ℂ] (Fin (e + j) → ℂ) := anrem_appendL (lam.comp anrem_fst) anrem_snd
  refine anrem_dimension_le_of_isolated_linear (by simpa using hb) (anrem_locEq_prod
    ⟨U, hU, hbU, k, f, hf, hUA⟩ s) Λ ?_
  have ht : Tendsto (anrem_fst : (Fin (m + j) → ℂ) → (Fin m → ℂ)) (𝓝 (Fin.append b s)) (𝓝 b) := by
    simpa using anrem_fst.continuous.tendsto (Fin.append b s)
  filter_upwards [ht.eventually hiso0, ht.eventually (hU.mem_nhds hbU)] with u h1 h2 huA hΛ
  simp only [Λ, anrem_appendL_apply, ContinuousLinearMap.comp_apply, anrem_fst_append,
    anrem_snd_append] at hΛ
  obtain ⟨hlamu, hsu⟩ := anrem_append_inj hΛ
  have hfu : anrem_fst u = b := h1 ⟨⟨huA, h2⟩, hlamu⟩
  rw [← anrem_append_fst_snd u, hfu, hsu]


/-! ### Openness of finite linear maps on components of full dimension -/

/-- The zero germ of finitely many germs, read on representatives. -/
theorem anrem_finset_inf_zero {n : ℕ} (s : Finset (AnalyticGerm n))
    (rep : AnalyticGerm n → (Fin n → ℂ) → ℂ) (hrep : ∀ a, Germ.ofFun (rep a) = a.val) :
    s.inf (adim2_zero n) = Germ.ofFun (fun z ↦ ∀ a ∈ s, rep a z = 0) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.inf_empty, Finset.notMem_empty, IsEmpty.forall_iff, implies_true]
    rfl
  | insert a s ha ih =>
    rw [Finset.inf_insert, ih]
    have : adim2_zero n a = Germ.ofFun (fun z ↦ rep a z = 0) := by
      unfold adim2_zero; rw [← hrep a]; rfl
    rw [this]
    apply Germ.coe_eq.2
    exact Eventually.of_forall fun z ↦ by simp

/-- **Openness.** At a point isolated in its fibre under a linear map to `ℂᵖ`, where the germ has
dimension at least `p`, the set is mapped onto a neighbourhood of the image point, already by
arbitrarily small pieces. -/
theorem anrem_open_image {n p : ℕ} {C : Set (Fin n → ℂ)} {w : Fin n → ℂ} (hw : w ∈ C)
    (hloc : anrem_LocEq C w) (π : (Fin n → ℂ) →L[ℂ] (Fin p → ℂ))
    (hiso : ∀ᶠ z in 𝓝 w, z ∈ C → π z = π w → z = w)
    (hdim : (p : WithBot ℕ∞) ≤ adim2_dimension n (adim2_germ n C w)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in 𝓝 (π w), ∃ z ∈ C, dist z w < ε ∧ π z = t := by
  classical
  rcases p with _ | d
  · exact Eventually.of_forall fun t ↦ ⟨w, hw, by simpa using hε, Subsingleton.elim _ _⟩
  rcases n with _ | N
  · exfalso
    have h0 := anrem_dimension_le_zero_of_isolated (C := C) (y := w)
      (Eventually.of_forall fun z _ ↦ Subsingleton.elim z w)
    have h1 : ((d + 1 : ℕ) : WithBot ℕ∞) ≤ ((0 : ℕ) : WithBot ℕ∞) := hdim.trans h0
    have h2 : d + 1 ≤ 0 := by exact_mod_cast h1
    omega
  have hle := anrem_dimension_le_of_isolated_linear hw hloc π hiso
  -- a minimal prime of full dimension
  obtain ⟨P, hPmin, hPdim⟩ : ∃ P ∈ (adim2_ideal (N + 1) (adim2_germ (N + 1) C w)).minimalPrimes,
      ringKrullDim (AnalyticGerm (N + 1) ⧸ P) = ((d + 1 : ℕ) : WithBot ℕ∞) := by
    by_contra hcon
    push Not at hcon
    have : adim2_dimension (N + 1) (adim2_germ (N + 1) C w) ≤ (d : WithBot ℕ∞) := by
      refine (anrem_dimension_le_iff C w _).2 fun Q hQ ↦ ?_
      exact anr_le_of_lt_succ _ d (lt_of_le_of_ne ((anrem_dimension_le_iff C w _).1 hle Q hQ)
        (hcon Q hQ))
    have h1 : ((d + 1 : ℕ) : WithBot ℕ∞) ≤ ((d : ℕ) : WithBot ℕ∞) := hdim.trans this
    have h2 : d + 1 ≤ d := by exact_mod_cast h1
    omega
  have hPprime : P.IsPrime := hPmin.1.1
  -- generators and representatives
  set gens := adim2_generators (N + 1) P
  have hspan : Ideal.span (gens : Set (AnalyticGerm (N + 1))) = P :=
    ((isNoetherianRing_iff_ideal_fg _).mp (adim_noetherian (N + 1)) P).choose_spec
  let g : Fin gens.card → AnalyticGerm (N + 1) := fun j ↦ (gens.equivFin.symm j).1
  have hrange : range g = (gens : Set (AnalyticGerm (N + 1))) := by
    ext a
    constructor
    · rintro ⟨j, rfl⟩; exact (gens.equivFin.symm j).2
    · intro ha; exact ⟨gens.equivFin ⟨a, ha⟩, by simp [g]⟩
  have hgen : Ideal.span (range g) = P := by rw [hrange, hspan]
  let rep : AnalyticGerm (N + 1) → (Fin (N + 1) → ℂ) → ℂ := fun a ↦ a.2.choose
  have hrepa : ∀ a, AnalyticAt ℂ (rep a) 0 := fun a ↦ a.2.choose_spec.1
  have hrep : ∀ a, Germ.ofFun (rep a) = a.val := fun a ↦ a.2.choose_spec.2
  let φ : Fin gens.card → (Fin (N + 1) → ℂ) → ℂ := fun j ↦ rep (g j)
  obtain ⟨U₀, hU₀sub, hU₀, h0U₀⟩ := eventually_nhds_iff.1
    (eventually_all.2 fun j ↦ (hrepa (g j)).eventually_analyticAt)
  have hφ : ∀ j, AnalyticOnNhd ℂ (φ j) U₀ := fun j z hz ↦ hU₀sub z hz j
  obtain ⟨W₁, hW₁, h0W₁, hW₁U, hpure⟩ := adim9b_local_purity (N + 1) (d + 1) gens.card P hPprime
    hPdim g hgen φ U₀ hU₀ h0U₀ hφ (fun j ↦ hrep (g j))
  -- the zero set of the prime lies in the translated set
  obtain ⟨U, hU, hwU, m, f, hf, hUC⟩ := hloc
  have hsub : adim2_zeroSet (N + 1) P ≤ adim2_germ (N + 1) C w := by
    refine adim9b_zeroSet_le_germ_of_equations P C w (Finset.univ.image f)
      (fun h hh ↦ ?_) ?_ (fun h hh ↦ ?_)
    · obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hh
      exact hf j w hwU
    · filter_upwards [hU.mem_nhds hwU] with z hz
      rw [hUC z hz]
      simp
    · obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hh
      refine hPmin.1.2 ?_
      rw [anrem_mem_ideal_iff C w _ _ rfl]
      have ht : Tendsto (fun z : Fin (N + 1) → ℂ ↦ w + z) (𝓝 0) (𝓝 w) := by
        simpa using (tendsto_id (x := 𝓝 (0 : Fin (N + 1) → ℂ))).const_add w
      filter_upwards [ht.eventually (hU.mem_nhds hwU)] with z hz hzC
      exact (hUC _ hz).1 hzC j
  have hzs : adim2_zeroSet (N + 1) P = Germ.ofFun (fun z ↦ ∀ j, φ j z = 0) := by
    rw [adim2_zeroSet, anrem_finset_inf_zero gens rep hrep]
    apply Germ.coe_eq.2
    refine Eventually.of_forall fun z ↦ propext ⟨fun h j ↦ h _ (gens.equivFin.symm j).2,
      fun h a ha ↦ ?_⟩
    have := h (gens.equivFin ⟨a, ha⟩)
    simpa [φ, g] using this
  rw [hzs, adim2_germ, Germ.coe_le] at hsub
  obtain ⟨W₂, hW₂sub, hW₂, h0W₂⟩ := eventually_nhds_iff.1 hsub
  -- the component through the point
  have hφ0 : ∀ j, φ j 0 = 0 := by
    intro j
    have hgP : g j ∈ P := hgen ▸ Ideal.subset_span ⟨j, rfl⟩
    have hnu : ¬ IsUnit (g j) := fun hu ↦ hPprime.ne_top (Ideal.eq_top_of_isUnit_mem _ hgP hu)
    rw [analyticGerm_isUnit_iff, not_not] at hnu
    change (g j).1.value = 0 at hnu
    rw [← hrep (g j)] at hnu
    exact hnu
  set W := W₁ ∩ W₂ ∩ Metric.ball 0 ε ∩ U₀
  have hW : IsOpen W := ((hW₁.inter hW₂).inter Metric.isOpen_ball).inter hU₀
  have h0W : (0 : Fin (N + 1) → ℂ) ∈ W := ⟨⟨⟨h0W₁, h0W₂⟩, Metric.mem_ball_self hε⟩, h0U₀⟩
  set CP := {z | ∀ j, φ j z = 0} ∩ W
  have hCP0 : (0 : Fin (N + 1) → ℂ) ∈ CP := ⟨hφ0, h0W⟩
  have hgermCP : adim2_germ (N + 1) CP 0 = adim2_germ (N + 1) {z | ∀ j, φ j z = 0} 0 :=
    anrem_germ_inter_nhds _ W 0 (hW.mem_nhds h0W)
  have hT0 : Tendsto (fun z : Fin (N + 1) → ℂ ↦ w + z) (𝓝 0) (𝓝 w) := by
    simpa using (tendsto_id (x := 𝓝 (0 : Fin (N + 1) → ℂ))).const_add w
  have honto := adim9_local_onto N d CP 0 hCP0 W hW h0W gens.card φ
    (fun j ↦ (hφ j).mono fun z hz ↦ hz.2)
    (fun z hz ↦ ⟨fun h ↦ h.1, fun h ↦ ⟨h, hz⟩⟩)
    (by rw [hgermCP]; exact hpure 0 h0W₁ hφ0) π (by
      filter_upwards [hT0.eventually hiso] with y hy hyC hπy
      have hwy : w + y ∈ C := by
        simpa using hW₂sub y hyC.2.1.1.2 hyC.1
      have : w + y = w := hy hwy (by rw [map_add, hπy, map_zero, add_zero])
      simpa using this)
  have hπt : Tendsto (fun t ↦ t - π w) (𝓝 (π w)) (𝓝 (π 0)) := by
    rw [map_zero]
    simpa using (tendsto_id (x := 𝓝 (π w))).sub_const (π w)
  filter_upwards [hπt.eventually honto] with t ht
  obtain ⟨y, hyC, hπy⟩ := ht
  refine ⟨w + y, by simpa using hW₂sub y hyC.2.1.1.2 hyC.1, ?_, ?_⟩
  · rw [dist_eq_norm, add_sub_cancel_left]
    simpa using hyC.2.1.2
  · rw [map_add, hπy]; abel


/-! ### More germ facts -/

/-- Germs of a translated set. -/
theorem anrem_germ_translate {n : ℕ} (A : Set (Fin n → ℂ)) (y y' : Fin n → ℂ) :
    adim2_germ n {v | y + v ∈ A} (y' - y) = adim2_germ n A y' := by
  unfold adim2_germ; congr 1; funext z
  simp only [mem_ofPred_eq]
  rw [show y + (y' - y + z) = y' + z by abel]

/-- Germ dimension is monotone under eventual inclusion. -/
theorem anrem_dimension_mono {n : ℕ} {A B : Set (Fin n → ℂ)} {y : Fin n → ℂ}
    (h : ∀ᶠ z in 𝓝 y, z ∈ A → z ∈ B) :
    adim2_dimension n (adim2_germ n A y) ≤ adim2_dimension n (adim2_germ n B y) := by
  refine anr_dim_le_of_le fun a ha ↦ ?_
  obtain ⟨φ, -, hφ⟩ := a.2
  rw [anrem_mem_ideal_iff B y a φ hφ] at ha
  rw [anrem_mem_ideal_iff A y a φ hφ]
  have ht : Tendsto (fun z : Fin n → ℂ ↦ y + z) (𝓝 0) (𝓝 y) := by
    simpa using (tendsto_id (x := 𝓝 (0 : Fin n → ℂ))).const_add y
  filter_upwards [ht.eventually h, ha] with z h1 h2 hz
  exact h2 (h1 hz)

/-- A minimal prime attains a lower bound on the germ dimension. -/
theorem anrem_exists_minimalPrime_ge {n : ℕ} {A : Set (Fin n → ℂ)} {y : Fin n → ℂ} {e : ℕ}
    (h : (e : WithBot ℕ∞) ≤ adim2_dimension n (adim2_germ n A y)) :
    ∃ Q ∈ (adim2_ideal n (adim2_germ n A y)).minimalPrimes,
      (e : WithBot ℕ∞) ≤ ringKrullDim (AnalyticGerm n ⧸ Q) := by
  rcases e with _ | e
  · have hne : adim2_ideal n (adim2_germ n A y) ≠ ⊤ := by
      intro htop
      have : Subsingleton (AnalyticGerm n ⧸ adim2_ideal n (adim2_germ n A y)) := by
        rw [htop]; infer_instance
      have hbot : adim2_dimension n (adim2_germ n A y) = ⊥ := ringKrullDim_eq_bot_of_subsingleton
      rw [hbot] at h
      exact absurd h (by simp)
    obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal _ hne
    have := hM.isPrime
    obtain ⟨Q, hQ, -⟩ := Ideal.exists_minimalPrimes_le hIM
    refine ⟨Q, hQ, ?_⟩
    have := hQ.1.1
    have : Nontrivial (AnalyticGerm n ⧸ Q) := Ideal.Quotient.nontrivial_iff.2 hQ.1.1.ne_top
    exact_mod_cast ringKrullDim_nonneg_of_nontrivial
  · by_contra hcon
    push Not at hcon
    have : adim2_dimension n (adim2_germ n A y) ≤ (e : WithBot ℕ∞) :=
      (anrem_dimension_le_iff A y _).2 fun Q hQ ↦ anr_le_of_lt_succ _ e (hcon Q hQ)
    have h2 := h.trans this
    have h3 : e + 1 ≤ e := by exact_mod_cast h2
    omega

/-- **Upper semicontinuity of germ dimension.** -/
theorem anrem_dimension_upper {n : ℕ} {A : Set (Fin n → ℂ)} {y : Fin n → ℂ}
    (hloc : anrem_LocEq A y) {e : ℕ} (h : adim2_dimension n (adim2_germ n A y) ≤ e) :
    ∀ᶠ z in 𝓝 y, adim2_dimension n (adim2_germ n A z) ≤ e := by
  rcases n with _ | N
  · exact Eventually.of_forall fun z ↦ by rwa [Subsingleton.elim z y]
  obtain ⟨U, hU, hyU, m, f, hf, hUA⟩ := hloc
  set A' : Set (Fin (N + 1) → ℂ) := {v | y + v ∈ A}
  have hU' : IsOpen ((fun v ↦ y + v) ⁻¹' U) := hU.preimage (continuous_const.add continuous_id)
  obtain ⟨W, hW, h0W, -, hWdim⟩ := adim9b_component_dimension_upper_near N e m A'
    ((fun v ↦ y + v) ⁻¹' U) hU' (by simpa using hyU) (fun j v ↦ f j (y + v))
    (fun j v hv ↦ (hf j _ hv).comp_of_eq (analyticAt_const.add analyticAt_id) rfl)
    (fun v hv ↦ hUA _ hv)
    (by
      have : adim2_germ (N + 1) A' 0 = adim2_germ (N + 1) A y := by
        rw [← anrem_germ_translate A y y, sub_self]
      rw [this]; exact (anrem_dimension_le_iff A y _).1 h)
  have ht : Tendsto (fun z : Fin (N + 1) → ℂ ↦ z - y) (𝓝 y) (𝓝 0) := by
    simpa using (tendsto_id (x := 𝓝 y)).sub_const y
  filter_upwards [ht.eventually (hW.mem_nhds h0W)] with z hz
  rw [← anrem_germ_translate A y z]
  exact (anrem_dimension_le_iff _ _ _).2 (hWdim _ hz)


/-- A set all of whose minimal primes at a point have dimension `e` has germ dimension `e` there. -/
theorem anrem_dimension_eq_of_pure {n : ℕ} {C : Set (Fin n → ℂ)} {z : Fin n → ℂ} (hz : z ∈ C)
    {e : ℕ} (h : ∀ Q ∈ (adim2_ideal n (adim2_germ n C z)).minimalPrimes,
      ringKrullDim (AnalyticGerm n ⧸ Q) = e) :
    adim2_dimension n (adim2_germ n C z) = e := by
  refine le_antisymm ((anrem_dimension_le_iff C z _).2 fun Q hQ ↦ (h Q hQ).le) ?_
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal _ (adim9b_germ_ideal_ne_top n C z hz)
  have := hM.isPrime
  obtain ⟨Q, hQ, -⟩ := Ideal.exists_minimalPrimes_le hIM
  rw [← h Q hQ]
  exact anr_minimal_le_dim _ Q hQ

/-- **A pure component through a point.** For a minimal prime of dimension `e` of the germ of a
locally analytic set, a representative of its zero set lies in the set near the point, contains
the point, has local equations near it and has germ dimension `e` at all its points near it. -/
theorem anrem_component {n : ℕ} {A : Set (Fin n → ℂ)} {y : Fin n → ℂ} (hy : y ∈ A)
    (hloc : anrem_LocEq A y) {Q : Ideal (AnalyticGerm n)}
    (hQ : Q ∈ (adim2_ideal n (adim2_germ n A y)).minimalPrimes) {e : ℕ}
    (he : ringKrullDim (AnalyticGerm n ⧸ Q) = e) :
    ∃ C : Set (Fin n → ℂ), y ∈ C ∧ (∀ᶠ z in 𝓝 y, z ∈ C → z ∈ A) ∧
      (∀ᶠ z in 𝓝 y, anrem_LocEq C z) ∧
      (∀ᶠ z in 𝓝 y, z ∈ C → ∀ Q' ∈ (adim2_ideal n (adim2_germ n C z)).minimalPrimes,
        ringKrullDim (AnalyticGerm n ⧸ Q') = e) ∧
      adim2_germ n C y = adim2_zeroSet n Q := by
  classical
  rcases n with _ | N
  · refine ⟨{y}, rfl, Eventually.of_forall fun z hz ↦ (Subsingleton.elim z y) ▸ hy,
      Eventually.of_forall fun z ↦ ?_, Eventually.of_forall fun z hz ↦ ?_, ?_⟩
    · refine ⟨univ, isOpen_univ, mem_univ _, 0, Fin.elim0, fun j ↦ j.elim0, fun x _ ↦ ?_⟩
      simp [Subsingleton.elim x y]
    · intro Q' hQ'
      have hQA : ringKrullDim (AnalyticGerm 0 ⧸ Q) ≤ 0 := by
        have := (anrem_dimension_le_iff A y 0).1 (anrem_dimension_le_zero_of_isolated
          (Eventually.of_forall fun z _ ↦ Subsingleton.elim z y)) Q hQ
        exact this
      have he0 : e = 0 := by
        rw [he] at hQA
        have : e ≤ 0 := by exact_mod_cast hQA
        omega
      rw [he0]
      refine le_antisymm ((anrem_dimension_le_iff _ _ _).1 (anrem_dimension_le_zero_of_isolated
        (Eventually.of_forall fun x _ ↦ Subsingleton.elim x z)) Q' hQ') ?_
      have : Nontrivial (AnalyticGerm 0 ⧸ Q') := Ideal.Quotient.nontrivial_iff.2 hQ'.1.1.ne_top
      exact_mod_cast ringKrullDim_nonneg_of_nontrivial
    · -- in `ℂ⁰` every nonempty germ is the whole space
      have hQprime : Q.IsPrime := hQ.1.1
      have htop : adim2_germ 0 {y} y = ⊤ := by
        apply Germ.coe_eq.2
        exact Eventually.of_forall fun z ↦ propext ⟨fun _ ↦ trivial, fun _ ↦
          Subsingleton.elim _ _⟩
      rw [htop]
      refine le_antisymm ((adim2_galois 0 ⊤ Q).2 fun a ha ↦ ?_) le_top
      obtain ⟨φ, -, hφ⟩ := a.2
      have hnu : ¬ IsUnit a := fun hu ↦ hQprime.ne_top (Ideal.eq_top_of_isUnit_mem _ ha hu)
      rw [analyticGerm_isUnit_iff, not_not] at hnu
      change a.1.value = 0 at hnu
      rw [← hφ] at hnu
      change ⊤ ≤ a.val.map (· = 0)
      rw [← hφ, Germ.map_coe]
      exact Eventually.of_forall fun z _ ↦ by
        change φ z = 0
        rw [Subsingleton.elim z 0]; exact hnu
  have hPprime : Q.IsPrime := hQ.1.1
  set gens := adim2_generators (N + 1) Q
  have hspan : Ideal.span (gens : Set (AnalyticGerm (N + 1))) = Q :=
    ((isNoetherianRing_iff_ideal_fg _).mp (adim_noetherian (N + 1)) Q).choose_spec
  let g : Fin gens.card → AnalyticGerm (N + 1) := fun j ↦ (gens.equivFin.symm j).1
  have hrange : range g = (gens : Set (AnalyticGerm (N + 1))) := by
    ext a
    constructor
    · rintro ⟨j, rfl⟩; exact (gens.equivFin.symm j).2
    · intro ha; exact ⟨gens.equivFin ⟨a, ha⟩, by simp [g]⟩
  have hgen : Ideal.span (range g) = Q := by rw [hrange, hspan]
  let rep : AnalyticGerm (N + 1) → (Fin (N + 1) → ℂ) → ℂ := fun a ↦ a.2.choose
  have hrepa : ∀ a, AnalyticAt ℂ (rep a) 0 := fun a ↦ a.2.choose_spec.1
  have hrep : ∀ a, Germ.ofFun (rep a) = a.val := fun a ↦ a.2.choose_spec.2
  let φ : Fin gens.card → (Fin (N + 1) → ℂ) → ℂ := fun j ↦ rep (g j)
  obtain ⟨U₀, hU₀sub, hU₀, h0U₀⟩ := eventually_nhds_iff.1
    (eventually_all.2 fun j ↦ (hrepa (g j)).eventually_analyticAt)
  have hφ : ∀ j, AnalyticOnNhd ℂ (φ j) U₀ := fun j z hz ↦ hU₀sub z hz j
  obtain ⟨W₁, hW₁, h0W₁, hW₁U, hpure⟩ := adim9b_local_purity (N + 1) e gens.card Q hPprime
    he g hgen φ U₀ hU₀ h0U₀ hφ (fun j ↦ hrep (g j))
  obtain ⟨U, hU, hyU, m, f, hf, hUA⟩ := hloc
  have hsub : adim2_zeroSet (N + 1) Q ≤ adim2_germ (N + 1) A y := by
    refine adim9b_zeroSet_le_germ_of_equations Q A y (Finset.univ.image f)
      (fun h hh ↦ ?_) ?_ (fun h hh ↦ ?_)
    · obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hh
      exact hf j y hyU
    · filter_upwards [hU.mem_nhds hyU] with z hz
      rw [hUA z hz]
      simp
    · obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hh
      refine hQ.1.2 ?_
      rw [anrem_mem_ideal_iff A y _ _ rfl]
      have ht : Tendsto (fun z : Fin (N + 1) → ℂ ↦ y + z) (𝓝 0) (𝓝 y) := by
        simpa using (tendsto_id (x := 𝓝 (0 : Fin (N + 1) → ℂ))).const_add y
      filter_upwards [ht.eventually (hU.mem_nhds hyU)] with z hz hzC
      exact (hUA _ hz).1 hzC j
  have hzs : adim2_zeroSet (N + 1) Q = Germ.ofFun (fun z ↦ ∀ j, φ j z = 0) := by
    rw [adim2_zeroSet, anrem_finset_inf_zero gens rep hrep]
    apply Germ.coe_eq.2
    refine Eventually.of_forall fun z ↦ propext ⟨fun h j ↦ h _ (gens.equivFin.symm j).2,
      fun h a ha ↦ ?_⟩
    have := h (gens.equivFin ⟨a, ha⟩)
    simpa [φ, g] using this
  rw [hzs, adim2_germ, Germ.coe_le] at hsub
  have hφ0 : ∀ j, φ j 0 = 0 := by
    intro j
    have hgP : g j ∈ Q := hgen ▸ Ideal.subset_span ⟨j, rfl⟩
    have hnu : ¬ IsUnit (g j) := fun hu ↦ hPprime.ne_top (Ideal.eq_top_of_isUnit_mem _ hgP hu)
    rw [analyticGerm_isUnit_iff, not_not] at hnu
    change (g j).1.value = 0 at hnu
    rw [← hrep (g j)] at hnu
    exact hnu
  set C' : Set (Fin (N + 1) → ℂ) := {v | v ∈ W₁ ∧ ∀ j, φ j v = 0}
  set C : Set (Fin (N + 1) → ℂ) := {z | z - y ∈ C'}
  have hCt : ∀ z, adim2_germ (N + 1) C z = adim2_germ (N + 1) C' (z - y) := by
    intro z
    rw [← anrem_germ_translate C y z]
    congr 1
    ext v; simp [C]
  have ht : Tendsto (fun z : Fin (N + 1) → ℂ ↦ z - y) (𝓝 y) (𝓝 0) := by
    simpa using (tendsto_id (x := 𝓝 y)).sub_const y
  refine ⟨C, ⟨by simpa using h0W₁, by simpa using hφ0⟩, ?_, ?_, ?_, ?_⟩
  · filter_upwards [ht.eventually hsub] with z hz hzC
    simpa using hz hzC.2
  · filter_upwards [ht.eventually ((hW₁.inter hU₀).mem_nhds ⟨h0W₁, h0U₀⟩)] with z hz
    refine ⟨(fun x ↦ x - y) ⁻¹' (W₁ ∩ U₀),
      (hW₁.inter hU₀).preimage (continuous_id.sub continuous_const), hz, gens.card,
      fun j x ↦ φ j (x - y), fun j x hx ↦ (hφ j _ hx.2).comp_of_eq
        (analyticAt_id.sub analyticAt_const) rfl, fun x hx ↦ ?_⟩
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨hx.1, h⟩⟩
  · filter_upwards [ht.eventually (hW₁.mem_nhds h0W₁)] with z hz hzC Q' hQ'
    rw [hCt, show adim2_germ (N + 1) C' (z - y) =
        adim2_germ (N + 1) {v | ∀ j, φ j v = 0} (z - y) from by
      rw [show C' = {v | ∀ j, φ j v = 0} ∩ W₁ by ext; simp [C', and_comm]]
      exact anrem_germ_inter_nhds _ _ _ (hW₁.mem_nhds hz)] at hQ'
    exact hpure (z - y) hz hzC.2 Q' hQ'
  · rw [hCt, sub_self, hzs]
    rw [show C' = {v | ∀ j, φ j v = 0} ∩ W₁ by ext; simp [C', and_comm]]
    rw [anrem_germ_inter_nhds _ _ _ (hW₁.mem_nhds h0W₁)]
    unfold adim2_germ
    congr 1
    funext z
    simp


/-! ### Finite unions -/

/-- Local equations of a finite union. -/
theorem anrem_locEq_biUnion {n : ℕ} {ι : Type*} (F : Finset ι) {S : ι → Set (Fin n → ℂ)}
    {z : Fin n → ℂ} (h : ∀ i ∈ F, anrem_LocEq (S i) z) :
    anrem_LocEq (⋃ i ∈ F, S i) z := by
  classical
  choose! U hU hzU m f hf hS using h
  set U₀ := ⋂ i ∈ F, U i
  have hU₀ : IsOpen U₀ := isOpen_biInter_finset fun i hi ↦ hU i hi
  have hzU₀ : z ∈ U₀ := mem_iInter₂.2 fun i hi ↦ hzU i hi
  obtain ⟨t, ht, hteq⟩ := adim9b_union_zero_equations U₀ F (fun i ↦ Finset.univ.image (f i))
    (fun i hi h hh ↦ by
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hh
      exact (hf i hi j).mono (biInter_subset_of_mem hi))
  refine ⟨U₀, hU₀, hzU₀, t.card, fun j ↦ (t.equivFin.symm j).1,
    fun j ↦ ht _ (t.equivFin.symm j).2, fun x hx ↦ ?_⟩
  have h1 : (∀ j, (t.equivFin.symm j).1 x = 0) ↔ ∀ h ∈ t, h x = 0 := by
    constructor
    · intro h' g hg
      have := h' (t.equivFin ⟨g, hg⟩)
      simpa using this
    · intro h' j; exact h' _ (t.equivFin.symm j).2
  rw [h1, hteq]
  simp only [mem_iUnion₂, Finset.mem_image, Finset.mem_univ, true_and, forall_exists_index,
    forall_apply_eq_imp_iff]
  constructor
  · rintro ⟨i, hi, hxi⟩
    exact ⟨i, hi, (hS i hi x (mem_iInter₂.1 hx i hi)).1 hxi⟩
  · rintro ⟨i, hi, hxi⟩
    exact ⟨i, hi, (hS i hi x (mem_iInter₂.1 hx i hi)).2 hxi⟩

/-- A set with local equations at a point outside it has the empty germ there. -/
theorem anrem_germ_eq_bot_of_not_mem {n : ℕ} {S : Set (Fin n → ℂ)} {z : Fin n → ℂ}
    (hloc : anrem_LocEq S z) (hz : z ∉ S) : adim2_germ n S z = ⊥ := by
  obtain ⟨U, hU, hzU, m, f, hf, hUS⟩ := hloc
  have : ¬ ∀ j, f j z = 0 := fun h' ↦ hz ((hUS z hzU).2 h')
  push Not at this
  obtain ⟨j, hj⟩ := this
  apply Germ.coe_eq.2
  have ht : Tendsto (fun v : Fin n → ℂ ↦ z + v) (𝓝 0) (𝓝 z) := by
    simpa using (tendsto_id (x := 𝓝 (0 : Fin n → ℂ))).const_add z
  filter_upwards [ht.eventually (Filter.Eventually.and (hU.mem_nhds hzU)
    ((hf j z hzU).continuousAt.eventually_ne hj))] with v hv
  refine propext ⟨fun hvS ↦ hv.2 ((hUS _ hv.1).1 hvS j), fun h ↦ h.elim⟩

/-- Minimal primes of a finite union come from the pieces. -/
theorem anrem_minimalPrimes_biUnion {n : ℕ} {ι : Type*} (F : Finset ι) (S : ι → Set (Fin n → ℂ))
    (z : Fin n → ℂ) {Q : Ideal (AnalyticGerm n)}
    (hQ : Q ∈ (adim2_ideal n (adim2_germ n (⋃ i ∈ F, S i) z)).minimalPrimes) :
    ∃ i ∈ F, Q ∈ (adim2_ideal n (adim2_germ n (S i) z)).minimalPrimes := by
  have hset : (⋃ i ∈ F, S i) = {x | ∃ i ∈ F, x ∈ S i} := by ext; simp
  rw [hset, ← adim9b_finset_sup_germ, adim9b_ideal_finset_sup] at hQ
  exact adim9b_minimalPrime_of_finset_inf F _ Q hQ


theorem anrem_quotient_dim_cases {n : ℕ} (Q : Ideal (AnalyticGerm n)) (hQ : Q.IsPrime) :
    ∃ e : ℕ, ringKrullDim (AnalyticGerm n ⧸ Q) = e := by
  have : Nontrivial (AnalyticGerm n ⧸ Q) := Ideal.Quotient.nontrivial_iff.2 hQ.ne_top
  have hle : ringKrullDim (AnalyticGerm n ⧸ Q) ≤ (n : WithBot ℕ∞) := by
    rw [← adim6_parameter_dimension n]
    exact ringKrullDim_quotient_le _
  obtain ⟨e, -, he⟩ := anr_dim_cases n hle
  exact ⟨e, he⟩

/-- **Local decomposition into pure components.** Near a point of a locally analytic set, the set
is the union of finitely many pure-dimensional sets, one for each minimal prime of its germ. -/
theorem anrem_decomp {n : ℕ} {A : Set (Fin n → ℂ)} {y : Fin n → ℂ} (hy : y ∈ A)
    (hloc : anrem_LocEq A y) :
    ∃ (F : Finset (Ideal (AnalyticGerm n))) (e : Ideal (AnalyticGerm n) → ℕ)
      (C : Ideal (AnalyticGerm n) → Set (Fin n → ℂ)),
      (∀ P, P ∈ F ↔ P ∈ (adim2_ideal n (adim2_germ n A y)).minimalPrimes) ∧
      (∀ P ∈ F, ringKrullDim (AnalyticGerm n ⧸ P) = e P) ∧
      (∀ P ∈ F, y ∈ C P ∧ adim2_germ n (C P) y = adim2_zeroSet n P) ∧
      (∀ᶠ z in 𝓝 y, ∀ P ∈ F, anrem_LocEq (C P) z) ∧
      (∀ᶠ z in 𝓝 y, ∀ P ∈ F, z ∈ C P →
        ∀ Q ∈ (adim2_ideal n (adim2_germ n (C P) z)).minimalPrimes,
          ringKrullDim (AnalyticGerm n ⧸ Q) = e P) ∧
      (∀ᶠ z in 𝓝 y, z ∈ A ↔ ∃ P ∈ F, z ∈ C P) := by
  classical
  obtain ⟨U, hU, hyU, m, f, hf, hUA⟩ := hloc
  obtain ⟨s, hs⟩ := adim9b_local_equations_of_representatives n m A y U hU hyU f hf hUA
  obtain ⟨F, hFeq, hcover⟩ := adim3_minimal_prime_cover n s
  rw [← hs] at hFeq hcover
  have hmem : ∀ P, P ∈ F ↔ P ∈ (adim2_ideal n (adim2_germ n A y)).minimalPrimes := fun P ↦ by
    rw [← hFeq]; rfl
  let e : Ideal (AnalyticGerm n) → ℕ := fun P ↦
    if h : P.IsPrime then (anrem_quotient_dim_cases P h).choose else 0
  have he : ∀ P ∈ F, ringKrullDim (AnalyticGerm n ⧸ P) = e P := fun P hP ↦ by
    have hp : P.IsPrime := ((hmem P).1 hP).1.1
    simp only [e, hp, ↓reduceDIte]
    exact (anrem_quotient_dim_cases P hp).choose_spec
  have hcomp : ∀ P ∈ F, ∃ C : Set (Fin n → ℂ), y ∈ C ∧ (∀ᶠ z in 𝓝 y, z ∈ C → z ∈ A) ∧
      (∀ᶠ z in 𝓝 y, anrem_LocEq C z) ∧
      (∀ᶠ z in 𝓝 y, z ∈ C → ∀ Q' ∈ (adim2_ideal n (adim2_germ n C z)).minimalPrimes,
        ringKrullDim (AnalyticGerm n ⧸ Q') = e P) ∧
      adim2_germ n C y = adim2_zeroSet n P := fun P hP ↦
    anrem_component hy ⟨U, hU, hyU, m, f, hf, hUA⟩ ((hmem P).1 hP) (he P hP)
  choose! C hyC _hCA hCloc hCpure hCgerm using hcomp
  refine ⟨F, e, C, hmem, he, fun P hP ↦ ⟨hyC P hP, hCgerm P hP⟩,
    (Filter.eventually_all_finset F).2 hCloc, (Filter.eventually_all_finset F).2 hCpure, ?_⟩
  have hgerm : adim2_germ n A y = adim2_germ n {z | ∃ P ∈ F, z ∈ C P} y := by
    rw [hcover, ← adim9b_finset_sup_germ]
    exact Finset.sup_congr rfl fun P hP ↦ (hCgerm P hP).symm
  have := Germ.coe_eq.1 hgerm
  have ht : Tendsto (fun z : Fin n → ℂ ↦ z - y) (𝓝 y) (𝓝 0) := by
    simpa using (tendsto_id (x := 𝓝 y)).sub_const y
  filter_upwards [ht.eventually this] with z hz
  have := congrArg (fun p : Prop ↦ p) hz
  simpa using hz


theorem anrem_locEq_congr {n : ℕ} {A B : Set (Fin n → ℂ)} {y : Fin n → ℂ} {O : Set (Fin n → ℂ)}
    (hO : IsOpen O) (hyO : y ∈ O) (hAB : A ∩ O = B ∩ O) (hA : anrem_LocEq A y) :
    anrem_LocEq B y := by
  obtain ⟨U, hU, hyU, m, f, hf, hUA⟩ := hA
  refine ⟨U ∩ O, hU.inter hO, ⟨hyU, hyO⟩, m, f, fun j ↦ (hf j).mono inter_subset_left,
    fun z hz ↦ ?_⟩
  rw [← hUA z hz.1]
  have : z ∈ A ∩ O ↔ z ∈ B ∩ O := by rw [hAB]
  simpa [hz.2] using this.symm

theorem anrem_locEq_inter {n : ℕ} {A B : Set (Fin n → ℂ)} {y : Fin n → ℂ}
    (hA : anrem_LocEq A y) (hB : anrem_LocEq B y) : anrem_LocEq (A ∩ B) y := by
  obtain ⟨U, hU, hyU, m, f, hf, hUA⟩ := hA
  obtain ⟨U', hU', hyU', m', f', hf', hUB⟩ := hB
  refine ⟨U ∩ U', hU.inter hU', ⟨hyU, hyU'⟩, m + m', Fin.append f f', fun j ↦ ?_,
    fun z hz ↦ ?_⟩
  · refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) j
    · rw [Fin.append_left]; exact (hf j).mono inter_subset_left
    · rw [Fin.append_right]; exact (hf' j).mono inter_subset_right
  · rw [mem_inter_iff, hUA z hz.1, hUB z hz.2]
    constructor
    · rintro ⟨h1, h2⟩ j
      refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) j
      · simpa using h1 j
      · simpa using h2 j
    · intro h
      exact ⟨fun j ↦ by simpa using h (Fin.castAdd m' j),
        fun j ↦ by simpa using h (Fin.natAdd m j)⟩

theorem anrem_minimalPrimes_of_not_mem {n : ℕ} {S : Set (Fin n → ℂ)} {z : Fin n → ℂ}
    (hloc : anrem_LocEq S z) (hz : z ∉ S) :
    (adim2_ideal n (adim2_germ n S z)).minimalPrimes = ∅ := by
  rw [anrem_germ_eq_bot_of_not_mem hloc hz]
  have : adim2_ideal n (⊥ : adim2_SetGerm n) = ⊤ := by
    ext a
    simp only [Submodule.mem_top, iff_true]
    exact (bot_le : (⊥ : adim2_SetGerm n) ≤ adim2_zero n a)
  rw [this]
  ext Q
  simp only [mem_empty_iff_false, iff_false]
  intro hQ
  exact hQ.1.1.ne_top (top_le_iff.1 hQ.1.2)

/-- Dimension of a finite union. -/
theorem anrem_dimension_biUnion_le {n : ℕ} {ι : Type*} (F : Finset ι) {S : ι → Set (Fin n → ℂ)}
    {z : Fin n → ℂ} {d : WithBot ℕ∞} (hloc : ∀ i ∈ F, anrem_LocEq (S i) z)
    (h : ∀ i ∈ F, z ∈ S i → adim2_dimension n (adim2_germ n (S i) z) ≤ d) :
    adim2_dimension n (adim2_germ n (⋃ i ∈ F, S i) z) ≤ d := by
  refine (anrem_dimension_le_iff _ z d).2 fun Q hQ ↦ ?_
  obtain ⟨i, hi, hQi⟩ := anrem_minimalPrimes_biUnion F S z hQ
  by_cases hz : z ∈ S i
  · exact (anrem_dimension_le_iff _ z d).1 (h i hi hz) Q hQi
  · rw [anrem_minimalPrimes_of_not_mem (hloc i hi) hz] at hQi
    exact hQi.elim


theorem anrem_germ_congr {n : ℕ} {A B : Set (Fin n → ℂ)} {y : Fin n → ℂ}
    (h : ∀ᶠ z in 𝓝 y, z ∈ A ↔ z ∈ B) : adim2_germ n A y = adim2_germ n B y := by
  apply Germ.coe_eq.2
  have ht : Tendsto (fun z : Fin n → ℂ ↦ y + z) (𝓝 0) (𝓝 y) := by
    simpa using (tendsto_id (x := 𝓝 (0 : Fin n → ℂ))).const_add y
  filter_upwards [ht.eventually h] with z hz
  exact propext hz

/-- **The top-dimensional part and the lower-dimensional part of a locally analytic set.** Near
a point where a locally analytic set has dimension at most `e + 1` nearby, the points of
dimension `e + 1` form a locally analytic set of pure dimension `e + 1`, and the closure of the
points of dimension at most `e` is locally analytic of dimension at most `e`. -/
theorem anrem_split {n : ℕ} {A : Set (Fin n → ℂ)} {y : Fin n → ℂ} (hy : y ∈ A)
    (hloc : anrem_LocEq A y) {e : ℕ}
    (hdim : ∀ᶠ z in 𝓝 y, adim2_dimension n (adim2_germ n A z) ≤ ((e + 1 : ℕ) : WithBot ℕ∞)) :
    anrem_LocEq {z | z ∈ A ∧ ((e + 1 : ℕ) : WithBot ℕ∞) ≤ adim2_dimension n (adim2_germ n A z)} y ∧
    (∀ᶠ z in 𝓝 y, z ∈ {z | z ∈ A ∧ ((e + 1 : ℕ) : WithBot ℕ∞) ≤
        adim2_dimension n (adim2_germ n A z)} →
      ∀ Q ∈ (adim2_ideal n (adim2_germ n {z | z ∈ A ∧ ((e + 1 : ℕ) : WithBot ℕ∞) ≤
        adim2_dimension n (adim2_germ n A z)} z)).minimalPrimes,
        ringKrullDim (AnalyticGerm n ⧸ Q) = ((e + 1 : ℕ) : WithBot ℕ∞)) ∧
    anrem_LocEq (closure {z | z ∈ A ∧ adim2_dimension n (adim2_germ n A z) ≤ (e : WithBot ℕ∞)})
      y ∧
    (∀ᶠ z in 𝓝 y, z ∈ closure {z | z ∈ A ∧ adim2_dimension n (adim2_germ n A z) ≤
        (e : WithBot ℕ∞)} →
      adim2_dimension n (adim2_germ n (closure {z | z ∈ A ∧
        adim2_dimension n (adim2_germ n A z) ≤ (e : WithBot ℕ∞)}) z) ≤ (e : WithBot ℕ∞)) := by
  classical
  obtain ⟨F, eP, C, hmem, heP, hyC, hCloc, hCpure, hAeq⟩ := anrem_decomp hy hloc
  have heP_le : ∀ P ∈ F, eP P ≤ e + 1 := by
    intro P hP
    have h1 : ringKrullDim (AnalyticGerm n ⧸ P) ≤ adim2_dimension n (adim2_germ n A y) :=
      anr_minimal_le_dim _ P ((hmem P).1 hP)
    rw [heP P hP] at h1
    exact_mod_cast h1.trans hdim.self_of_nhds
  obtain ⟨O₀, hO₀sub, hO₀, hyO₀⟩ := eventually_nhds_iff.1 (((hCloc.and hCpure).and hAeq).and hdim)
  -- germs of `A` near `y` are germs of the union of the components
  have hgermA : ∀ z ∈ O₀, adim2_germ n A z = adim2_germ n (⋃ P ∈ F, C P) z := by
    intro z hz
    apply anrem_germ_congr
    filter_upwards [hO₀.mem_nhds hz] with w hw
    rw [(hO₀sub w hw).1.2]
    simp
  have hpureC : ∀ z ∈ O₀, ∀ P ∈ F, z ∈ C P →
      adim2_dimension n (adim2_germ n (C P) z) = eP P := fun z hz P hP hzP ↦
    anrem_dimension_eq_of_pure hzP ((hO₀sub z hz).1.1.2 P hP hzP)
  have hCA : ∀ z ∈ O₀, ∀ P ∈ F, ∀ᶠ w in 𝓝 z, w ∈ C P → w ∈ A := fun z hz P hP ↦ by
    filter_upwards [hO₀.mem_nhds hz] with w hw hwP
    exact (hO₀sub w hw).1.2.2 ⟨P, hP, hwP⟩
  have hDge : ∀ z ∈ O₀, ∀ P ∈ F, z ∈ C P →
      (eP P : WithBot ℕ∞) ≤ adim2_dimension n (adim2_germ n A z) := fun z hz P hP hzP ↦ by
    rw [← hpureC z hz P hP hzP]
    exact anrem_dimension_mono (hCA z hz P hP)
  have hDle : ∀ z ∈ O₀, ∀ Q ∈ (adim2_ideal n (adim2_germ n A z)).minimalPrimes,
      ∃ P ∈ F, z ∈ C P ∧ ringKrullDim (AnalyticGerm n ⧸ Q) = eP P := by
    intro z hz Q hQ
    rw [hgermA z hz] at hQ
    obtain ⟨P, hP, hQP⟩ := anrem_minimalPrimes_biUnion F C z hQ
    by_cases hzP : z ∈ C P
    · exact ⟨P, hP, hzP, (hO₀sub z hz).1.1.2 P hP hzP Q hQP⟩
    · rw [anrem_minimalPrimes_of_not_mem ((hO₀sub z hz).1.1.1 P hP) hzP] at hQP
      exact hQP.elim
  set Fe := F.filter fun P ↦ eP P = e + 1
  set Fl := F.filter fun P ↦ eP P ≤ e
  -- the top-dimensional part
  have hH : ∀ z ∈ O₀, (z ∈ A ∧ ((e + 1 : ℕ) : WithBot ℕ∞) ≤
      adim2_dimension n (adim2_germ n A z)) ↔ z ∈ ⋃ P ∈ Fe, C P := by
    intro z hz
    constructor
    · rintro ⟨hzA, hzd⟩
      obtain ⟨Q, hQ, hQd⟩ := anrem_exists_minimalPrime_ge hzd
      obtain ⟨P, hP, hzP, hQP⟩ := hDle z hz Q hQ
      rw [hQP] at hQd
      have : e + 1 ≤ eP P := by exact_mod_cast hQd
      exact mem_iUnion₂.2 ⟨P, Finset.mem_filter.2 ⟨hP, le_antisymm (heP_le P hP) this⟩, hzP⟩
    · intro h
      obtain ⟨P, hP, hzP⟩ := mem_iUnion₂.1 h
      obtain ⟨hPF, hPe⟩ := Finset.mem_filter.1 hP
      refine ⟨(hO₀sub z hz).1.2.2 ⟨P, hPF, hzP⟩, ?_⟩
      have := hDge z hz P hPF hzP
      rwa [hPe] at this
  have hHeq : {z | z ∈ A ∧ ((e + 1 : ℕ) : WithBot ℕ∞) ≤ adim2_dimension n (adim2_germ n A z)} ∩ O₀
      = (⋃ P ∈ Fe, C P) ∩ O₀ := by
    ext z; exact ⟨fun h ↦ ⟨(hH z h.2).1 h.1, h.2⟩, fun h ↦ ⟨(hH z h.2).2 h.1, h.2⟩⟩
  have hlocU : ∀ z ∈ O₀, ∀ G ⊆ F, anrem_LocEq (⋃ P ∈ G, C P) z := fun z hz G hG ↦
    anrem_locEq_biUnion G fun P hP ↦ (hO₀sub z hz).1.1.1 P (hG hP)
  -- the lower-dimensional components meet the top-dimensional ones in smaller dimension
  have hPmin : ∀ P ∈ F, ∀ Q ∈ F, Q ≤ P → Q = P := by
    intro P hP Q hQ hQP
    exact ((hmem P).1 hP).2 ⟨((hmem Q).1 hQ).1.1, ((hmem Q).1 hQ).1.2⟩ hQP |>.antisymm hQP
      |>.symm
  have hgermle : ∀ P ∈ F, P ≤ adim2_ideal n (adim2_germ n (C P) y) := by
    intro P hP
    rw [(hyC P hP).2]
    exact (adim2_galois n _ P).1 le_rfl
  have hdrop : ∀ P ∈ Fl, ∀ Q ∈ Fe, ∀ᶠ z in 𝓝 y, z ∈ C P ∩ C Q →
      adim2_dimension n (adim2_germ n (C P ∩ C Q) z) + 1 ≤ (eP P : WithBot ℕ∞) := by
    intro P hP Q hQ
    obtain ⟨hPF, hPe⟩ := Finset.mem_filter.1 hP
    obtain ⟨hQF, hQe⟩ := Finset.mem_filter.1 hQ
    have hQP : ¬ Q ≤ P := by
      intro h
      have := hPmin P hPF Q hQF h
      subst this
      omega
    obtain ⟨b, hbQ, hbP⟩ := Set.not_subset.1 hQP
    have hDloc : anrem_LocEq (C P ∩ C Q) y :=
      anrem_locEq_inter ((hO₀sub y hyO₀).1.1.1 P hPF) ((hO₀sub y hyO₀).1.1.1 Q hQF)
    have hR : ∀ R ∈ (adim2_ideal n (adim2_germ n (C P ∩ C Q) y)).minimalPrimes,
        ringKrullDim (AnalyticGerm n ⧸ R) + 1 ≤ (eP P : WithBot ℕ∞) := by
      intro R hR
      have hPR : P ≤ R := (hgermle P hPF).trans ((anr_ideal_anti inter_subset_left y).trans hR.1.2)
      have hbR : b ∈ R := hR.1.2 (anr_ideal_anti inter_subset_right y (hgermle Q hQF hbQ))
      have := hPmin P hPF
      have hPp : P.IsPrime := ((hmem P).1 hPF).1.1
      rw [← heP P hPF]
      exact adim9_krullDim_drop P R hPR b hbP hbR
    rcases hk : eP P with _ | k
    · -- a zero-dimensional component meets nothing else
      have hne : adim2_ideal n (adim2_germ n (C P ∩ C Q) y) = ⊤ := by
        by_contra hne
        obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal _ hne
        have := hM.isPrime
        obtain ⟨R, hRmin, -⟩ := Ideal.exists_minimalPrimes_le hIM
        have h1 := hR R hRmin
        rw [hk] at h1
        have : Nontrivial (AnalyticGerm n ⧸ R) := Ideal.Quotient.nontrivial_iff.2 hRmin.1.1.ne_top
        have h2 := ringKrullDim_nonneg_of_nontrivial (R := AnalyticGerm n ⧸ R)
        have h3 : ringKrullDim (AnalyticGerm n ⧸ R) + 1 ≤ 0 := by exact_mod_cast h1
        have h4 : (0 : WithBot ℕ∞) + 1 ≤ ringKrullDim (AnalyticGerm n ⧸ R) + 1 := by gcongr
        exact absurd (h4.trans h3) (by norm_num)
      have hyD : y ∉ C P ∩ C Q := fun h ↦ adim9b_germ_ideal_ne_top n _ y h hne
      obtain ⟨UD, hUD, hyUD, mD, fD, hfD, hUDeq⟩ := hDloc
      have : ¬ ∀ j, fD j y = 0 := fun h' ↦ hyD ((hUDeq y hyUD).2 h')
      push Not at this
      obtain ⟨j, hj⟩ := this
      filter_upwards [Filter.Eventually.and (hUD.mem_nhds hyUD)
        ((hfD j y hyUD).continuousAt.eventually_ne hj)] with z hz hzD
      exact absurd ((hUDeq z hz.1).1 hzD j) hz.2
    · have hy' : adim2_dimension n (adim2_germ n (C P ∩ C Q) y) ≤ (k : WithBot ℕ∞) := by
        refine (anrem_dimension_le_iff _ y _).2 fun R hRm ↦ ?_
        have := hR R hRm
        rw [hk] at this
        exact adim9_le_pred_of_succ_le _ k this
      filter_upwards [anrem_dimension_upper hDloc hy'] with z hz _
      calc adim2_dimension n (adim2_germ n (C P ∩ C Q) z) + 1 ≤ (k : WithBot ℕ∞) + 1 := by
            gcongr
        _ = ((k + 1 : ℕ) : WithBot ℕ∞) := by push_cast; rfl
  obtain ⟨O₁, hO₁sub, hO₁, hyO₁⟩ := eventually_nhds_iff.1
    (Filter.Eventually.and (hO₀.mem_nhds hyO₀) ((Filter.eventually_all_finset Fl).2 fun P hP ↦
      (Filter.eventually_all_finset Fe).2 fun Q hQ ↦ hdrop P hP Q hQ))
  set low := {z | z ∈ A ∧ adim2_dimension n (adim2_germ n A z) ≤ (e : WithBot ℕ∞)}
  have hlowZ : ∀ w ∈ low ∩ O₀, w ∈ ⋃ P ∈ Fl, C P := by
    rintro w ⟨⟨hwA, hwd⟩, hwO⟩
    obtain ⟨P, hP, hwP⟩ := ((hO₀sub w hwO).1.2).1 hwA
    have := (hDge w hwO P hP hwP).trans hwd
    exact mem_iUnion₂.2 ⟨P, Finset.mem_filter.2 ⟨hP, by exact_mod_cast this⟩, hwP⟩
  have hlowEq : closure low ∩ O₁ = (⋃ P ∈ Fl, C P) ∩ O₁ := by
    ext z
    constructor
    · rintro ⟨hzc, hzO⟩
      have hzO₀ := (hO₁sub z hzO).1
      refine ⟨?_, hzO⟩
      by_contra hzZ
      obtain ⟨UZ, hUZ, hzUZ, mZ, fZ, hfZ, hUZeq⟩ := hlocU z hzO₀ Fl (Finset.filter_subset _ _)
      have : ¬ ∀ j, fZ j z = 0 := fun h' ↦ hzZ ((hUZeq z hzUZ).2 h')
      push Not at this
      obtain ⟨j, hj⟩ := this
      have hev : ∀ᶠ w in 𝓝 z, w ∈ UZ ∧ fZ j w ≠ 0 ∧ w ∈ O₀ :=
        Filter.Eventually.and (hUZ.mem_nhds hzUZ) (((hfZ j z hzUZ).continuousAt.eventually_ne
          hj).and (hO₀.mem_nhds hzO₀))
      obtain ⟨w, hwlow, hw⟩ := (mem_closure_iff_frequently.1 hzc |>.and_eventually hev).exists
      exact hw.2.1 ((hUZeq w hw.1).1 (hlowZ w ⟨hwlow, hw.2.2⟩) j)
    · rintro ⟨hzZ, hzO⟩
      refine ⟨?_, hzO⟩
      obtain ⟨P, hP, hzP⟩ := mem_iUnion₂.1 hzZ
      obtain ⟨hPF, hPe⟩ := Finset.mem_filter.1 hP
      have hzO₀ := (hO₁sub z hzO).1
      rw [mem_closure_iff_frequently]
      by_contra hcon
      rw [not_frequently] at hcon
      -- near `z`, the component lies in the top-dimensional components
      have hsub : ∀ᶠ w in 𝓝 z, w ∈ C P → w ∈ C P ∩ ⋃ Q ∈ Fe, C Q := by
        filter_upwards [hcon, hO₀.mem_nhds hzO₀] with w hw hwO hwP
        refine ⟨hwP, ?_⟩
        by_contra hwZ
        apply hw
        refine ⟨(hO₀sub w hwO).1.2.2 ⟨P, hPF, hwP⟩, ?_⟩
        refine (anrem_dimension_le_iff A w _).2 fun R hR ↦ ?_
        obtain ⟨Q, hQF, hwQ, hRQ⟩ := hDle w hwO R hR
        rw [hRQ]
        have hQe : eP Q ≠ e + 1 := fun h ↦ hwZ (mem_iUnion₂.2 ⟨Q, Finset.mem_filter.2 ⟨hQF, h⟩, hwQ⟩)
        have := heP_le Q hQF
        exact_mod_cast (show eP Q ≤ e by omega)
      have h1 := anrem_dimension_mono hsub
      rw [hpureC z hzO₀ P hPF hzP] at h1
      have hset : C P ∩ ⋃ Q ∈ Fe, C Q = ⋃ Q ∈ Fe, (C P ∩ C Q) := by
        ext w; simp only [mem_inter_iff, mem_iUnion₂]; tauto
      rw [hset] at h1
      obtain ⟨R, hR, hRd⟩ := anrem_exists_minimalPrime_ge h1
      obtain ⟨Q, hQ, hRQ⟩ := anrem_minimalPrimes_biUnion Fe (fun Q ↦ C P ∩ C Q) z hR
      by_cases hzD : z ∈ C P ∩ C Q
      · have h2 := (hO₁sub z hzO).2 P hP Q hQ hzD
        have h3 : ringKrullDim (AnalyticGerm n ⧸ R) + 1 ≤ (eP P : WithBot ℕ∞) :=
          (add_le_add (anr_minimal_le_dim _ R hRQ) le_rfl).trans h2
        have h4 : (eP P : WithBot ℕ∞) + 1 ≤ (eP P : WithBot ℕ∞) :=
          (add_le_add hRd le_rfl).trans h3
        exact absurd h4 (by
          have : ((eP P : ℕ) : WithBot ℕ∞) + 1 = ((eP P + 1 : ℕ) : WithBot ℕ∞) := by
            push_cast; rfl
          rw [this]
          exact_mod_cast Nat.not_succ_le_self _)
      · rw [anrem_minimalPrimes_of_not_mem (anrem_locEq_inter ((hO₀sub z hzO₀).1.1.1 P hPF)
          ((hO₀sub z hzO₀).1.1.1 Q (Finset.mem_filter.1 hQ).1)) hzD] at hRQ
        exact hRQ.elim
  refine ⟨anrem_locEq_congr hO₀ hyO₀ hHeq.symm (hlocU y hyO₀ Fe (Finset.filter_subset _ _)),
    ?_, anrem_locEq_congr hO₁ hyO₁ hlowEq.symm (hlocU y hyO₀ Fl (Finset.filter_subset _ _)), ?_⟩
  · filter_upwards [hO₀.mem_nhds hyO₀] with z hz hzH Q hQ
    have hgerm : adim2_germ n {z | z ∈ A ∧ ((e + 1 : ℕ) : WithBot ℕ∞) ≤
        adim2_dimension n (adim2_germ n A z)} z = adim2_germ n (⋃ P ∈ Fe, C P) z := by
      apply anrem_germ_congr
      filter_upwards [hO₀.mem_nhds hz] with w hw
      exact hH w hw
    rw [hgerm] at hQ
    obtain ⟨P, hP, hQP⟩ := anrem_minimalPrimes_biUnion Fe C z hQ
    obtain ⟨hPF, hPe⟩ := Finset.mem_filter.1 hP
    by_cases hzP : z ∈ C P
    · rw [(hO₀sub z hz).1.1.2 P hPF hzP Q hQP, hPe]
    · rw [anrem_minimalPrimes_of_not_mem ((hO₀sub z hz).1.1.1 P hPF) hzP] at hQP
      exact hQP.elim
  · filter_upwards [hO₁.mem_nhds hyO₁] with z hz _
    have hzO₀ := (hO₁sub z hz).1
    have hgerm : adim2_germ n (closure low) z = adim2_germ n (⋃ P ∈ Fl, C P) z := by
      apply anrem_germ_congr
      filter_upwards [hO₁.mem_nhds hz] with w hw
      have : w ∈ closure low ∩ O₁ ↔ w ∈ (⋃ P ∈ Fl, C P) ∩ O₁ := by rw [hlowEq]
      simpa [hw] using this
    rw [hgerm]
    refine anrem_dimension_biUnion_le Fl (fun P hP ↦ (hO₀sub z hzO₀).1.1.1 P
      (Finset.mem_filter.1 hP).1) fun P hP hzP ↦ ?_
    obtain ⟨hPF, hPe⟩ := Finset.mem_filter.1 hP
    rw [hpureC z hzO₀ P hPF hzP]
    exact_mod_cast hPe

end HodgeLean.Foundations.Analytic
