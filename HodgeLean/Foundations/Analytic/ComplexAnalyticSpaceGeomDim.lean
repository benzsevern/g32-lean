import HodgeLean.Foundations.Analytic.ComplexAnalyticSpaceSubspace
import HodgeLean.Foundations.Analytic.ComplexAnalyticSpaceUpper
import HodgeLean.Foundations.Analytic.ComplexAnalyticSpaceSheet

/-! # Krull dimension and geometric dimension

Helpers prefixed `anb_` for the comparison of the Krull dimension of the germ of a closed analytic
subset with the dimensions of its nearby manifold points.

* A *manifold piece* of `B ⊆ ℂⁿ` of dimension `d` at `a` (`anb_IsManifoldPiece`): near `a`, `B` is
  the image of an open `V ⊆ ℂᵈ` under an analytic map with an analytic left inverse. Its germ has
  Krull dimension `d` (`anb_dimension_of_manifoldPiece`).
* Manifold points of a closed analytic subset, read in a chart, are manifold pieces of its image,
  and conversely.
HC no distance; AV milestone no distance.
-/

noncomputable section

open Set Filter Topology TopologicalSpace

namespace HodgeLean.Foundations.Analytic

open HodgeLean.Foundations HodgeLean.Foundations.AnalyticDivisorAlgebraic6

universe u

/-- `B` is, near `a ∈ B`, the image of an open `V ⊆ ℂᵈ` under an analytic map `σ` with an analytic
left inverse `ψ`. -/
def anb_IsManifoldPiece {n : ℕ} (B : Set (Fin n → ℂ)) (d : ℕ) (a : Fin n → ℂ) : Prop :=
  a ∈ B ∧ ∃ (O : Set (Fin n → ℂ)) (V : Set (Fin d → ℂ)) (σ : (Fin d → ℂ) → (Fin n → ℂ))
    (ψ : (Fin n → ℂ) → (Fin d → ℂ)), IsOpen O ∧ a ∈ O ∧ IsOpen V ∧ AnalyticOnNhd ℂ σ V ∧
      AnalyticOnNhd ℂ ψ O ∧ σ '' V = B ∩ O ∧ ∀ v ∈ V, ψ (σ v) = v

/-- The germ of a manifold piece of dimension `d` has Krull dimension `d`. -/
theorem anb_dimension_of_manifoldPiece {n d : ℕ} {B : Set (Fin n → ℂ)} {a : Fin n → ℂ}
    (h : anb_IsManifoldPiece B d a) :
    adim2_dimension n (adim2_germ n B a) = ((d : ℕ∞) : WithBot ℕ∞) := by
  obtain ⟨haB, O, V, σ, ψ, hO, haO, hV, hσ, hψ, himg, hψσ⟩ := h
  obtain ⟨v1, hv1, hv1a⟩ : a ∈ σ '' V := himg ▸ ⟨haB, haO⟩
  have hv0 : ψ a = v1 := by rw [← hv1a]; exact hψσ v1 hv1
  have hσv0 : σ (ψ a) = a := by rw [hv0, hv1a]
  rw [anb_dimension_eq_of_inverse (B := V) (q := ψ a)
    (anb_analyticAt_shift (hψ a haO) (ψ a)) (by simp)
    (anb_analyticAt_shift (hσ (ψ a) (hv0 ▸ hv1)) a) (by simp [hσv0]) ?_ ?_ ?_ ?_]
  · exact anb_dimension_germ_of_mem_nhds (hV.mem_nhds (hv0 ▸ hv1))
  · filter_upwards [anb_eventually_add_mem hO haO] with z hzO hzB
    obtain ⟨v, hv, hvz⟩ : a + z ∈ σ '' V := himg ▸ ⟨hzB, hzO⟩
    rw [add_sub_cancel, ← hvz, hψσ v hv]
    exact hv
  · exact Filter.Eventually.of_forall fun w hw ↦ by
      rw [add_sub_cancel]
      exact (himg ▸ mem_image_of_mem σ hw : σ (ψ a + w) ∈ B ∩ O).1
  · filter_upwards [anb_eventually_add_mem hO haO] with z hzO hzB
    obtain ⟨v, hv, hvz⟩ : a + z ∈ σ '' V := himg ▸ ⟨hzB, hzO⟩
    rw [add_sub_cancel, ← hvz, hψσ v hv, hvz, add_sub_cancel_left]
  · exact Filter.Eventually.of_forall fun w hw ↦ by
      rw [add_sub_cancel, hψσ _ hw, add_sub_cancel_left]

/-- `B ⊆ ℂⁿ` is, near `p`, the zero set of a map analytic on a neighbourhood of `p`. -/
def anb_LocAnalytic {n : ℕ} (B : Set (Fin n → ℂ)) (p : Fin n → ℂ) : Prop :=
  ∃ O : Set (Fin n → ℂ), IsOpen O ∧ p ∈ O ∧ ∃ (k : ℕ) (F : (Fin n → ℂ) → (Fin k → ℂ)),
    AnalyticOnNhd ℂ F O ∧ ∀ z ∈ O, (z ∈ B ↔ F z = 0)

/-- **Upper bound.** Near a point `p` where `B` is locally analytic, every manifold piece of `B`
has dimension at most the Krull dimension of the germ of `B` at `p`. -/
theorem anb_piece_le {n : ℕ} {B : Set (Fin n → ℂ)} {p : Fin n → ℂ} (hB : anb_LocAnalytic B p) :
    ∃ O : Set (Fin n → ℂ), IsOpen O ∧ p ∈ O ∧ ∀ a ∈ O, ∀ d : ℕ, anb_IsManifoldPiece B d a →
      ((d : ℕ∞) : WithBot ℕ∞) ≤ adim2_dimension n (adim2_germ n B p) := by
  obtain ⟨O0, hO0, hpO0, k, F, hF, hBF⟩ := hB
  obtain ⟨s, hs⟩ := anb_germ_eq_inf hO0 hpO0 hF hBF
  obtain ⟨F', hF'min, hF'sup⟩ := adim3_minimal_prime_cover n s
  set I := adim2_ideal n (adim2_germ n B p)
  have hmin : ∀ P ∈ F', P ∈ I.minimalPrimes := fun P hP ↦ by
    have : P ∈ (F' : Set (Ideal (AnalyticGerm n))) := hP
    rw [hF'min, ← hs] at this
    exact this
  have hdata : ∀ P : {P // P ∈ F'}, ∃ (dP : ℕ) (π : (Fin n → ℂ) →L[ℂ] (Fin dP → ℂ))
      (W : Set (Fin n → ℂ)) (m : ℕ) (f : Fin m → (Fin n → ℂ) → ℂ),
      IsOpen W ∧ (0 : Fin n → ℂ) ∈ W ∧ (∀ j, ContinuousOn (f j) W) ∧
      adim2_zeroSet n P.1 = Filter.Germ.ofFun (fun z ↦ ∀ j, f j z = 0) ∧
      (∀ w, {z | z ∈ W ∧ (∀ j, f j z = 0) ∧ π z = w}.Finite) ∧
      ((dP : ℕ∞) : WithBot ℕ∞) ≤ adim2_dimension n (adim2_germ n B p) := by
    intro P
    have hPm := hmin P.1 P.2
    obtain ⟨dP, π, W, m, f, hW, hW0, hfc, hzs, hfib, hdP⟩ := anb_prime_projection P.1 hPm.1.1
    refine ⟨dP, π, W, m, f, hW, hW0, hfc, hzs, hfib, ?_⟩
    rw [hdP, adim2_dimension]
    exact ringKrullDim_le_of_surjective (Ideal.Quotient.factor hPm.1.2)
      (Ideal.Quotient.factor_surjective _)
  choose dP π W m f hW hW0 hfc hzs hfib hdle using hdata
  have hgerm : adim2_germ n B p =
      Filter.Germ.ofFun (fun z ↦ ∃ P ∈ F'.attach, ∀ j, f P j z = 0) := by
    rw [hs, hF'sup, ← Finset.sup_attach, Finset.sup_congr rfl fun P _ ↦ hzs P,
      anb_germ_finset_sup]
  obtain ⟨t, ht, hto, h0t⟩ := eventually_nhds_iff.1 (Filter.Germ.coe_eq.1 hgerm)
  let Ω := t ∩ ⋂ P : {P // P ∈ F'}, W P
  have hΩ : IsOpen Ω := hto.inter (isOpen_iInter_of_finite fun P ↦ hW P)
  have hΩt : ∀ z ∈ Ω, (p + z ∈ B ↔ ∃ P ∈ F'.attach, ∀ j, f P j z = 0) := fun z hz ↦ by
    have := ht z hz.1
    exact Iff.of_eq this
  have hΩW : ∀ z ∈ Ω, ∀ P, z ∈ W P := fun z hz P ↦ mem_iInter.1 hz.2 P
  let O := (fun a ↦ a - p) ⁻¹' Ω
  refine ⟨O, hΩ.preimage (continuous_id.sub continuous_const),
    ⟨by simpa using h0t, mem_iInter.2 fun P ↦ by simpa using hW0 P⟩, fun a haO d hpiece ↦ ?_⟩
  obtain ⟨haB, Oa, V, σ, ψ, hOa, haOa, hV, hσ, hψ, himg, hψσ⟩ := hpiece
  obtain ⟨v1, hv1, hv1a⟩ : a ∈ σ '' V := himg ▸ ⟨haB, haOa⟩
  let V1 := V ∩ σ ⁻¹' (O ∩ Oa)
  have hV1 : IsOpen V1 := hσ.continuousOn.isOpen_inter_preimage hV
    ((hΩ.preimage (continuous_id.sub continuous_const)).inter hOa)
  have hv1V1 : v1 ∈ V1 := ⟨hv1, by rw [mem_preimage, hv1a]; exact ⟨haO, haOa⟩⟩
  let C : {P // P ∈ F'} → Set (Fin d → ℂ) := fun P ↦ {v | ∀ j, f P j (σ v - p) = 0}
  have hcov : V1 ⊆ ⋃ P ∈ F'.attach, C P := by
    intro v hv
    have hσv : σ v ∈ B ∩ Oa := himg ▸ mem_image_of_mem σ hv.1
    have := (hΩt _ hv.2.1).1 (by rw [add_sub_cancel]; exact hσv.1)
    obtain ⟨P, hP, hPv⟩ := this
    exact mem_biUnion hP hPv
  have hcont : ∀ P j, ContinuousOn (fun v ↦ f P j (σ v - p)) V1 := fun P j ↦
    (hfc P j).comp ((hσ.continuousOn.mono inter_subset_left).sub continuousOn_const)
      fun v hv ↦ hΩW _ hv.2.1 P
  have hrel : ∀ P ∈ F'.attach, IsOpen (V1 \ C P) := by
    intro P _
    have : V1 \ C P = ⋃ j, V1 ∩ (fun v ↦ f P j (σ v - p)) ⁻¹' {0}ᶜ := by
      ext v
      simp only [C, Set.mem_sdiff, mem_ofPred_eq, not_forall, mem_iUnion, mem_inter_iff,
        mem_preimage, mem_compl_iff, mem_singleton_iff]
      tauto
    rw [this]
    exact isOpen_iUnion fun j ↦ (hcont P j).isOpen_inter_preimage hV1 isOpen_compl_singleton
  obtain ⟨P, -, V2, hV2, hne2, hV2V1, hV2C⟩ :=
    anb_exists_open_of_finite_cover F'.attach C hV1 ⟨v1, hv1V1⟩ hrel hcov
  have hg : AnalyticOnNhd ℂ (fun v ↦ π P (σ v - p)) V2 := fun v hv ↦
    (π P).analyticAt _ |>.comp ((hσ v (hV2V1 hv).1).sub analyticAt_const)
  have hfin2 : ∀ w, {v | v ∈ V2 ∧ π P (σ v - p) = w}.Finite := by
    intro w
    refine ((hfib P w).image fun z ↦ ψ (z + p)).subset ?_
    rintro v ⟨hv, hvw⟩
    refine ⟨σ v - p, ⟨hΩW _ (hV2V1 hv).2.1 P, hV2C hv, hvw⟩, ?_⟩
    simp only [sub_add_cancel]
    exact hψσ v (hV2V1 hv).1
  have hdd := anb_le_of_finite_fibres hV2 hne2 hg hfin2
  exact le_trans (by exact_mod_cast hdd) (hdle P)

/-- The common zeros of two families of functions analytic on open sets containing the origin form
a locally analytic set there. -/
theorem anb_locAnalytic_zeros {n m m' : ℕ} (f : Fin m → (Fin n → ℂ) → ℂ)
    (f' : Fin m' → (Fin n → ℂ) → ℂ) (U U' : Set (Fin n → ℂ)) (hU : IsOpen U) (hU' : IsOpen U')
    (h0 : (0 : Fin n → ℂ) ∈ U ∩ U') (hf : ∀ j, AnalyticOnNhd ℂ (f j) U)
    (hf' : ∀ j, AnalyticOnNhd ℂ (f' j) U') :
    anb_LocAnalytic {z | z ∈ U ∩ U' ∧ (∀ j, f j z = 0) ∧ ∀ j, f' j z = 0} 0 := by
  refine ⟨U ∩ U', hU.inter hU', h0, m + m', fun z ↦ Fin.append (fun j ↦ f j z) (fun j ↦ f' j z),
    fun z hz ↦ ?_, fun z hz ↦ ?_⟩
  · refine analyticAt_pi_iff.2 fun l ↦ Fin.addCases (fun l ↦ ?_) (fun j ↦ ?_) l
    · simp only [Fin.append_left]; exact hf l z hz.1
    · simp only [Fin.append_right]; exact hf' j z hz.2
  · constructor
    · rintro ⟨-, h1, h2⟩
      funext l
      refine Fin.addCases (fun l ↦ ?_) (fun j ↦ ?_) l
      · simp [h1 l]
      · simp [h2 j]
    · intro h
      refine ⟨hz, fun j ↦ ?_, fun j ↦ ?_⟩
      · simpa using congrFun h (Fin.castAdd m' j)
      · simpa using congrFun h (Fin.natAdd m j)

/-- The common zeros of representatives of generators of two distinct minimal primes `P`, `P'`
have, at the origin, Krull dimension less than that of `P`. -/
theorem anb_inter_dim_lt {n m m' : ℕ} {I P P' : Ideal (AnalyticGerm n)} (hP : P ∈ I.minimalPrimes)
    (hP' : P' ∈ I.minimalPrimes) (hne : P' ≠ P) (g : Fin m → AnalyticGerm n)
    (f : Fin m → (Fin n → ℂ) → ℂ) (hgen : Ideal.span (Set.range g) = P)
    (hrep : ∀ j, Filter.Germ.ofFun (f j) = (g j).val) (g' : Fin m' → AnalyticGerm n)
    (f' : Fin m' → (Fin n → ℂ) → ℂ) (hgen' : Ideal.span (Set.range g') = P')
    (hrep' : ∀ j, Filter.Germ.ofFun (f' j) = (g' j).val) (Y : Set (Fin n → ℂ))
    (hY : ∀ z ∈ Y, (∀ j, f j z = 0) ∧ ∀ j, f' j z = 0) :
    adim2_dimension n (adim2_germ n Y 0) + 1 ≤ ringKrullDim (AnalyticGerm n ⧸ P) := by
  have hle : P ⊔ P' ≤ adim2_ideal n (adim2_germ n Y 0) := by
    intro h hh
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hh
    rw [anb_mem_ideal_germ_iff (F := anb_rep a + anb_rep b)
      (by rw [show (a + b).val = a.val + b.val from rfl, ← anb_rep_germ a, ← anb_rep_germ b]; rfl)]
    filter_upwards [anb_vanish_of_mem hgen hrep ha (anb_rep_germ a),
      anb_vanish_of_mem hgen' hrep' hb (anb_rep_germ b)] with z hza hzb hzY
    rw [zero_add] at hzY
    simp [hza (hY z hzY).1, hzb (hY z hzY).2]
  have hnot : ¬ P' ≤ P := fun h ↦ hne (le_antisymm h (hP.2 hP'.1 h))
  obtain ⟨h, hhP', hhP⟩ := Set.not_subset.1 hnot
  have := hP.1.1
  have h1 := anb_dim_sup_lt (P := P) (J := P') hhP' hhP
  have h2 : adim2_dimension n (adim2_germ n Y 0) ≤ ringKrullDim (AnalyticGerm n ⧸ (P ⊔ P')) :=
    ringKrullDim_le_of_surjective (Ideal.Quotient.factor hle) (Ideal.Quotient.factor_surjective _)
  calc adim2_dimension n (adim2_germ n Y 0) + 1
      ≤ ringKrullDim (AnalyticGerm n ⧸ (P ⊔ P')) + 1 := by gcongr
    _ ≤ _ := h1

/-- **Lower bound.** Arbitrarily near a point `p ∈ B` where `B` is locally analytic there are
manifold pieces of `B` of dimension the Krull dimension of the germ of `B` at `p`. -/
theorem anb_exists_piece {n : ℕ} {B : Set (Fin n → ℂ)} {p : Fin n → ℂ}
    (hB : anb_LocAnalytic B p) (hp : p ∈ B) (O : Set (Fin n → ℂ)) (hO : IsOpen O) (hpO : p ∈ O) :
    ∃ a ∈ O, ∃ d : ℕ, anb_IsManifoldPiece B d a ∧
      ((d : ℕ∞) : WithBot ℕ∞) = adim2_dimension n (adim2_germ n B p) := by
  classical
  obtain ⟨O0, hO0, hpO0, k, F, hF, hBF⟩ := hB
  obtain ⟨s, hs⟩ := anb_germ_eq_inf hO0 hpO0 hF hBF
  obtain ⟨F', hF'min, hF'sup⟩ := adim3_minimal_prime_cover n s
  set I := adim2_ideal n (adim2_germ n B p)
  have hmin : ∀ P ∈ F', P ∈ I.minimalPrimes := fun P hP ↦ by
    have : P ∈ (F' : Set (Ideal (AnalyticGerm n))) := hP
    rw [hF'min, ← hs] at this
    exact this
  -- the dimension is a natural number
  have hItop : I ≠ ⊤ := by
    intro h
    have h1 : (1 : AnalyticGerm n) ∈ I := h ▸ Submodule.mem_top
    rw [anb_mem_ideal_germ_iff (F := fun _ ↦ 1) rfl] at h1
    have := h1.self_of_nhds (by simpa using hp)
    exact one_ne_zero this
  have : Nontrivial (AnalyticGerm n ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hItop
  have hDnn : (0 : WithBot ℕ∞) ≤ adim2_dimension n (adim2_germ n B p) :=
    ringKrullDim_nonneg_of_nontrivial
  have hDle : adim2_dimension n (adim2_germ n B p) ≤ ((n : ℕ∞) : WithBot ℕ∞) := by
    refine (ringKrullDim_quotient_le _).trans ?_
    rw [adim6_parameter_dimension]; rfl
  obtain ⟨D, hD⟩ : ∃ D : ℕ, adim2_dimension n (adim2_germ n B p) = ((D : ℕ∞) : WithBot ℕ∞) := by
    generalize adim2_dimension n (adim2_germ n B p) = x at hDnn hDle
    induction x using WithBot.recBotCoe with
    | bot => exact absurd hDnn (by simp)
    | coe m =>
      induction m using ENat.recTopCoe with
      | top => exact absurd (top_le_iff.1 (WithBot.coe_le_coe.1 hDle)) (ENat.natCast_ne_top n)
      | coe m => exact ⟨m, rfl⟩
  rw [hD]
  -- a minimal prime of dimension `D`
  obtain ⟨P, hPmin, hPD⟩ := anb_exists_minimalPrime_dim I hD
  have hPF' : P ∈ F' := by
    have : P ∈ (F' : Set (Ideal (AnalyticGerm n))) := by rw [hF'min, ← hs]; exact hPmin
    exact this
  -- generators of all components
  have hdata := fun Q : {Q // Q ∈ F'} ↦ anb_generators Q.1
  choose m g f U hgen hrep hU hU0 hf hzs using hdata
  set P0 : {Q // Q ∈ F'} := ⟨P, hPF'⟩
  have hgerm : adim2_germ n B p =
      Filter.Germ.ofFun (fun z ↦ ∃ Q ∈ F'.attach, ∀ j, f Q j z = 0) := by
    rw [hs, hF'sup, ← Finset.sup_attach, Finset.sup_congr rfl fun Q _ ↦ hzs Q,
      anb_germ_finset_sup]
  obtain ⟨t, ht, hto, h0t⟩ := eventually_nhds_iff.1 (Filter.Germ.coe_eq.1 hgerm)
  -- the intersections with the other components are of smaller dimension
  let Y : {Q // Q ∈ F'} → Set (Fin n → ℂ) := fun Q ↦
    {z | z ∈ U P0 ∩ U Q ∧ (∀ j, f P0 j z = 0) ∧ ∀ j, f Q j z = 0}
  have hYU : ∀ Q, ∃ OY : Set (Fin n → ℂ), IsOpen OY ∧ (0 : Fin n → ℂ) ∈ OY ∧
      (Q ≠ P0 → ∀ a ∈ OY, ∀ d : ℕ, anb_IsManifoldPiece (Y Q) d a →
        ((d : ℕ∞) : WithBot ℕ∞) + 1 ≤ ((D : ℕ∞) : WithBot ℕ∞)) := by
    intro Q
    by_cases hQ : Q = P0
    · exact ⟨univ, isOpen_univ, mem_univ _, fun h ↦ absurd hQ h⟩
    obtain ⟨OY, hOY, h0OY, hle⟩ := anb_piece_le (anb_locAnalytic_zeros (f P0) (f Q) (U P0) (U Q)
      (hU P0) (hU Q) ⟨hU0 P0, hU0 Q⟩ (hf P0) (hf Q))
    have hlt := anb_inter_dim_lt hPmin (hmin Q.1 Q.2) (fun h ↦ hQ (Subtype.ext h)) (g P0) (f P0)
      (hgen P0) (hrep P0) (g Q) (f Q) (hgen Q) (hrep Q) (Y Q) fun z hz ↦ hz.2
    rw [hPD] at hlt
    refine ⟨OY, hOY, h0OY, fun _ a ha d hpiece ↦ ?_⟩
    calc ((d : ℕ∞) : WithBot ℕ∞) + 1 ≤ adim2_dimension n (adim2_germ n (Y Q) 0) + 1 := by
          gcongr; exact hle a ha d hpiece
      _ ≤ _ := hlt
  choose OY hOY h0OY hOYle using hYU
  -- the neighbourhood `Ω` of the origin
  let Ω := t ∩ (⋂ Q, U Q) ∩ (⋂ Q, OY Q) ∩ (fun z ↦ p + z) ⁻¹' O
  have hΩ : IsOpen Ω := ((hto.inter (isOpen_iInter_of_finite hU)).inter
    (isOpen_iInter_of_finite hOY)).inter (hO.preimage (continuous_const.add continuous_id))
  have hΩ0 : (0 : Fin n → ℂ) ∈ Ω :=
    ⟨⟨⟨h0t, mem_iInter.2 hU0⟩, mem_iInter.2 h0OY⟩, by simpa using hpO⟩
  have hΩU : ∀ z ∈ Ω, ∀ Q, z ∈ U Q := fun z hz Q ↦ mem_iInter.1 hz.1.1.2 Q
  have hΩB : ∀ z ∈ Ω, (p + z ∈ B ↔ ∃ Q ∈ F'.attach, ∀ j, f Q j z = 0) := fun z hz ↦
    Iff.of_eq (ht z hz.1.1.1)
  -- the sheets of the component `P`
  obtain ⟨π, V5, σ, hV5, hV5ne, hσ, hσV, hsheet⟩ := anb_prime_sheet P hPmin.1.1 hPD (g P0)
    (f P0) (U P0) (hgen P0) (hrep P0) (hU P0) (hU0 P0) (hf P0) Ω hΩ hΩ0
  have hσc : ContinuousOn σ V5 := hσ.continuousOn
  -- a parameter whose sheet point avoids the other components
  let others := F'.attach.filter (fun Q ↦ Q ≠ P0)
  let C' : {Q // Q ∈ F'} → Set (Fin D → ℂ) := fun Q ↦ {w | ∀ j, f Q j (σ w) = 0}
  have hrel : ∀ Q ∈ others, IsOpen (V5 \ C' Q) := by
    intro Q _
    have : V5 \ C' Q = V5 ∩ (fun w ↦ fun j ↦ f Q j (σ w)) ⁻¹' {0}ᶜ := by
      ext w
      simp [C', funext_iff]
    rw [this]
    refine ContinuousOn.isOpen_inter_preimage ?_ hV5 isOpen_compl_singleton
    exact continuousOn_pi.2 fun j ↦
      (hf Q j).continuousOn.comp hσc fun w hw ↦ hΩU _ (hσV w hw).1 Q
  have hw1 : ∃ w1 ∈ V5, ∀ Q ∈ others, w1 ∉ C' Q := by
    by_contra hcon
    have hcov : V5 ⊆ ⋃ Q ∈ others, C' Q := fun w hw ↦ by
      by_contra hw'
      exact hcon ⟨w, hw, fun Q hQ hwQ ↦ hw' (mem_biUnion hQ hwQ)⟩
    obtain ⟨Q, hQ, V6, hV6, hV6ne, hV6V5, hV6C⟩ :=
      anb_exists_open_of_finite_cover others C' hV5 hV5ne hrel hcov
    have hQne : Q ≠ P0 := (Finset.mem_filter.1 hQ).2
    obtain ⟨w', hw'⟩ := hV6ne
    have hw'5 := hV6V5 hw'
    obtain ⟨Os, hOs, hσOs, Vs, hVs, hw'Vs, hVsV5, himg⟩ := hsheet w' hw'5
    have hpiece : anb_IsManifoldPiece (Y Q) D (σ w') := by
      refine ⟨⟨⟨hΩU _ (hσV _ hw'5).1 P0, hΩU _ (hσV _ hw'5).1 Q⟩, (hσV _ hw'5).2.1, hV6C hw'⟩,
        Os ∩ π ⁻¹' V6 ∩ Ω, Vs ∩ V6, σ, π, (hOs.inter (hV6.preimage π.continuous)).inter hΩ,
        ⟨⟨hσOs, by rw [mem_preimage, (hσV _ hw'5).2.2]; exact hw'⟩, (hσV _ hw'5).1⟩,
        hVs.inter hV6, fun w hw ↦ hσ w (hV6V5 hw.2), fun x _ ↦ π.analyticAt x, ?_,
        fun w hw ↦ (hσV w (hV6V5 hw.2)).2.2⟩
      ext x
      constructor
      · rintro ⟨w, ⟨hwVs, hwV6⟩, rfl⟩
        have hx : σ w ∈ {x | x ∈ Ω ∧ ∀ j, f P0 j x = 0} ∩ Os := himg ▸ mem_image_of_mem σ hwVs
        exact ⟨⟨⟨hΩU _ hx.1.1 P0, hΩU _ hx.1.1 Q⟩, hx.1.2, hV6C hwV6⟩,
          ⟨hx.2, by rw [mem_preimage, (hσV w (hV6V5 hwV6)).2.2]; exact hwV6⟩, hx.1.1⟩
      · rintro ⟨⟨-, hx0, -⟩, ⟨hxOs, hxV6⟩, hxΩ⟩
        obtain ⟨w, hw, rfl⟩ : x ∈ σ '' Vs := himg ▸ ⟨⟨hxΩ, hx0⟩, hxOs⟩
        refine ⟨w, ⟨hw, ?_⟩, rfl⟩
        rw [mem_preimage, (hσV w (hVsV5 hw)).2.2] at hxV6
        exact hxV6
    have hbad := hOYle Q hQne (σ w') (mem_iInter.1 (hσV _ hw'5).1.1.2 Q) D hpiece
    have h1 : (((D + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) ≤ ((D : ℕ∞) : WithBot ℕ∞) := by
      exact_mod_cast hbad
    have h2 := Nat.cast_le.1 (WithBot.coe_le_coe.1 h1)
    omega
  obtain ⟨w1, hw1V5, hw1C⟩ := hw1
  obtain ⟨Os1, hOs1, hσOs1, Vs1, hVs1, hw1Vs1, hVs1V5, himg1⟩ := hsheet w1 hw1V5
  have havoid : ∀ Q, ∃ A : Set (Fin n → ℂ), IsOpen A ∧ σ w1 ∈ A ∧
      (Q ≠ P0 → ∀ z ∈ A, z ∈ Ω → ¬ ∀ j, f Q j z = 0) := by
    intro Q
    by_cases hQ : Q = P0
    · exact ⟨univ, isOpen_univ, mem_univ _, fun h ↦ absurd hQ h⟩
    · have hQo : Q ∈ others := Finset.mem_filter.2 ⟨Finset.mem_attach _ _, hQ⟩
      obtain ⟨j, hj⟩ := not_forall.1 (hw1C Q hQo)
      refine ⟨Ω ∩ (f Q j) ⁻¹' {0}ᶜ, ((hf Q j).continuousOn.mono fun z hz ↦ hΩU z hz Q)
        |>.isOpen_inter_preimage hΩ isOpen_compl_singleton, ⟨(hσV w1 hw1V5).1, hj⟩,
        fun _ z hz _ h ↦ hz.2 (h j)⟩
  choose A hA hσA hAav using havoid
  let Oav := ⋂ Q, A Q
  have hOav : IsOpen Oav := isOpen_iInter_of_finite hA
  have hσ1Oav : σ w1 ∈ Oav := mem_iInter.2 hσA
  -- the manifold piece of `B` at `p + σ w1`
  have hmemB : ∀ w ∈ Vs1, p + σ w ∈ B := fun w hw ↦ by
    have hx : σ w ∈ {x | x ∈ Ω ∧ ∀ j, f P0 j x = 0} ∩ Os1 := himg1 ▸ mem_image_of_mem σ hw
    exact (hΩB _ hx.1.1).2 ⟨P0, Finset.mem_attach _ _, hx.1.2⟩
  refine ⟨p + σ w1, (hσV w1 hw1V5).1.2, D, ⟨hmemB w1 hw1Vs1,
    (fun x ↦ x - p) ⁻¹' (Os1 ∩ Oav ∩ Ω), Vs1 ∩ σ ⁻¹' Oav, fun w ↦ p + σ w,
    fun x ↦ π (x - p), ((hOs1.inter hOav).inter hΩ).preimage (continuous_id.sub continuous_const),
    by simpa using ⟨⟨hσOs1, hσ1Oav⟩, (hσV w1 hw1V5).1⟩,
    (hσc.mono hVs1V5).isOpen_inter_preimage hVs1 hOav,
    fun w hw ↦ analyticAt_const.add (hσ w (hVs1V5 hw.1)),
    fun x _ ↦ by simp only [map_sub]; exact (π.analyticAt x).sub analyticAt_const, ?_,
    fun w hw ↦ by simpa using (hσV w (hVs1V5 hw.1)).2.2⟩, rfl⟩
  ext x
  constructor
  · rintro ⟨w, ⟨hwVs1, hwA⟩, rfl⟩
    have hx : σ w ∈ {x | x ∈ Ω ∧ ∀ j, f P0 j x = 0} ∩ Os1 := himg1 ▸ mem_image_of_mem σ hwVs1
    exact ⟨hmemB w hwVs1, by simpa using ⟨⟨hx.2, hwA⟩, hx.1.1⟩⟩
  · rintro ⟨hxB, ⟨hxOs, hxA⟩, hxΩ⟩
    have hxB' : p + (x - p) ∈ B := by simpa using hxB
    obtain ⟨Q, -, hQ⟩ := (hΩB _ hxΩ).1 hxB'
    have hQ0 : Q = P0 := by
      by_contra hne
      exact hAav Q hne _ (mem_iInter.1 hxA Q) hxΩ hQ
    subst hQ0
    obtain ⟨w, hw, hwx⟩ : x - p ∈ σ '' Vs1 := himg1 ▸ ⟨⟨hxΩ, hQ⟩, hxOs⟩
    refine ⟨w, ⟨hw, by rw [mem_preimage, hwx]; exact hxA⟩, ?_⟩
    simp only [hwx, add_sub_cancel]

section Chart

variable {X : Type u} [TopologicalSpace X] (S : an_ReducedSpace X) (Z : Set X)

/-- A manifold point of `Z` in a chart domain is a manifold piece of the image of `Z`. -/
theorem anb_piece_of_regular (i : S.atlas.ι) {d : ℕ} {y : X} (hy : y ∈ (S.atlas.chart i).dom)
    (h : an_IsRegularOfDim S Z d y) :
    anb_IsManifoldPiece ((S.atlas.chart i).toFun '' (Z ∩ (S.atlas.chart i).dom)) d
      ((S.atlas.chart i).toFun y) := by
  set c := S.atlas.chart i
  obtain ⟨hyZ, W, V, σ, ψ, hW, hyW, hV, hσc, himg, hψσ, hψ, hσ⟩ := h
  have hk := fun j ↦ hψ j ⟨y, hyW⟩ i hy
  choose N hN hyN G hG hψG using hk
  let Ψ : (Fin c.n → ℂ) → (Fin d → ℂ) := fun z j ↦ G j z
  have hΨ : AnalyticAt ℂ Ψ (c.toFun y) := analyticAt_pi_iff.2 hG
  let N' := W ∩ (⋂ j, N j) ∩ c.dom
  have hN' : IsOpen N' := (hW.inter (isOpen_iInter_of_finite hN)).inter c.isOpen_dom
  obtain ⟨O1, hO1, hO1N⟩ := anb_exists_open_trace c hN'
  let O := O1 ∩ {z | AnalyticAt ℂ Ψ z}
  have hO : IsOpen O := hO1.inter (isOpen_analyticAt ℂ Ψ)
  have hσi := hσ i
  have hV1 : IsOpen (V ∩ σ ⁻¹' c.dom) := hσc.isOpen_inter_preimage hV c.isOpen_dom
  let V' := (V ∩ σ ⁻¹' c.dom) ∩ (c.toFun ∘ σ) ⁻¹' O
  have hV' : IsOpen V' := hσi.continuousOn.isOpen_inter_preimage hV1 hO
  have hNmem : ∀ w ∈ c.dom, c.toFun w ∈ O → w ∈ N' := fun w hw hwO ↦ (hO1N w hw).1 hwO.1
  refine ⟨⟨y, ⟨hyZ, hy⟩, rfl⟩, O, V', c.toFun ∘ σ, Ψ, hO,
    ⟨(hO1N y hy).2 ⟨⟨hyW, mem_iInter.2 hyN⟩, hy⟩, hΨ⟩, hV', hσi.mono inter_subset_left,
    fun z hz ↦ hz.2, ?_, fun v hv ↦ ?_⟩
  · ext z
    constructor
    · rintro ⟨v, hv, rfl⟩
      have hσv : σ v ∈ Z ∩ W := himg ▸ mem_image_of_mem σ hv.1.1
      exact ⟨⟨σ v, ⟨hσv.1, hv.1.2⟩, rfl⟩, hv.2⟩
    · rintro ⟨⟨w, ⟨hwZ, hwd⟩, rfl⟩, hzO⟩
      have hwN := hNmem w hwd hzO
      obtain ⟨v, hv, hvw⟩ : w ∈ σ '' V := himg ▸ ⟨hwZ, hwN.1.1⟩
      refine ⟨v, ⟨⟨hv, ?_⟩, ?_⟩, by simp [hvw]⟩
      · rw [mem_preimage, hvw]; exact hwd
      · simp only [mem_preimage, Function.comp_apply, hvw]; exact hzO
  · have hσv : σ v ∈ Z ∩ W := himg ▸ mem_image_of_mem σ hv.1.1
    have hN'v := hNmem (σ v) hv.1.2 hv.2
    change Ψ (c.toFun (σ v)) = v
    conv_rhs => rw [← hψσ v hv.1.1]
    funext j
    exact (hψG j ⟨σ v, hσv.2⟩ ⟨mem_iInter.1 hN'v.1.2 j, hv.1.2⟩).symm

/-- A manifold piece of the image of `Z` in a chart is a manifold point of `Z`. -/
theorem anb_regular_of_piece (i : S.atlas.ι) {d : ℕ} {a : Fin (S.atlas.chart i).n → ℂ}
    (h : anb_IsManifoldPiece ((S.atlas.chart i).toFun '' (Z ∩ (S.atlas.chart i).dom)) d a) :
    ∃ y ∈ (S.atlas.chart i).dom, (S.atlas.chart i).toFun y = a ∧ an_IsRegularOfDim S Z d y := by
  set c := S.atlas.chart i
  obtain ⟨⟨y, ⟨hyZ, hyd⟩, rfl⟩, O, V, σA, ψA, hO, hyO, hV, hσA, hψA, himg, hψσ⟩ := h
  have : Nonempty X := ⟨y⟩
  let σ : (Fin d → ℂ) → X := fun v ↦ Function.invFunOn c.toFun c.dom (σA v)
  have hσA_mem : ∀ v ∈ V, ∃ w ∈ c.dom, c.toFun w = σA v := fun v hv ↦ by
    obtain ⟨⟨w, ⟨-, hw⟩, hwv⟩, -⟩ : σA v ∈ _ ∩ O := himg ▸ mem_image_of_mem σA hv
    exact ⟨w, hw, hwv⟩
  have hσdom : ∀ v ∈ V, σ v ∈ c.dom := fun v hv ↦ Function.invFunOn_mem (hσA_mem v hv)
  have hcσ : ∀ v ∈ V, c.toFun (σ v) = σA v := fun v hv ↦ Function.invFunOn_eq (hσA_mem v hv)
  have hσcont : ContinuousOn σ V := by
    rw [continuousOn_iff_continuous_domRestrict]
    let σ' : V → c.dom := fun v ↦ ⟨σ v, hσdom v v.2⟩
    have h1 : Continuous (c.dom.domRestrict c.toFun ∘ σ') := by
      have : c.dom.domRestrict c.toFun ∘ σ' = V.domRestrict σA := funext fun v ↦ hcσ v v.2
      rw [this]
      exact continuousOn_iff_continuous_domRestrict.1 hσA.continuousOn
    exact continuous_subtype_val.comp (c.isEmbedding.isInducing.continuous_iff.2 h1)
  let W := c.dom ∩ c.toFun ⁻¹' O
  have hW : IsOpen W := (anb_continuousOn_toFun c).isOpen_inter_preimage c.isOpen_dom hO
  refine ⟨y, hyd, rfl, hyZ, W, V, σ, ψA ∘ c.toFun, hW, ⟨hyd, hyO⟩, hV, hσcont, ?_,
    fun v hv ↦ ?_, fun j ↦ ?_, fun i' ↦ ?_⟩
  · ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨⟨w', ⟨hw'Z, hw'd⟩, hw'v⟩, hO'⟩ : σA v ∈ _ ∩ O := himg ▸ mem_image_of_mem σA hv
      have : σ v = w' := anb_injOn_toFun c (hσdom v hv) hw'd (by rw [hcσ v hv, hw'v])
      exact ⟨this ▸ hw'Z, hσdom v hv, by rw [mem_preimage, hcσ v hv]; exact hO'⟩
    · rintro ⟨hwZ, hwd, hwO⟩
      obtain ⟨v, hv, hvw⟩ : c.toFun w ∈ σA '' V := himg ▸ ⟨⟨w, ⟨hwZ, hwd⟩, rfl⟩, hwO⟩
      exact ⟨v, hv, anb_injOn_toFun c (hσdom v hv) hwd (by rw [hcσ v hv, hvw])⟩
  · simp only [Function.comp_apply, hcσ v hv, hψσ v hv]
  · refine anb_isHolFun_of_chart S.atlas S.isAnalytic fun w ↦
      ⟨i, w.2.1, univ, isOpen_univ, mem_univ _, fun z ↦ ψA z j, ?_, fun _ _ ↦ rfl⟩
    exact analyticAt_pi_iff.1 (hψA _ w.2.2) j
  · rintro v ⟨hv, hvi'⟩
    obtain ⟨N, hN, hvN, hNsub, H, hH⟩ := anb_transition S.atlas S.isAnalytic i i' (hσdom v hv) hvi'
    have hev : ∀ᶠ v' in 𝓝 v, v' ∈ V ∧ σ v' ∈ N := by
      filter_upwards [hV.mem_nhds hv, (hσcont.continuousAt (hV.mem_nhds hv)).preimage_mem_nhds
        (hN.mem_nhds hvN)] with v' hv' hv'N using ⟨hv', hv'N⟩
    have hHa : AnalyticAt ℂ (H ∘ σA) v :=
      (hH (σ v) hvN).1.comp_of_eq (hσA v hv) (hcσ v hv).symm
    refine hHa.congr ?_
    filter_upwards [hev] with v' hv'
    simp only [Function.comp_apply]
    rw [(hH (σ v') hv'.2).2, hcσ v' hv'.1]

variable {S Z}

/-- The image of a closed analytic subset in the chart of local data is locally analytic. -/
theorem anb_locAnalytic_of_subData (D : anb_SubData S Z) {x : X} (hx : x ∈ D.N) :
    anb_LocAnalytic ((S.atlas.chart D.i).toFun '' (Z ∩ (S.atlas.chart D.i).dom))
      ((S.atlas.chart D.i).toFun x) := by
  set c := S.atlas.chart D.i
  have hxd := D.N_sub hx
  refine ⟨c.U ∩ D.O, c.isOpen_U.inter D.isOpen_O,
    ⟨(c.image_eq ▸ mem_image_of_mem _ hxd : c.toFun x ∈ an_zeroLocus c.U c.eqns).1,
      (D.trace x hxd).2 hx⟩, _, D.eqns, D.analyticOnNhd_eqns, fun z hz ↦ ?_⟩
  rw [D.eqns_eq_zero]
  constructor
  · rintro ⟨w, ⟨hwZ, hwd⟩, rfl⟩
    have hwN := (D.trace w hwd).1 hz.2
    exact ⟨(c.image_eq ▸ mem_image_of_mem _ hwd : c.toFun w ∈ an_zeroLocus c.U c.eqns).2,
      (D.zeros w hwN).1 hwZ⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨w, hwd, rfl⟩ : z ∈ c.toFun '' c.dom := c.image_eq ▸ ⟨hz.1, h1⟩
    have hwN := (D.trace w hwd).1 hz.2
    exact ⟨w, ⟨(D.zeros w hwN).2 h2, hwd⟩, rfl⟩

variable (S)

/-- **Krull dimension equals geometric dimension** for a closed analytic subset. -/
theorem anb_dimAt_eq_geomDim {Z : Set X} (hZ : an_IsClosedAnalytic S Z) (x : X) :
    an_dimAt S Z x = an_geomDim S Z x := by
  by_cases hx : x ∈ Z
  · obtain ⟨D, hxD⟩ := anb_exists_subData S hZ hx
    set c := S.atlas.chart D.i
    have hxd : x ∈ c.dom := D.N_sub hxD
    have hdim : an_dimAt S Z x = adim2_dimension c.n
        (adim2_germ c.n (c.toFun '' (Z ∩ c.dom)) (c.toFun x)) :=
      anb_dimension_chart_eq S.atlas S.isAnalytic Z _ D.i (S.atlas.mem_chartAt x) hxd
    rw [hdim]
    have hB := anb_locAnalytic_of_subData D hxD
    refine le_antisymm (le_iInf₂ fun W hW ↦ le_iInf fun hxW ↦ ?_) ?_
    · obtain ⟨O', hO', hO'W⟩ := anb_exists_open_trace c (hW.inter c.isOpen_dom)
      obtain ⟨a, haO', d, hpiece, hd⟩ := anb_exists_piece hB ⟨x, ⟨hx, hxd⟩, rfl⟩ O' hO'
        ((hO'W x hxd).2 ⟨hxW, hxd⟩)
      obtain ⟨y, hyd, rfl, hreg⟩ := anb_regular_of_piece S Z D.i hpiece
      have hyW := ((hO'W y hyd).1 haO').1
      rw [← hd]
      exact le_iSup₂_of_le (f := fun y _ ↦ ⨆ (d : ℕ) (_ : an_IsRegularOfDim S Z d y),
        ((d : ℕ∞) : WithBot ℕ∞)) y hyW (le_iSup₂_of_le d hreg le_rfl)
    · obtain ⟨O, hO, hpO, hle⟩ := anb_piece_le hB
      let W0 := c.dom ∩ c.toFun ⁻¹' O
      have hW0 : IsOpen W0 := (anb_continuousOn_toFun c).isOpen_inter_preimage c.isOpen_dom hO
      refine iInf₂_le_of_le W0 hW0 (iInf_le_of_le ⟨hxd, hpO⟩ ?_)
      refine iSup₂_le fun y hy ↦ iSup₂_le fun d hreg ↦ ?_
      exact hle _ hy.2 d (anb_piece_of_regular S Z D.i hy.1 hreg)
  · have hbot : an_geomDim S Z x = ⊥ := by
      refine le_antisymm (iInf₂_le_of_le Zᶜ hZ.1.isOpen_compl (iInf_le_of_le hx ?_)) bot_le
      exact iSup₂_le fun y hy ↦ iSup₂_le fun d hreg ↦ absurd hreg.1 hy
    rw [hbot, an_dimAt]
    set c := S.atlas.chart (S.atlas.chartAt x)
    have hxd : x ∈ c.dom := S.atlas.mem_chartAt x
    obtain ⟨O, hO, hON⟩ := anb_exists_open_trace c (hZ.1.isOpen_compl.inter c.isOpen_dom)
    have hI : adim2_ideal c.n (adim2_germ c.n (c.toFun '' (Z ∩ c.dom)) (c.toFun x)) = ⊤ := by
      rw [Ideal.eq_top_iff_one, anb_mem_ideal_germ_iff (F := fun _ ↦ 1) rfl]
      filter_upwards [anb_eventually_add_mem hO ((hON x hxd).2 ⟨hx, hxd⟩)] with z hzO hzA
      obtain ⟨w, ⟨hwZ, hwd⟩, hwz⟩ := hzA
      exact absurd hwZ ((hON w hwd).1 (hwz ▸ hzO)).1
    rw [adim2_dimension, hI]
    exact ringKrullDim_eq_bot_of_subsingleton

end Chart

end HodgeLean.Foundations.Analytic
