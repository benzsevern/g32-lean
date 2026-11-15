import HodgeLean.Foundations.Program.BraidBridgesThreeTransport
import HodgeLean.Foundations.Program.RadialTransportIsotopy

/-! # Transport retaining the ambient motion -/
noncomputable section
open Set
namespace HodgeLean.Foundations.Program

/-- Transport with the sphere family and its literal endpoint retained.
Source: `b65x_isotopy_sphere`; `b65x_family_end`. -/
theorem rtc_transport_motion {n : ℕ} (Q : ℝ → Fin n → ℂ) (hQ : Continuous Q)
    (hinj : ∀ t ∈ Icc (0 : ℝ) 1, Function.Injective (Q t))
    (hB : ∀ t ∈ Icc (0 : ℝ) 1, ∀ j, Q t j ≠ mr_basePoint) (S : Set (Fin n)) :
    ∃ e : OnePoint ℂ ≃ₜ OnePoint ℂ,
      e (mr_basePoint : OnePoint ℂ) = (mr_basePoint : OnePoint ℂ) ∧
      e OnePoint.infty = OnePoint.infty ∧
      (∀ j, e (Q 0 j : OnePoint ℂ) = (Q 1 j : OnePoint ℂ)) ∧
      ∃ F : C(unitInterval × OnePoint ℂ, OnePoint ℂ),
        (∀ t, Function.Bijective (fun z ↦ F (t, z))) ∧
        (∀ z, F (0, z) = z) ∧
        (∀ t, F (t, OnePoint.infty) = OnePoint.infty) ∧
        (∀ t j, F (t, (Q 0 j : OnePoint ℂ)) = (Q t j : OnePoint ℂ)) ∧
        (∀ z, F (1, z) = e z) ∧
      ∀ (K : C(unitInterval × unitInterval, OnePoint ℂ)),
        (∀ t, K (t, 0) = (mr_basePoint : OnePoint ℂ) ∧ K (t, 1) = (mr_basePoint : OnePoint ℂ)) →
        (∀ t s, K (t, s) ≠ OnePoint.infty ∧ ∀ j ∈ S, K (t, s) ≠ (Q t j : OnePoint ℂ)) →
        ∀ (Y : Set (OnePoint ℂ)),
          (∀ w, w ≠ OnePoint.infty → (∀ j ∈ S, w ≠ (Q 1 j : OnePoint ℂ)) → w ∈ Y) →
          ∀ {y : Y} (γ γ' : Path y y), (∀ s, (γ s : OnePoint ℂ) = K (1, s)) →
            (∀ s, (γ' s : OnePoint ℂ) = e (K (0, s))) → γ'.Homotopic γ := by
  have hcA : Continuous (b65x_adjoinN Q) := by
    apply continuous_pi
    intro j
    unfold b65x_adjoinN
    by_cases h : j.val < n
    · simp only [dite_eq_left h]; exact (continuous_apply _).comp hQ
    · simp only [dite_eq_right h]; exact continuous_const
  have hinjA : ∀ t ∈ Icc (0 : ℝ) 1, Function.Injective (b65x_adjoinN Q t) := by
    intro t ht i j hij
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => rfl
      | cast j =>
        rw [b65x_adjoinN_last, b65x_adjoinN_cast] at hij
        exact absurd hij.symm (hB t ht j)
    | cast i =>
      induction j using Fin.lastCases with
      | last =>
        rw [b65x_adjoinN_last, b65x_adjoinN_cast] at hij
        exact absurd hij (hB t ht i)
      | cast j =>
        rw [b65x_adjoinN_cast, b65x_adjoinN_cast] at hij
        rw [hinj t ht hij]
  obtain ⟨Φ, E, hE, hbij, h0, htr⟩ := b65x_isotopy_sphere (b65x_adjoinN Q) hcA hinjA
  have hcont : Continuous (OnePoint.map (Φ 1)) := by
    have h : OnePoint.map (Φ 1) = fun w ↦ (E (1, w)).2 := by
      funext w; rw [hE]; rfl
    rw [h]
    exact continuous_snd.comp (E.continuous.comp (continuous_const.prodMk continuous_id))
  let e : OnePoint ℂ ≃ₜ OnePoint ℂ :=
    hcont.homeoOfEquivCompactToT2 (f := Equiv.ofBijective _ (b65x_map_bijective (hbij 1)))
  have he : ∀ w, e w = OnePoint.map (Φ 1) w := fun w ↦ rfl
  have htr1 : ∀ j : Fin (n + 1), Φ 1 (b65x_adjoinN Q 0 j) = b65x_adjoinN Q 1 j :=
    fun j ↦ htr 1 ⟨zero_le_one, le_rfl⟩ j
  let F : C(unitInterval × OnePoint ℂ, OnePoint ℂ) :=
    ⟨fun q ↦ (E q).2, continuous_snd.comp E.continuous⟩
  have hF (t : unitInterval) (w : OnePoint ℂ) :
      F (t, w) = OnePoint.map (Φ t) w := by
    change (E (t, w)).2 = _
    rw [hE]
  refine ⟨e, ?_, rfl, fun j ↦ ?_, F, ?_, ?_, ?_, ?_, ?_,
    fun K hKb hKa Y hY y γ γ' hγ hγ' ↦ ?_⟩
  · rw [he, OnePoint.map_some]
    have := htr1 (Fin.last n)
    rw [b65x_adjoinN_last, b65x_adjoinN_last] at this
    rw [this]
  · rw [he, OnePoint.map_some]
    have := htr1 j.castSucc
    rw [b65x_adjoinN_cast, b65x_adjoinN_cast] at this
    rw [this]
  · intro t
    simpa only [hF] using b65x_map_bijective (hbij t)
  · intro w
    rw [hF]
    induction w using OnePoint.rec with
    | infty => rfl
    | coe z => simpa only [OnePoint.map_some, Set.Icc.coe_zero, h0]
  · intro t
    rw [hF]
    rfl
  · intro t j
    rw [hF, OnePoint.map_some]
    have ht := htr t t.property j.castSucc
    rw [b65x_adjoinN_cast, b65x_adjoinN_cast] at ht
    rw [ht]
  · intro z
    rw [hF, he, Set.Icc.coe_one]
  · apply b65x_family_end (b65x_adjoinN Q) Φ E hE hbij h0 htr
      {j | ∃ h : j.val < n, (⟨j.val, h⟩ : Fin n) ∈ S} (Fin.last n)
      (fun t _ ↦ by rw [b65x_adjoinN_last, b65x_adjoinN_last]) K
    · intro t
      rw [b65x_adjoinN_last]; exact hKb t
    · intro t s
      refine ⟨(hKa t s).1, fun j hj ↦ ?_⟩
      obtain ⟨hjn, hjS⟩ := hj
      have h := (hKa t s).2 ⟨j.val, hjn⟩ hjS
      simpa [b65x_adjoinN, dite_eq_left hjn] using h
    · intro w hw hj
      apply hY w hw
      intro j hjS
      have h := hj j.castSucc ⟨j.isLt, by simpa using hjS⟩
      rwa [b65x_adjoinN_cast] at h
    · exact hγ
    · intro s; rw [hγ', he]


end HodgeLean.Foundations.Program
