import HodgeLean.Foundations.Program.BraidBridgesThreeIsotopy
import HodgeLean.Foundations.Program.MarkedRootCoverDefs

/-! # Transport along a moving configuration with the base point fixed

For a continuous collision-free motion of twelve points avoiding the base point `mr_basePoint`,
the end map of the isotopy is a homeomorphism of the sphere fixing infinity and the base point,
carrying the initial points to the final ones, and every based family avoiding the moving points
ends at the image of its initial loop, up to based homotopy.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set
namespace HodgeLean.Foundations.Program

/-- Twelve points with the base point adjoined as the last point. -/
def b65x_adjoin (Q : ℝ → Fin 12 → ℂ) (t : ℝ) (j : Fin 13) : ℂ :=
  if h : j.val < 12 then Q t ⟨j.val, h⟩ else mr_basePoint

theorem b65x_adjoin_continuous (Q : ℝ → Fin 12 → ℂ) (hQ : Continuous Q) :
    Continuous (b65x_adjoin Q) := by
  apply continuous_pi
  intro j
  unfold b65x_adjoin
  by_cases h : j.val < 12
  · simp only [dite_eq_left h]; exact (continuous_apply _).comp hQ
  · simp only [dite_eq_right h]; exact continuous_const

theorem b65x_adjoin_cast (Q : ℝ → Fin 12 → ℂ) (t : ℝ) (j : Fin 12) :
    b65x_adjoin Q t j.castSucc = Q t j := by simp [b65x_adjoin]

theorem b65x_adjoin_last (Q : ℝ → Fin 12 → ℂ) (t : ℝ) :
    b65x_adjoin Q t (Fin.last 12) = mr_basePoint := by simp [b65x_adjoin]

theorem b65x_adjoin_injective (Q : ℝ → Fin 12 → ℂ) (t : ℝ) (hinj : Function.Injective (Q t))
    (hB : ∀ j, Q t j ≠ mr_basePoint) : Function.Injective (b65x_adjoin Q t) := by
  intro i j hij
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => rfl
    | cast j =>
      rw [b65x_adjoin_last, b65x_adjoin_cast] at hij
      exact absurd hij.symm (hB j)
  | cast i =>
    induction j using Fin.lastCases with
    | last =>
      rw [b65x_adjoin_last, b65x_adjoin_cast] at hij
      exact absurd hij (hB i)
    | cast j =>
      rw [b65x_adjoin_cast, b65x_adjoin_cast] at hij
      rw [hinj hij]

/-- Transport along a collision-free motion of twelve points. -/
theorem b65x_transport (Q : ℝ → Fin 12 → ℂ) (hQ : Continuous Q)
    (hinj : ∀ t ∈ Icc (0 : ℝ) 1, Function.Injective (Q t))
    (hB : ∀ t ∈ Icc (0 : ℝ) 1, ∀ j, Q t j ≠ mr_basePoint) :
    ∃ e : OnePoint ℂ ≃ₜ OnePoint ℂ,
      e (mr_basePoint : OnePoint ℂ) = (mr_basePoint : OnePoint ℂ) ∧
      e OnePoint.infty = OnePoint.infty ∧
      (∀ j, e (Q 0 j : OnePoint ℂ) = (Q 1 j : OnePoint ℂ)) ∧
      ∀ (K : C(unitInterval × unitInterval, OnePoint ℂ)),
        (∀ t, K (t, 0) = (mr_basePoint : OnePoint ℂ) ∧ K (t, 1) = (mr_basePoint : OnePoint ℂ)) →
        (∀ t s, K (t, s) ≠ OnePoint.infty ∧ ∀ j, K (t, s) ≠ (Q t j : OnePoint ℂ)) →
        ∀ (Y : Set (OnePoint ℂ)),
          (∀ w, w ≠ OnePoint.infty → (∀ j, w ≠ (Q 1 j : OnePoint ℂ)) → w ∈ Y) →
          ∀ {y : Y} (γ γ' : Path y y), (∀ s, (γ s : OnePoint ℂ) = K (1, s)) →
            (∀ s, (γ' s : OnePoint ℂ) = e (K (0, s))) → γ'.Homotopic γ := by
  have hinjA : ∀ t ∈ Icc (0 : ℝ) 1, Function.Injective (b65x_adjoin Q t) :=
    fun t ht ↦ b65x_adjoin_injective Q t (hinj t ht) (hB t ht)
  obtain ⟨Φ, E, hE, hbij, h0, htr⟩ :=
    b65x_isotopy_sphere (b65x_adjoin Q) (b65x_adjoin_continuous Q hQ) hinjA
  have hcont : Continuous (OnePoint.map (Φ 1)) := by
    have h : OnePoint.map (Φ 1) = fun w ↦ (E (1, w)).2 := by
      funext w; rw [hE]; rfl
    rw [h]
    exact continuous_snd.comp (E.continuous.comp (continuous_const.prodMk continuous_id))
  let e : OnePoint ℂ ≃ₜ OnePoint ℂ :=
    hcont.homeoOfEquivCompactToT2 (f := Equiv.ofBijective _ (b65x_map_bijective (hbij 1)))
  have he : ∀ w, e w = OnePoint.map (Φ 1) w := fun w ↦ rfl
  have htr1 : ∀ j : Fin 13, Φ 1 (b65x_adjoin Q 0 j) = b65x_adjoin Q 1 j :=
    fun j ↦ htr 1 ⟨zero_le_one, le_rfl⟩ j
  refine ⟨e, ?_, rfl, fun j ↦ ?_, fun K hKb hKa Y hY y γ γ' hγ hγ' ↦ ?_⟩
  · rw [he, OnePoint.map_some]
    have := htr1 (Fin.last 12)
    rw [b65x_adjoin_last, b65x_adjoin_last] at this
    rw [this]
  · rw [he, OnePoint.map_some]
    have := htr1 j.castSucc
    rw [b65x_adjoin_cast, b65x_adjoin_cast] at this
    rw [this]
  · apply b65x_family_end (b65x_adjoin Q) Φ E hE hbij h0 htr {j | j.val < 12} (Fin.last 12)
      (fun t _ ↦ by rw [b65x_adjoin_last, b65x_adjoin_last]) K
    · intro t
      rw [b65x_adjoin_last]; exact hKb t
    · intro t s
      refine ⟨(hKa t s).1, fun j hj ↦ ?_⟩
      have h := (hKa t s).2 ⟨j.val, hj⟩
      simpa [b65x_adjoin, dite_eq_left (show j.val < 12 from hj)] using h
    · intro w hw hj
      apply hY w hw
      intro j
      have h := hj j.castSucc (by simp)
      rwa [b65x_adjoin_cast] at h
    · exact hγ
    · intro s; rw [hγ', he]

/-- The end map of a transport carries a based family of loops avoiding the initial points to a
based homotopy avoiding the final points. -/
theorem b65x_transport_static (Q0 Q1 : Fin 12 → ℂ) (e : OnePoint ℂ ≃ₜ OnePoint ℂ)
    (heB : e (mr_basePoint : OnePoint ℂ) = (mr_basePoint : OnePoint ℂ))
    (heI : e OnePoint.infty = OnePoint.infty)
    (heQ : ∀ j, e (Q0 j : OnePoint ℂ) = (Q1 j : OnePoint ℂ))
    (F : unitInterval × unitInterval → ℂ) (hF : Continuous F)
    (hFb : ∀ t, F (t, 0) = mr_basePoint ∧ F (t, 1) = mr_basePoint)
    (hFa : ∀ t s j, F (t, s) ≠ Q0 j)
    (Y : Set (OnePoint ℂ))
    (hY : ∀ w, w ≠ OnePoint.infty → (∀ j, w ≠ (Q1 j : OnePoint ℂ)) → w ∈ Y)
    {y : Y} (hy : (y : OnePoint ℂ) = (mr_basePoint : OnePoint ℂ)) (γ γ' : Path y y)
    (hγ : ∀ s, (γ s : OnePoint ℂ) = e (F (0, s))) (hγ' : ∀ s, (γ' s : OnePoint ℂ) = e (F (1, s))) :
    γ.Homotopic γ' := by
  refine ⟨{ toFun := fun q ↦ ⟨e (F q), ?_⟩
            continuous_toFun := ?_
            map_zero_left := fun s ↦ Subtype.ext (hγ s).symm
            map_one_left := fun s ↦ Subtype.ext (hγ' s).symm
            prop' := fun t s hs ↦ ?_ }⟩
  · apply hY
    · intro h
      rw [← heI] at h
      exact OnePoint.coe_ne_infty _ (e.injective h)
    · intro j h
      rw [← heQ j] at h
      exact hFa q.1 q.2 j (OnePoint.coe_injective (e.injective h))
  · exact (e.continuous.comp (OnePoint.continuous_coe.comp hF)).subtype_mk _
  · rcases hs with rfl | rfl
    · apply Subtype.ext
      change e (F (t, 0)) = ((γ 0 : Y) : OnePoint ℂ)
      rw [γ.source, hy, (hFb t).1, heB]
    · apply Subtype.ext
      change e (F (t, 1)) = ((γ 1 : Y) : OnePoint ℂ)
      rw [γ.target, hy, (hFb t).2, heB]

end HodgeLean.Foundations.Program

namespace HodgeLean.Foundations.Program

/-- Finitely many points with the base point adjoined as the last point. -/
def b65x_adjoinN {n : ℕ} (Q : ℝ → Fin n → ℂ) (t : ℝ) (j : Fin (n + 1)) : ℂ :=
  if h : j.val < n then Q t ⟨j.val, h⟩ else mr_basePoint

theorem b65x_adjoinN_cast {n : ℕ} (Q : ℝ → Fin n → ℂ) (t : ℝ) (j : Fin n) :
    b65x_adjoinN Q t j.castSucc = Q t j := by simp [b65x_adjoinN]

theorem b65x_adjoinN_last {n : ℕ} (Q : ℝ → Fin n → ℂ) (t : ℝ) :
    b65x_adjoinN Q t (Fin.last n) = mr_basePoint := by simp [b65x_adjoinN]

/-- Transport along a collision-free motion of finitely many points, for families that avoid a
chosen subset of them. -/
theorem b65x_transportS {n : ℕ} (Q : ℝ → Fin n → ℂ) (hQ : Continuous Q)
    (hinj : ∀ t ∈ Icc (0 : ℝ) 1, Function.Injective (Q t))
    (hB : ∀ t ∈ Icc (0 : ℝ) 1, ∀ j, Q t j ≠ mr_basePoint) (S : Set (Fin n)) :
    ∃ e : OnePoint ℂ ≃ₜ OnePoint ℂ,
      e (mr_basePoint : OnePoint ℂ) = (mr_basePoint : OnePoint ℂ) ∧
      e OnePoint.infty = OnePoint.infty ∧
      (∀ j, e (Q 0 j : OnePoint ℂ) = (Q 1 j : OnePoint ℂ)) ∧
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
  refine ⟨e, ?_, rfl, fun j ↦ ?_, fun K hKb hKa Y hY y γ γ' hγ hγ' ↦ ?_⟩
  · rw [he, OnePoint.map_some]
    have := htr1 (Fin.last n)
    rw [b65x_adjoinN_last, b65x_adjoinN_last] at this
    rw [this]
  · rw [he, OnePoint.map_some]
    have := htr1 j.castSucc
    rw [b65x_adjoinN_cast, b65x_adjoinN_cast] at this
    rw [this]
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
