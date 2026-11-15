import HodgeLean.Adapters.IntersectionProductMovingRobertsTranslate

/-! # General translates over a base, and along a line of translations

Stage A3.3, the second input of Bloch's homotopy: Kleiman's transversality of a general
translate for the homogeneous `ℙⁿ`, over a base, as a dimension count on affine cones. The
coordinates are split into projective coordinates `x_σ`, on which a matrix `M` acts, and base
coordinates `t_τ`, which it fixes.

* `a3h_generic_translate_rel`: for a generic `M`, every relevant prime of `ℂ[x, t]` containing the
  ideal of `V(P_W) × (base)` and the `M`-translate of a prime `I_C` of `ℂ[x, t]` has the expected
  dimension `dim C + dim W - (N + 1)`: a general translate of a family of cones over the base
  meets `W × (base)` properly.
* `a3h_generic_line`: the same along the line of translations `h_s = (1 - s) I + s M`: for a
  generic `M`, every prime of `ℂ[x, t][s]` containing `P_W` and the `h_s`-translate of `I_C`, not
  containing `s x_j`, has dimension at most `dim C + dim W + 1 - (N + 1)`. So the family
  `s ↦ h_s⁻¹(C)` over `𝔸¹_s ∖ {0}` meets `W × 𝔸¹_s` properly, including over the special values
  of `s`; its fibre over `s = 0` is `C` itself and over `s = 1` the translate `M⁻¹(C)`.

Both are the linear incidence bound `a3r_generic_linear` on the incidence algebra
`ℂ[C] ⊗ ℂ[W]` (with a polynomial variable `s` for the line), whose relations `M w = c`
(respectively `s M w = c - (1 - s) w`) are solved for a column of `M`.

Source: Kleiman, *The transversality of a general translate*, Compositio Math. 28 (1974),
287–297, Theorem 2 (dimension part) and its proof; S. Bloch, *The moving lemma for higher Chow
groups*, J. Algebraic Geom. 3 (1994), §2 (the family of translates over the line).
HC no distance; AV milestone no distance.
-/

noncomputable section

open MvPolynomial TensorProduct

namespace HodgeLean.Adapters

section Translate

variable {σ τ : Type} [Fintype σ]

/-- The translation `x ↦ M x` on `ℂ[x, t]`, fixing the base coordinates. -/
def a3h_substT (a : σ × σ → ℂ) : MvPolynomial (σ ⊕ τ) ℂ →ₐ[ℂ] MvPolynomial (σ ⊕ τ) ℂ :=
  aeval (Sum.elim (fun k => ∑ l, C (a (k, l)) * X (Sum.inl l)) fun t => X (Sum.inr t))

theorem a3h_substT_inl (a : σ × σ → ℂ) (k : σ) :
    a3h_substT (τ := τ) a (X (Sum.inl k)) = ∑ l, C (a (k, l)) * X (Sum.inl l) := by
  simp [a3h_substT]

theorem a3h_substT_inr (a : σ × σ → ℂ) (t : τ) :
    a3h_substT (τ := τ) a (X (Sum.inr t)) = X (Sum.inr t) := by
  simp [a3h_substT]

/-- The line of translations `x ↦ h_s x = (1 - s) x + s M x` on `ℂ[x, t]`, with values in
`ℂ[x, t][s]`, fixing the base coordinates. -/
def a3h_substLine (a : σ × σ → ℂ) :
    MvPolynomial (σ ⊕ τ) ℂ →ₐ[ℂ] Polynomial (MvPolynomial (σ ⊕ τ) ℂ) :=
  aeval (Sum.elim (fun k => (1 - Polynomial.X) * Polynomial.C (X (Sum.inl k)) +
      Polynomial.X * Polynomial.C (∑ l, C (a (k, l)) * X (Sum.inl l)))
    fun t => Polynomial.C (X (Sum.inr t)))

theorem a3h_substLine_inl (a : σ × σ → ℂ) (k : σ) :
    a3h_substLine (τ := τ) a (X (Sum.inl k)) = (1 - Polynomial.X) * Polynomial.C (X (Sum.inl k)) +
      Polynomial.X * Polynomial.C (∑ l, C (a (k, l)) * X (Sum.inl l)) := by
  simp [a3h_substLine]

theorem a3h_substLine_inr (a : σ × σ → ℂ) (t : τ) :
    a3h_substLine (τ := τ) a (X (Sum.inr t)) = Polynomial.C (X (Sum.inr t)) := by
  simp [a3h_substLine]

/-- The line of translations at `s = 0` is the identity. -/
theorem a3h_substLine_eval_zero (a : σ × σ → ℂ) (F : MvPolynomial (σ ⊕ τ) ℂ) :
    (a3h_substLine a F).eval 0 = F := by
  have : (Polynomial.evalRingHom (0 : MvPolynomial (σ ⊕ τ) ℂ)).comp
      (a3h_substLine (τ := τ) a).toRingHom = RingHom.id _ := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
    · simp [a3h_substLine]
    · rcases i with k | t
      · simp [a3h_substLine_inl]
      · simp [a3h_substLine_inr]
  exact congrArg (fun φ : MvPolynomial (σ ⊕ τ) ℂ →+* MvPolynomial (σ ⊕ τ) ℂ => φ F) this

/-- The line of translations at `s = 1` is the translation by `M`. -/
theorem a3h_substLine_eval_one (a : σ × σ → ℂ) (F : MvPolynomial (σ ⊕ τ) ℂ) :
    (a3h_substLine a F).eval 1 = a3h_substT a F := by
  have : (Polynomial.evalRingHom (1 : MvPolynomial (σ ⊕ τ) ℂ)).comp
      (a3h_substLine (τ := τ) a).toRingHom = (a3h_substT a).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
    · simp [a3h_substLine, a3h_substT]
    · rcases i with k | t
      · simp [a3h_substLine_inl, a3h_substT_inl, Polynomial.eval_finsetSum]
      · simp [a3h_substLine_inr, a3h_substT_inr]
  exact congrArg (fun φ : MvPolynomial (σ ⊕ τ) ℂ →+* MvPolynomial (σ ⊕ τ) ℂ => φ F) this

variable [DecidableEq σ] [Fintype τ]

/-- **Transversality of a general translate over a base.** For a generic matrix `M`, every
relevant prime `Q` of `ℂ[x, t]` containing `P_W` (constant along the base) and the `M`-translate
of `I_C` has `dim Q + (N + 1) ≤ dim I_C + dim P_W` (affine cone dimensions).
Source: Kleiman, *The transversality of a general translate*, Compositio Math. 28 (1974),
287–297, Theorem 2 (dimension part, over a base). -/
theorem a3h_generic_translate_rel (IC : Ideal (MvPolynomial (σ ⊕ τ) ℂ)) [IC.IsPrime]
    (PW : Ideal (MvPolynomial σ ℂ)) [PW.IsPrime] :
    a3r_Generic {a : σ × σ → ℂ | ∀ Q : Ideal (MvPolynomial (σ ⊕ τ) ℂ), Q.IsPrime →
      (∀ F ∈ PW, rename Sum.inl F ∈ Q) → (∀ F ∈ IC, a3h_substT a F ∈ Q) →
      ∀ j, X (Sum.inl j) ∉ Q →
      ringKrullDim (MvPolynomial (σ ⊕ τ) ℂ ⧸ Q) + Fintype.card σ ≤
        ringKrullDim (MvPolynomial (σ ⊕ τ) ℂ ⧸ IC) + ringKrullDim (MvPolynomial σ ℂ ⧸ PW)} := by
  classical
  set A := MvPolynomial (σ ⊕ τ) ℂ
  set D := (A ⧸ IC) ⊗[ℂ] (MvPolynomial σ ℂ ⧸ PW)
  have : Algebra.FiniteType ℂ (A ⧸ IC) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ _) (Ideal.Quotient.mkₐ_surjective ℂ _)
  have : Algebra.FiniteType ℂ (MvPolynomial σ ℂ ⧸ PW) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ _) (Ideal.Quotient.mkₐ_surjective ℂ _)
  refine (a3r_generic_iInter_fintype _ fun j => a3r_generic_linear (ρ := σ) D
    (fun k => 1 ⊗ₜ Ideal.Quotient.mk PW (X k))
    (fun i => Ideal.Quotient.mk IC (X (Sum.inl i)) ⊗ₜ 1) j).mono
    fun a ha Q hQ hWQ hCQ j hj => ?_
  have hle : IC ≤ Ideal.comap (a3h_substT a) Q := fun F hF => hCQ F hF
  have hle' : PW ≤ Ideal.comap (rename (R := ℂ) (Sum.inl : σ → σ ⊕ τ)) Q := fun F hF => hWQ F hF
  let θ₁ : A ⧸ IC →ₐ[ℂ] A ⧸ Q := Ideal.quotientMapₐ Q _ hle
  let θ₂ : MvPolynomial σ ℂ ⧸ PW →ₐ[ℂ] A ⧸ Q := Ideal.quotientMapₐ Q (rename Sum.inl) hle'
  let Θ : D →ₐ[ℂ] A ⧸ Q := Algebra.TensorProduct.lift θ₁ θ₂ fun _ _ => Commute.all _ _
  have hΘ1 : ∀ F, Θ (Ideal.Quotient.mk IC F ⊗ₜ 1) = Ideal.Quotient.mk Q (a3h_substT a F) := by
    intro F
    change θ₁ (Ideal.Quotient.mk IC F) * θ₂ 1 = _
    rw [map_one, mul_one]
    rfl
  have hΘ2 : ∀ F, Θ (1 ⊗ₜ Ideal.Quotient.mk PW F) = Ideal.Quotient.mk Q (rename Sum.inl F) := by
    intro F
    change θ₁ 1 * θ₂ (Ideal.Quotient.mk PW F) = _
    rw [map_one, one_mul]
    rfl
  have hsurj : Function.Surjective Θ := by
    -- the generators `x_k` (from `W`) and `t` (from `C`) lie in the image
    let S := Θ.range
    have hgen : ∀ i, Ideal.Quotient.mk Q (X i : A) ∈ S := by
      rintro (k | t)
      · exact ⟨1 ⊗ₜ Ideal.Quotient.mk PW (X k), (hΘ2 _).trans (by rw [rename_X])⟩
      · exact ⟨Ideal.Quotient.mk IC (X (Sum.inr t)) ⊗ₜ 1,
          (hΘ1 _).trans (by rw [a3h_substT_inr])⟩
    intro y
    obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective y
    induction F using MvPolynomial.induction_on with
    | C c => exact ⟨algebraMap ℂ D c, (Θ.commutes c).trans rfl⟩
    | add p q hp hq =>
      rw [map_add]
      exact S.add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul]
      exact S.mul_mem hp (hgen i)
  set 𝔓 := RingHom.ker (Θ : D →+* A ⧸ Q)
  have h𝔓 : 𝔓.IsPrime := RingHom.ker_isPrime _
  have hj' : (1 : A ⧸ IC) ⊗ₜ Ideal.Quotient.mk PW (X j) ∉ 𝔓 := by
    rw [RingHom.mem_ker]
    change Θ _ ≠ 0
    rw [hΘ2, rename_X]
    exact fun h => hj (Ideal.Quotient.eq_zero_iff_mem.1 h)
  have heq : ∀ i, ∑ k, algebraMap ℂ D (a (i, k)) * (1 ⊗ₜ Ideal.Quotient.mk PW (X k)) -
      Ideal.Quotient.mk IC (X (Sum.inl i)) ⊗ₜ 1 ∈ 𝔓 := by
    intro i
    rw [RingHom.mem_ker]
    change Θ _ = 0
    rw [map_sub, map_sum, hΘ1, a3h_substT_inl, map_sum, sub_eq_zero]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, AlgHom.commutes, hΘ2, map_mul, rename_X]
    rfl
  have hb := ha j 𝔓 h𝔓 hj' heq
  have : Nontrivial (A ⧸ IC) := Ideal.Quotient.nontrivial_iff.2 (Ideal.IsPrime.ne_top inferInstance)
  have : Nontrivial (MvPolynomial σ ℂ ⧸ PW) :=
    Ideal.Quotient.nontrivial_iff.2 (Ideal.IsPrime.ne_top inferInstance)
  have hD : ringKrullDim D = ringKrullDim (A ⧸ IC) + ringKrullDim (MvPolynomial σ ℂ ⧸ PW) :=
    hc9k8_ringKrullDim_tensorProduct
  have hDP : ringKrullDim (D ⧸ 𝔓) = ringKrullDim (A ⧸ Q) :=
    ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective
      (f := (Θ : D →+* A ⧸ Q)) hsurj)
  rwa [hD, hDP] at hb

/-- **Transversality along the line of translations, over a base.** For a generic matrix `M`,
every prime `Q` of `ℂ[x, t][s]` containing `P_W` and the `h_s`-translate of `I_C`,
`h_s = (1 - s) I + s M`, and not containing `s x_j`, has
`dim Q + (N + 1) ≤ dim I_C + dim P_W + 1`: the family of translates `s ↦ h_s⁻¹(C)` meets
`W × 𝔸¹_s` properly away from `s = 0`, also at the special values of `s`.
Source: Kleiman, *The transversality of a general translate*, Compositio Math. 28 (1974),
287–297, proof of Theorem 2; S. Bloch, *The moving lemma for higher Chow groups*,
J. Algebraic Geom. 3 (1994), §2. -/
theorem a3h_generic_line (IC : Ideal (MvPolynomial (σ ⊕ τ) ℂ)) [IC.IsPrime]
    (PW : Ideal (MvPolynomial σ ℂ)) [PW.IsPrime] :
    a3r_Generic {a : σ × σ → ℂ | ∀ Q : Ideal (Polynomial (MvPolynomial (σ ⊕ τ) ℂ)), Q.IsPrime →
      (∀ F ∈ PW, Polynomial.C (rename Sum.inl F) ∈ Q) → (∀ F ∈ IC, a3h_substLine a F ∈ Q) →
      ∀ j, Polynomial.X * Polynomial.C (X (Sum.inl j)) ∉ Q →
      ringKrullDim (Polynomial (MvPolynomial (σ ⊕ τ) ℂ) ⧸ Q) + Fintype.card σ ≤
        ringKrullDim (MvPolynomial (σ ⊕ τ) ℂ ⧸ IC) + ringKrullDim (MvPolynomial σ ℂ ⧸ PW) +
          1} := by
  classical
  set A := MvPolynomial (σ ⊕ τ) ℂ
  set D₀ := (A ⧸ IC) ⊗[ℂ] (MvPolynomial σ ℂ ⧸ PW)
  set D := Polynomial D₀
  have : Algebra.FiniteType ℂ (A ⧸ IC) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ _) (Ideal.Quotient.mkₐ_surjective ℂ _)
  have : Algebra.FiniteType ℂ (MvPolynomial σ ℂ ⧸ PW) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ _) (Ideal.Quotient.mkₐ_surjective ℂ _)
  have : Algebra.FiniteType ℂ D := Algebra.FiniteType.trans (S := D₀) inferInstance inferInstance
  let w : σ → D₀ := fun k => 1 ⊗ₜ Ideal.Quotient.mk PW (X k)
  let c : σ → D₀ := fun i => Ideal.Quotient.mk IC (X (Sum.inl i)) ⊗ₜ 1
  refine (a3r_generic_iInter_fintype _ fun j => a3r_generic_linear (ρ := σ) D
    (fun k => Polynomial.X * Polynomial.C (w k))
    (fun i => Polynomial.C (c i) - (1 - Polynomial.X) * Polynomial.C (w i)) j).mono
    fun a ha Q hQ hWQ hCQ j hj => ?_
  set R := Polynomial A
  have hle : IC ≤ Ideal.comap (a3h_substLine a) Q := fun F hF => hCQ F hF
  have hle' : PW ≤ Ideal.comap ((Polynomial.CAlgHom (R := ℂ) (A := A)).comp
      (rename (R := ℂ) (Sum.inl : σ → σ ⊕ τ))) Q := fun F hF => hWQ F hF
  let θ₁ : A ⧸ IC →ₐ[ℂ] R ⧸ Q := Ideal.quotientMapₐ Q _ hle
  let θ₂ : MvPolynomial σ ℂ ⧸ PW →ₐ[ℂ] R ⧸ Q := Ideal.quotientMapₐ Q _ hle'
  let Θ₀ : D₀ →ₐ[ℂ] R ⧸ Q := Algebra.TensorProduct.lift θ₁ θ₂ fun _ _ => Commute.all _ _
  let Θ : D →+* R ⧸ Q := Polynomial.eval₂RingHom Θ₀.toRingHom (Ideal.Quotient.mk Q Polynomial.X)
  have hΘ1 : ∀ F, Θ (Polynomial.C (Ideal.Quotient.mk IC F ⊗ₜ 1)) =
      Ideal.Quotient.mk Q (a3h_substLine a F) := by
    intro F
    refine (Polynomial.eval₂_C _ _).trans ?_
    change θ₁ (Ideal.Quotient.mk IC F) * θ₂ 1 = _
    rw [map_one, mul_one]
    rfl
  have hΘ2 : ∀ F, Θ (Polynomial.C (1 ⊗ₜ Ideal.Quotient.mk PW F)) =
      Ideal.Quotient.mk Q (Polynomial.C (rename Sum.inl F)) := by
    intro F
    refine (Polynomial.eval₂_C _ _).trans ?_
    change θ₁ 1 * θ₂ (Ideal.Quotient.mk PW F) = _
    rw [map_one, one_mul]
    rfl
  have hΘX : Θ Polynomial.X = Ideal.Quotient.mk Q Polynomial.X := Polynomial.eval₂_X _ _
  have hΘc : ∀ z : ℂ, Θ (algebraMap ℂ D z) = algebraMap ℂ (R ⧸ Q) z := by
    intro z
    rw [Polynomial.algebraMap_apply]
    exact (Polynomial.eval₂_C _ _).trans (Θ₀.commutes z)
  have hsurj : Function.Surjective Θ := by
    let S := Θ.range
    have hgenA : ∀ i, Ideal.Quotient.mk Q (Polynomial.C (X i : A)) ∈ S := by
      rintro (k | t)
      · exact ⟨Polynomial.C (1 ⊗ₜ Ideal.Quotient.mk PW (X k)), (hΘ2 _).trans (by rw [rename_X])⟩
      · exact ⟨Polynomial.C (Ideal.Quotient.mk IC (X (Sum.inr t)) ⊗ₜ 1),
          (hΘ1 _).trans (by rw [a3h_substLine_inr])⟩
    have hA : ∀ F : A, Ideal.Quotient.mk Q (Polynomial.C F) ∈ S := by
      intro F
      induction F using MvPolynomial.induction_on with
      | C z =>
        refine ⟨algebraMap ℂ D z, (hΘc z).trans ?_⟩
        rw [← Ideal.Quotient.mk_algebraMap, Polynomial.algebraMap_apply,
          MvPolynomial.algebraMap_eq]
      | add p q hp hq =>
        rw [Polynomial.C_add, map_add]
        exact S.add_mem hp hq
      | mul_X p i hp =>
        rw [Polynomial.C_mul, map_mul]
        exact S.mul_mem hp (hgenA i)
    intro y
    obtain ⟨G, rfl⟩ := Ideal.Quotient.mk_surjective y
    induction G using Polynomial.induction_on' with
    | add p q hp hq =>
      rw [map_add]
      exact S.add_mem hp hq
    | monomial m F =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow]
      exact S.mul_mem (hA F) (S.pow_mem ⟨Polynomial.X, hΘX⟩ m)
  set 𝔓 := RingHom.ker Θ
  have h𝔓 : 𝔓.IsPrime := RingHom.ker_isPrime _
  have hj' : Polynomial.X * Polynomial.C (w j) ∉ 𝔓 := by
    rw [RingHom.mem_ker, map_mul, hΘX, hΘ2, rename_X, ← map_mul]
    exact fun h => hj (Ideal.Quotient.eq_zero_iff_mem.1 h)
  have hc : ∀ z : ℂ, algebraMap ℂ (R ⧸ Q) z =
      Ideal.Quotient.mk Q (Polynomial.C (C z)) := fun z => by
    rw [← Ideal.Quotient.mk_algebraMap, Polynomial.algebraMap_apply,
      MvPolynomial.algebraMap_eq]
  have heq : ∀ i, ∑ k, algebraMap ℂ D (a (i, k)) * (Polynomial.X * Polynomial.C (w k)) -
      (Polynomial.C (c i) - (1 - Polynomial.X) * Polynomial.C (w i)) ∈ 𝔓 := by
    intro i
    rw [RingHom.mem_ker]
    simp only [w, c, map_sum, map_mul, map_sub, map_one, hΘc, hΘX, hΘ1, hΘ2, rename_X,
      a3h_substLine_inl, map_add, hc]
    rw [Finset.mul_sum]
    ring_nf
    rw [sub_eq_zero]
    exact Finset.sum_congr rfl fun x _ => by ring
  have hb := ha j 𝔓 h𝔓 hj' heq
  have : Nontrivial (A ⧸ IC) := Ideal.Quotient.nontrivial_iff.2 (Ideal.IsPrime.ne_top inferInstance)
  have : Nontrivial (MvPolynomial σ ℂ ⧸ PW) :=
    Ideal.Quotient.nontrivial_iff.2 (Ideal.IsPrime.ne_top inferInstance)
  have : IsNoetherianRing D₀ := Algebra.FiniteType.isNoetherianRing ℂ D₀
  have hD : ringKrullDim D = ringKrullDim (A ⧸ IC) + ringKrullDim (MvPolynomial σ ℂ ⧸ PW) + 1 := by
    rw [Polynomial.ringKrullDim_of_isNoetherianRing, hc9k8_ringKrullDim_tensorProduct]
  have hDP : ringKrullDim (D ⧸ 𝔓) = ringKrullDim (R ⧸ Q) :=
    ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective (f := Θ) hsurj)
  rwa [hD, hDP] at hb

end Translate

end HodgeLean.Adapters
