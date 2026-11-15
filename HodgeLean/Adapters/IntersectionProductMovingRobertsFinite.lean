import HodgeLean.Adapters.IntersectionProductMovingRobertsCone

/-! # Finite linear projections

A linear projection `π_ℓ : V(I) → ℙⁿ` from a centre `L = V(ℓ)` missing `V(I)` is finite. In
algebra: if a power of every coordinate lies in `I + (ℓ_0, …, ℓ_n)` for a homogeneous ideal `I`,
then `ℂ[x]/I` is a finite module over `ℂ[y_0, …, y_n]` through `y_i ↦ ℓ_i`
(`a3r_finite_of_pow_mem`, graded Nakayama). For a homogeneous prime `I` with affine cone of
dimension `n + 1`, a generic centre of codimension `n + 1` misses `V(I)`, by the linear incidence
bound, so the generic projection is finite (`a3r_generic_finite`). Along a finite projection a
subvariety and its image have the same dimension (`a3r_dim_eq_of_finite`).

Source: Shafarevich, *Basic Algebraic Geometry 1*, I.5.3, Theorem 1.15 (projections from a
centre disjoint from `X` are finite); Bruns–Herzog, *Cohen–Macaulay Rings*, Proposition 1.5.4;
J. Roberts, *Chow's moving lemma* (1972), §1. HC no distance; AV milestone no distance.
-/

noncomputable section

open MvPolynomial

namespace HodgeLean.Adapters

section Finite

variable {ρ σ : Type} [Fintype ρ] [Fintype σ]

omit [Fintype σ] in
/-- Multiplication by a homogeneous polynomial shifts homogeneous components. -/
theorem a3r_homogeneousComponent_mul (L g : MvPolynomial σ ℂ) {d : ℕ} (hL : L.IsHomogeneous d)
    (m : ℕ) : homogeneousComponent (m + d) (L * g) = L * homogeneousComponent m g := by
  classical
  conv_lhs => rw [← sum_homogeneousComponent g, Finset.mul_sum, map_sum]
  rw [Finset.sum_eq_single m]
  · rw [homogeneousComponent_of_mem (hL.mul (homogeneousComponent_isHomogeneous m g)),
      ite_eq_left_iff.2 fun h => absurd (add_comm _ _) h]
  · intro j _ hj
    rw [homogeneousComponent_of_mem (hL.mul (homogeneousComponent_isHomogeneous j g)), ite_eq_right_iff.2 fun h => by omega]
  · intro hm
    rw [Finset.mem_range, not_lt] at hm
    rw [homogeneousComponent_eq_zero m g (by omega), mul_zero, map_zero]

omit [Fintype ρ] in
theorem a3r_lin_X_isHomogeneous (ℓ : Matrix ρ σ ℂ) (i : ρ) : (a3r_lin ℓ (X i)).IsHomogeneous 1 := by
  rw [a3r_lin_X]
  exact IsHomogeneous.sum _ _ _ fun k _ => by
    simpa using (isHomogeneous_C σ (ℓ i k)).mul (isHomogeneous_X ℂ k)

attribute [local instance] MvPolynomial.gradedAlgebra in
/-- Graded finiteness: if a power of every coordinate lies in `I + (ℓ_ρ)` for a homogeneous ideal
`I`, then `ℂ[x_σ]/I` is a finite module over `ℂ[y_ρ]` through `y_i ↦ ℓ_i`.
Source: Bruns–Herzog, *Cohen–Macaulay Rings*, Proposition 1.5.4 (graded Nakayama);
Eisenbud, *Commutative Algebra*, Exercise 4.6. -/
theorem a3r_finite_of_pow_mem (I : Ideal (MvPolynomial σ ℂ))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ ℂ)) (ℓ : Matrix ρ σ ℂ)
    (hpow : ∀ k, ∃ e, X k ^ e ∈ I ⊔ Ideal.span (Set.range fun i => a3r_lin ℓ (X i))) :
    ((Ideal.Quotient.mk I).comp (a3r_lin ℓ).toRingHom).Finite := by
  classical
  choose e he using hpow
  set J := I ⊔ Ideal.span (Set.range fun i => a3r_lin ℓ (X i))
  -- exponents `e' k = e k + 1 ≥ 1`
  have he' : ∀ k, X k ^ (e k + 1) ∈ J := fun k => by
    rw [pow_succ]; exact J.mul_mem_right _ (he k)
  let Box : Finset (σ →₀ ℕ) := (Fintype.piFinset fun k => Finset.range (e k + 1)).map
    Finsupp.equivFunOnFinite.symm.toEmbedding
  have hBox : ∀ α : σ →₀ ℕ, (∀ k, α k < e k + 1) → α ∈ Box := by
    intro α hα
    refine Finset.mem_map.2 ⟨α, Fintype.mem_piFinset.2 fun k => Finset.mem_range.2 (hα k), ?_⟩
    simp
  let _ : Algebra (MvPolynomial ρ ℂ) (MvPolynomial σ ℂ) := (a3r_lin ℓ).toRingHom.toAlgebra
  set R := MvPolynomial ρ ℂ
  set S : Submodule R (MvPolynomial σ ℂ) :=
    Submodule.span R ((fun α => monomial α (1 : ℂ)) '' Box) ⊔ I.restrictScalars R
  have hsmulC : ∀ (c : ℂ) (y : MvPolynomial σ ℂ), y ∈ S → C c * y ∈ S := by
    intro c y hy
    have : (C c : R) • y = C c * y := by
      rw [Algebra.smul_def]
      change a3r_lin ℓ (C c) * y = _
      rw [a3r_lin_C]
    rw [← this]
    exact S.smul_mem _ hy
  have hlin : ∀ (i : ρ) (y : MvPolynomial σ ℂ), y ∈ S → a3r_lin ℓ (X i) * y ∈ S := by
    intro i y hy
    have : (X i : R) • y = a3r_lin ℓ (X i) * y := Algebra.smul_def _ _
    rw [← this]
    exact S.smul_mem _ hy
  have hI_S : ∀ y ∈ I, y ∈ S := fun y hy => Submodule.mem_sup_right hy
  -- every homogeneous polynomial lies in `S`
  have key : ∀ m (F : MvPolynomial σ ℂ), F.IsHomogeneous m → F ∈ S := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
    intro F hF
    rw [F.as_sum]
    refine Submodule.sum_mem _ fun α hα => ?_
    have hαdeg : α.degree = m := by
      have := hF (mem_support_iff.1 hα)
      rw [Finsupp.degree_eq_weight_one]
      exact this
    rw [show monomial α (F.coeff α) = C (F.coeff α) * monomial α 1 by
      rw [C_mul_monomial, mul_one]]
    refine hsmulC _ _ ?_
    by_cases hb : ∀ k, α k < e k + 1
    · exact Submodule.mem_sup_left (Submodule.subset_span ⟨α, hBox α hb, rfl⟩)
    push Not at hb
    obtain ⟨k, hk⟩ := hb
    set E := e k + 1
    -- `x_k^E = h + Σ_i ℓ_i c_i`
    obtain ⟨h, hh, z, hz, hhz⟩ := Submodule.mem_sup.1 (he' k)
    obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 hz
    have hcomp : X k ^ E = homogeneousComponent E h +
        ∑ i, a3r_lin ℓ (X i) * homogeneousComponent (E - 1) (c i) := by
      have h1 : homogeneousComponent E (X k ^ E) = X k ^ E :=
        homogeneousComponent_eq_self (isHomogeneous_X_pow (R := ℂ) k E)
      rw [← h1, ← hhz, map_add, map_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_comm, show E = (E - 1) + 1 by omega,
        a3r_homogeneousComponent_mul _ _ (a3r_lin_X_isHomogeneous ℓ i)]
      rfl
    set β := α - Finsupp.single k E
    have hαβ : α = β + Finsupp.single k E := by
      ext k'
      simp only [β, Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply]
      by_cases h' : k' = k
      · subst h'; simp; omega
      · simp [Ne.symm h']
    have hmon : monomial α (1 : ℂ) = monomial β 1 * X k ^ E := by
      rw [hαβ, monomial_add_single]
    have hβdeg : β.degree + E = m := by
      rw [← hαdeg, hαβ, map_add, Finsupp.degree_single]
    rw [hmon, hcomp, mul_add, Finset.mul_sum]
    refine S.add_mem (hI_S _ (I.mul_mem_left _ (homogeneousComponent_mem_of_mem hI hh E)))
      (Submodule.sum_mem _ fun i _ => ?_)
    rw [mul_left_comm]
    refine hlin i _ (ih (β.degree + (E - 1)) (by omega) _ ?_)
    exact (isHomogeneous_monomial _ rfl).mul (homogeneousComponent_isHomogeneous _ _)
  have hS : S = ⊤ := by
    refine eq_top_iff.2 fun F _ => ?_
    rw [← sum_homogeneousComponent F]
    exact Submodule.sum_mem _ fun m _ => key m _ (homogeneousComponent_isHomogeneous m F)
  -- the quotient is spanned by the images of the monomials in the box
  let q : MvPolynomial σ ℂ →ₗ[R] MvPolynomial σ ℂ ⧸ I := (Ideal.Quotient.mkₐ R I).toLinearMap
  have hfin : Module.Finite R (MvPolynomial σ ℂ ⧸ I) := by
    refine ⟨⟨Box.image fun α => q (monomial α 1), eq_top_iff.2 fun y _ => ?_⟩⟩
    obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hF : F ∈ S := hS ▸ Submodule.mem_top
    have hle : S ≤ (Submodule.span R ↑(Box.image fun α => q (monomial α 1))).comap q := by
      refine sup_le (Submodule.span_le.2 ?_) fun z hz => ?_
      · rintro _ ⟨α, hα, rfl⟩
        exact Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hα))
      · rw [Submodule.mem_comap]
        have : q z = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hz
        rw [this]
        exact zero_mem _
    exact hle hF
  exact hfin

omit [Fintype σ] in
attribute [local instance] MvPolynomial.gradedAlgebra in
/-- A proper homogeneous ideal lies in the irrelevant ideal. -/
theorem a3r_le_irrelevant (Q : Ideal (MvPolynomial σ ℂ))
    (hQ : Q.IsHomogeneous (homogeneousSubmodule σ ℂ)) (hne : Q ≠ ⊤) :
    Q ≤ RingHom.ker (constantCoeff : MvPolynomial σ ℂ →+* ℂ) := by
  intro F hF
  rw [RingHom.mem_ker]
  by_contra h0
  have h1 : homogeneousComponent 0 F ∈ Q := homogeneousComponent_mem_of_mem hQ hF 0
  rw [homogeneousComponent_zero] at h1
  have hu : IsUnit (C (F.coeff 0) : MvPolynomial σ ℂ) :=
    (isUnit_iff_ne_zero.2 (by rwa [← constantCoeff_eq])).map C
  exact hne (Ideal.eq_top_of_isUnit_mem _ h1 hu)

omit [Fintype σ] in
attribute [local instance] MvPolynomial.gradedAlgebra in
/-- A homogeneous prime missing a coordinate has a quotient of dimension at least one: it is not
the irrelevant ideal. -/
theorem a3r_one_le_dim (Q : Ideal (MvPolynomial σ ℂ)) [Q.IsPrime]
    (hQ : Q.IsHomogeneous (homogeneousSubmodule σ ℂ)) (k : σ) (hk : X k ∉ Q) :
    (1 : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial σ ℂ ⧸ Q) := by
  by_contra hlt
  push Not at hlt
  have h0 : ringKrullDim (MvPolynomial σ ℂ ⧸ Q) ≤ (0 : ℕ) := by
    generalize ringKrullDim (MvPolynomial σ ℂ ⧸ Q) = x at hlt
    induction x using WithBot.recBotCoe with
    | bot => exact bot_le
    | coe x =>
      have : x < 1 := by exact_mod_cast hlt
      rw [Order.lt_one_iff] at this
      subst this
      exact le_rfl
  have : Ring.KrullDimLE 0 (MvPolynomial σ ℂ ⧸ Q) := Ring.krullDimLE_iff.2 h0
  have hmax : Q.IsMaximal := Ideal.Quotient.maximal_of_isField _ Ring.KrullDimLE.isField_of_isDomain
  have hker : (RingHom.ker (constantCoeff : MvPolynomial σ ℂ →+* ℂ)).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ fun z => ⟨C z, constantCoeff_C _ z⟩
  have heq := hmax.eq_of_le hker.ne_top (a3r_le_irrelevant Q hQ (Ideal.IsPrime.ne_top inferInstance))
  exact hk (heq ▸ RingHom.mem_ker.2 (constantCoeff_X ℂ k))

omit [Fintype σ] in
attribute [local instance] MvPolynomial.gradedAlgebra in
/-- If every homogeneous prime over a homogeneous ideal `J` contains all coordinates, then a power
of every coordinate lies in `J`. -/
theorem a3r_pow_mem_of_forall (J : Ideal (MvPolynomial σ ℂ))
    (hJ : J.IsHomogeneous (homogeneousSubmodule σ ℂ))
    (h : ∀ Q : Ideal (MvPolynomial σ ℂ), Q.IsPrime → Q.IsHomogeneous (homogeneousSubmodule σ ℂ) →
      J ≤ Q → ∀ k, X k ∈ Q) (k : σ) : ∃ e, X k ^ e ∈ J := by
  have : X k ∈ J.radical := by
    rw [← Ideal.sInf_minimalPrimes]
    refine Submodule.mem_sInf.2 fun Q hQ => ?_
    exact h Q hQ.1.1 (a3m_isHomogeneous_of_mem_minimalPrimes hJ hQ) hQ.1.2 k
  exact this

omit [Fintype ρ] in
/-- The dimension of a subvariety of `V(I)` equals that of its image under a finite projection. -/
theorem a3r_dim_eq_of_finite (I : Ideal (MvPolynomial σ ℂ)) (ℓ : Matrix ρ σ ℂ)
    (hfin : ((Ideal.Quotient.mk I).comp (a3r_lin ℓ).toRingHom).Finite)
    (Q : Ideal (MvPolynomial σ ℂ)) [Q.IsPrime] (hIQ : I ≤ Q) :
    ringKrullDim (MvPolynomial σ ℂ ⧸ Q) =
      ringKrullDim (MvPolynomial ρ ℂ ⧸ Q.comap (a3r_lin ℓ)) := by
  have hle : Q.comap (a3r_lin ℓ) ≤ Q.comap (a3r_lin ℓ).toRingHom := le_rfl
  let f : MvPolynomial ρ ℂ ⧸ Q.comap (a3r_lin ℓ) →+* MvPolynomial σ ℂ ⧸ Q :=
    Ideal.quotientMap Q (a3r_lin ℓ).toRingHom hle
  have hinj : Function.Injective f := Ideal.quotientMap_injective
  -- integrality, through `ℂ[x]/I`
  let g : MvPolynomial σ ℂ ⧸ I →+* MvPolynomial σ ℂ ⧸ Q := Ideal.Quotient.factor hIQ
  have hgsurj : Function.Surjective g := Ideal.Quotient.factor_surjective hIQ
  have hcomp : ((Ideal.Quotient.mk Q).comp (a3r_lin ℓ).toRingHom) =
      g.comp ((Ideal.Quotient.mk I).comp (a3r_lin ℓ).toRingHom) := by
    ext F <;> rfl
  have hfinQ : ((Ideal.Quotient.mk Q).comp (a3r_lin ℓ).toRingHom).Finite := by
    rw [hcomp]
    exact RingHom.Finite.comp (RingHom.Finite.of_surjective g hgsurj) hfin
  have hint : f.IsIntegral := by
    have h1 := hfinQ.to_isIntegral
    have : f.comp (Ideal.Quotient.mk (Q.comap (a3r_lin ℓ))) =
        (Ideal.Quotient.mk Q).comp (a3r_lin ℓ).toRingHom := by
      ext F <;> rfl
    intro x
    rw [← this] at h1
    exact RingHom.IsIntegral.tower_top _ _ h1 x
  let _ : Algebra (MvPolynomial ρ ℂ ⧸ Q.comap (a3r_lin ℓ)) (MvPolynomial σ ℂ ⧸ Q) := f.toAlgebra
  have : Algebra.IsIntegral (MvPolynomial ρ ℂ ⧸ Q.comap (a3r_lin ℓ)) (MvPolynomial σ ℂ ⧸ Q) :=
    ⟨hint⟩
  have : Nontrivial (MvPolynomial ρ ℂ ⧸ Q.comap (a3r_lin ℓ)) :=
    Ideal.Quotient.nontrivial_iff.2 (Ideal.IsPrime.ne_top inferInstance)
  exact PolynomialCatenary.ringKrullDim_eq_of_isIntegral_of_injective hinj

end Finite

/-! ## Generic projections are finite -/

section GenericFinite

variable {σ : Type} [Fintype σ] {n : ℕ}

attribute [local instance] MvPolynomial.gradedAlgebra in
/-- For a homogeneous prime `I` with affine cone of dimension `n + 1`, a generic linear projection
from a centre of codimension `n + 1` is finite on `V(I)`: the centre misses `V(I)`. -/
theorem a3r_generic_finite (I : Ideal (MvPolynomial σ ℂ)) [I.IsPrime]
    (hI : I.IsHomogeneous (homogeneousSubmodule σ ℂ))
    (hdim : ringKrullDim (MvPolynomial σ ℂ ⧸ I) = (n + 1 : ℕ)) :
    a3r_Generic {a : Fin (n + 1) × σ → ℂ |
      ((Ideal.Quotient.mk I).comp (a3r_lin (a3r_mat a)).toRingHom).Finite} := by
  classical
  set D := MvPolynomial σ ℂ ⧸ I
  have : Algebra.FiniteType ℂ D :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ _) (Ideal.Quotient.mkₐ_surjective ℂ _)
  refine (a3r_generic_iInter_fintype _ fun j => a3r_generic_linear (ρ := Fin (n + 1)) D
    (fun k => Ideal.Quotient.mk I (X k)) 0 j).mono fun a ha => ?_
  refine a3r_finite_of_pow_mem I hI _ (a3r_pow_mem_of_forall _ (hI.sup (Ideal.homogeneous_span _ _
    fun x hx => ?_)) fun Q hQ hQh hJQ k => ?_)
  · obtain ⟨i, rfl⟩ := hx
    exact ⟨1, a3r_lin_X_isHomogeneous _ i⟩
  · by_contra hk
    set Q' := Q.map (Ideal.Quotient.mk I)
    have hIQ : I ≤ Q := le_sup_left.trans hJQ
    have hker : RingHom.ker (Ideal.Quotient.mk I) ≤ Q := by rwa [Ideal.mk_ker]
    have hQ' : Q'.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
    have hmem : ∀ F, Ideal.Quotient.mk I F ∈ Q' ↔ F ∈ Q := by
      intro F
      rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective,
        sup_eq_left.2 hker]
    have hb := ha k Q' hQ' (fun h => hk ((hmem _).1 h)) fun i => by
      rw [Pi.zero_apply, sub_zero]
      have : ∑ k', algebraMap ℂ D (a (i, k')) * Ideal.Quotient.mk I (X k') =
          Ideal.Quotient.mk I (a3r_lin (a3r_mat a) (X i)) := by
        rw [a3r_lin_X, map_sum]
        refine Finset.sum_congr rfl fun k' _ => ?_
        rw [map_mul, ← MvPolynomial.algebraMap_eq, Ideal.Quotient.mk_algebraMap]
        rfl
      rw [this, hmem]
      exact hJQ (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩))
    rw [ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hIQ), hdim] at hb
    have h1 := a3r_one_le_dim Q hQh k hk
    have : ringKrullDim (MvPolynomial σ ℂ ⧸ Q) ≤ 0 := by
      refine a3r_withBot_le_of_add_le_add (n + 1) ?_
      rw [zero_add]
      simpa using hb
    exact absurd (h1.trans this) (by decide)

end GenericFinite

end HodgeLean.Adapters
