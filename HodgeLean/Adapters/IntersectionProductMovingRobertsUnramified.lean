import HodgeLean.Adapters.IntersectionProductMovingRobertsTranslate

/-! # Generic projections are unramified at a smooth point

At a point `𝔶` of `V(I)` where the Kähler differentials `κ(𝔶) ⊗ Ω_{(ℂ[x]/I)/ℂ}` have rank at most
`n + 1` (a smooth point of the affine cone over an `n`-dimensional projective variety), a generic
linear projection `ℂ[y_0, …, y_n] → ℂ[x]/I` is unramified (`a3r_generic_isUnramifiedAt`): the
differentials `dℓ_i = Σ_k ℓ_{ik} dx_k` of generic linear forms span the fibre of `Ω`
(`a3r_generic_span`, a determinant with coefficients in `κ(𝔶)` that does not vanish at generic
complex points), so `κ(𝔶) ⊗ Ω_{(ℂ[x]/I)/ℂ[y]} = 0`, and by Nakayama `𝔶` is outside the support
of the relative differentials.

Source: Hartshorne, *Algebraic Geometry*, II, Proposition 8.7 and III, Exercise 10.3;
J. Roberts, *Chow's moving lemma* (1972), §1; Mathlib, `Algebra.unramifiedLocus_eq_compl_support`.
HC no distance; AV milestone no distance.
-/

noncomputable section

open MvPolynomial TensorProduct

namespace HodgeLean.Adapters

section Unramified

variable {ρ σ : Type} [Fintype ρ] [Fintype σ]

omit [Fintype σ] in
/-- The differentials of the coordinates span the Kähler differentials of `ℂ[x]/I`. -/
theorem a3r_span_D_X (I : Ideal (MvPolynomial σ ℂ)) :
    Submodule.span (MvPolynomial σ ℂ ⧸ I)
      (Set.range fun k => KaehlerDifferential.D ℂ (MvPolynomial σ ℂ ⧸ I) (Ideal.Quotient.mk I (X k)))
      = ⊤ := by
  set A := MvPolynomial σ ℂ ⧸ I
  set S := Submodule.span A
    (Set.range fun k => KaehlerDifferential.D ℂ A (Ideal.Quotient.mk I (X k)))
  rw [eq_top_iff, ← KaehlerDifferential.span_range_derivation ℂ A, Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective a
  induction F using MvPolynomial.induction_on with
  | C c =>
    rw [← MvPolynomial.algebraMap_eq, Ideal.Quotient.mk_algebraMap, Derivation.map_algebraMap]
    exact zero_mem _
  | add F G hF hG => rw [map_add, map_add]; exact add_mem hF hG
  | mul_X F k hF =>
    rw [map_mul, Derivation.leibniz]
    exact add_mem (S.smul_mem _ (Submodule.subset_span ⟨k, rfl⟩)) (S.smul_mem _ hF)

/-- Generic combinations of a spanning family span: if `v_k` span a vector space of dimension at
most `card ρ` over a field extension `K` of `ℂ`, then for generic complex `a` the vectors
`w_i = Σ_k a_{ik} v_k` span it. -/
theorem a3r_generic_span [DecidableEq σ] {K V : Type} [Field K] [Algebra ℂ K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (v : σ → V)
    (hv : Submodule.span K (Set.range v) = ⊤) (hrank : Module.finrank K V ≤ Fintype.card ρ) :
    a3r_Generic {a : ρ × σ → ℂ |
      Submodule.span K (Set.range fun i => ∑ k, algebraMap ℂ K (a (i, k)) • v k) = ⊤} := by
  classical
  -- a spanning subfamily of size at most `card ρ`
  obtain ⟨b, hb, hbspan, hbli⟩ := exists_linearIndependent K (Set.range v)
  have : Finite b := hbli.finite
  have : Fintype b := Fintype.ofFinite b
  have hbcard : Fintype.card b ≤ Fintype.card ρ := hbli.fintype_card_le_finrank.trans hrank
  have hpre : ∀ x : b, ∃ k, v k = x := fun x => hb x.2
  choose g hg using hpre
  set s : Finset σ := Finset.univ.image g
  have hscard : Fintype.card s ≤ Fintype.card ρ := by
    rw [Fintype.card_coe]
    exact (Finset.card_image_le).trans (by rw [Finset.card_univ]; exact hbcard)
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hscard
  have hsspan : Submodule.span K (Set.range fun m : s => v m) = ⊤ := by
    rw [eq_top_iff, ← hv, ← hbspan, Submodule.span_le]
    intro x hx
    refine Submodule.subset_span ⟨⟨g ⟨x, hx⟩, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩, ?_⟩
    exact hg ⟨x, hx⟩
  -- coordinates of every `v_k` in the subfamily, trivial on the subfamily
  have hcoord : ∀ k, ∃ c : s → K, ∑ m, c m • v m = v k := fun k =>
    (Submodule.mem_span_range_iff_exists_fun K).1 (hsspan ▸ Submodule.mem_top)
  choose c₀ hc₀ using hcoord
  let c : σ → s → K := fun k => if h : k ∈ s then Pi.single ⟨k, h⟩ 1 else c₀ k
  have hc : ∀ k, ∑ m, c k m • v m = v k := by
    intro k
    by_cases h : k ∈ s
    · simp only [c, h, dite_true]
      rw [Finset.sum_eq_single ⟨k, h⟩ (fun m _ hm => by simp [hm])
        (fun h' => absurd (Finset.mem_univ _) h')]
      simp
    · simp only [c, h, dite_false]
      exact hc₀ k
  -- the determinant polynomial
  let G : MvPolynomial (ρ × σ) K :=
    (Matrix.of fun (m' m : s) => ∑ k, X (e m', k) * MvPolynomial.C (c k m)).det
  have hevalG : ∀ p : ρ × σ → K, eval p G =
      (Matrix.of fun (m' m : s) => ∑ k, p (e m', k) * c k m).det := by
    intro p
    rw [RingHom.map_det]
    congr 1
    ext m' m
    simp [RingHom.mapMatrix_apply]
  have hG : G ≠ 0 := by
    intro h0
    let p : ρ × σ → K := fun ik => if h : ik.2 ∈ s then (if e ⟨ik.2, h⟩ = ik.1 then 1 else 0) else 0
    have h1 := hevalG p
    rw [h0, map_zero] at h1
    have hone : (Matrix.of fun (m' m : s) => ∑ k, p (e m', k) * c k m) = 1 := by
      ext m' m
      rw [Matrix.of_apply, Finset.sum_eq_single (m' : σ)]
      · simp only [p, m'.2, dite_true, Subtype.coe_eta, ite_true, one_mul, c, Matrix.one_apply,
          Pi.single_apply]
        split_ifs <;> simp_all
      · intro k _ hk
        simp only [p]
        split_ifs with h1 h2
        · exact absurd (congrArg Subtype.val (e.injective h2)) hk
        · simp
        · simp
      · exact fun h => absurd (Finset.mem_univ _) h
    rw [hone, Matrix.det_one] at h1
    exact one_ne_zero h1.symm
  refine (a3r_generic_of_ne_zero G hG).mono fun a ha => ?_
  have ha : eval (fun i => algebraMap ℂ K (a i)) G ≠ 0 := ha
  rw [hevalG] at ha
  set Q := Matrix.of fun (m' m : s) => ∑ k, algebraMap ℂ K (a (e m', k)) * c k m
  have hQ : IsUnit Q := (Matrix.isUnit_iff_isUnit_det Q).2 (isUnit_iff_ne_zero.2 ha)
  -- `w_{e m'} = Σ_m Q_{m' m} v_m`
  set w : ρ → V := fun i => ∑ k, algebraMap ℂ K (a (i, k)) • v k
  have hw : ∀ m', w (e m') = ∑ m, Q m' m • v m := by
    intro m'
    simp only [w, Q, Matrix.of_apply, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← hc k, Finset.smul_sum]
    exact Finset.sum_congr rfl fun m _ => by rw [smul_smul]
  have hvs : ∀ m : s, v m ∈ Submodule.span K (Set.range w) := by
    intro m
    obtain ⟨x, hx⟩ := (Matrix.vecMul_surjective_iff_isUnit.2 hQ) (Pi.single m (1 : K))
    have : v m = ∑ m', x m' • w (e m') := by
      simp only [hw, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      have : ∀ m'' : s, ∑ m', x m' * Q m' m'' = (Pi.single m (1 : K) : s → K) m'' := by
        intro m''
        rw [← hx]
        rfl
      simp only [← Finset.sum_smul, this]
      rw [Finset.sum_eq_single m (fun m'' _ hm'' => by simp [hm''])
        (fun h => absurd (Finset.mem_univ _) h)]
      simp
    rw [this]
    exact Submodule.sum_mem _ fun m' _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  change Submodule.span K (Set.range w) = ⊤
  rw [eq_top_iff, ← hsspan, Submodule.span_le]
  rintro _ ⟨m, rfl⟩
  exact hvs m

/-- Generic projections are unramified at a point where the Kähler differentials have rank at most
`card ρ`: for generic `ℓ`, `ℂ[y_ρ] → ℂ[x]/I` is unramified at the prime `𝔶`.
Source: Hartshorne, *Algebraic Geometry*, II, Proposition 8.7 and III, Exercise 10.3 (a general
projection of a smooth variety is unramified at a given point); J. Roberts, *Chow's moving lemma*
(1972), §1. -/
theorem a3r_generic_isUnramifiedAt [DecidableEq σ] (I : Ideal (MvPolynomial σ ℂ))
    (𝔶 : Ideal (MvPolynomial σ ℂ ⧸ I)) [𝔶.IsPrime]
    (hrank : Module.finrank 𝔶.ResidueField
      (𝔶.ResidueField ⊗[MvPolynomial σ ℂ ⧸ I] Ω[MvPolynomial σ ℂ ⧸ I⁄ℂ]) ≤ Fintype.card ρ) :
    a3r_Generic {a : ρ × σ → ℂ |
      letI : Algebra (MvPolynomial ρ ℂ) (MvPolynomial σ ℂ ⧸ I) :=
        ((Ideal.Quotient.mk I).comp (a3r_lin (a3r_mat a)).toRingHom).toAlgebra
      Algebra.IsUnramifiedAt (MvPolynomial ρ ℂ) 𝔶} := by
  classical
  set A := MvPolynomial σ ℂ ⧸ I
  set K := 𝔶.ResidueField
  have : Algebra.FiniteType ℂ A :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ _) (Ideal.Quotient.mkₐ_surjective ℂ _)
  set v : σ → K ⊗[A] Ω[A⁄ℂ] := fun k =>
    (1 : K) ⊗ₜ KaehlerDifferential.D ℂ A (Ideal.Quotient.mk I (X k))
  have h1 : ∀ ω : Ω[A⁄ℂ], (1 : K) ⊗ₜ[A] ω ∈ Submodule.span K (Set.range v) := by
    intro ω
    have hω : ω ∈ Submodule.span A (Set.range fun k =>
        KaehlerDifferential.D ℂ A (Ideal.Quotient.mk I (X k))) := by
      rw [a3r_span_D_X]; exact Submodule.mem_top
    induction hω using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨k, rfl⟩ := hy
      exact Submodule.subset_span ⟨k, rfl⟩
    | zero => rw [tmul_zero]; exact zero_mem _
    | add y y' _ _ hy hy' => rw [tmul_add]; exact add_mem hy hy'
    | smul r y _ hy =>
      rw [← TensorProduct.smul_tmul, ← algebraMap_smul K r, smul_eq_mul, mul_one,
        show (algebraMap A K r) ⊗ₜ[A] y = (algebraMap A K r) • ((1 : K) ⊗ₜ[A] y) by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]]
      exact Submodule.smul_mem _ _ hy
  have hv : Submodule.span K (Set.range v) = ⊤ := by
    refine eq_top_iff.2 fun z _ => ?_
    clear ‹z ∈ ⊤›
    induction z using TensorProduct.inductionOn with
    | tmul x ω =>
      have : x ⊗ₜ[A] ω = x • ((1 : K) ⊗ₜ[A] ω) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [this]
      exact Submodule.smul_mem _ _ (h1 ω)
    | add y y' hy hy' => exact add_mem hy hy'
  have : Module.Finite A Ω[A⁄ℂ] := inferInstance
  have : FiniteDimensional K (K ⊗[A] Ω[A⁄ℂ]) := inferInstance
  refine (a3r_generic_span (ρ := ρ) v hv hrank).mono fun a ha => ?_
  let _ : Algebra (MvPolynomial ρ ℂ) A :=
    ((Ideal.Quotient.mk I).comp (a3r_lin (a3r_mat a)).toRingHom).toAlgebra
  have : IsScalarTower ℂ (MvPolynomial ρ ℂ) A := IsScalarTower.of_algebraMap_eq fun c => by
    change _ = Ideal.Quotient.mk I (a3r_lin (a3r_mat a) (algebraMap ℂ (MvPolynomial ρ ℂ) c))
    rw [MvPolynomial.algebraMap_eq, a3r_lin_C, ← MvPolynomial.algebraMap_eq,
      Ideal.Quotient.mk_algebraMap]
  set R := MvPolynomial ρ ℂ
  have : Algebra.FiniteType R A := Algebra.FiniteType.of_restrictScalars_finiteType ℂ R A
  set L : K ⊗[A] Ω[A⁄ℂ] →ₗ[K] K ⊗[A] Ω[A⁄R] :=
    (KaehlerDifferential.map ℂ R A A).baseChange K
  have hLsurj : Function.Surjective L := by
    rw [show (L : K ⊗[A] Ω[A⁄ℂ] → K ⊗[A] Ω[A⁄R]) = _ from
      LinearMap.baseChange_eq_lTensor (KaehlerDifferential.map ℂ R A A)]
    exact LinearMap.lTensor_surjective _ (KaehlerDifferential.map_surjective ℂ R A)
  have hLv : ∀ k, L (v k) = (1 : K) ⊗ₜ KaehlerDifferential.D R A (Ideal.Quotient.mk I (X k)) := by
    intro k
    simp only [L, v, LinearMap.baseChange_tmul, KaehlerDifferential.map_D]
    rfl
  have hsm : ∀ (c : ℂ) (ω : Ω[A⁄R]), algebraMap ℂ K c • ((1 : K) ⊗ₜ[A] ω) =
      (1 : K) ⊗ₜ[A] (algebraMap ℂ A c • ω) := by
    intro c ω
    rw [IsScalarTower.algebraMap_apply ℂ A K, algebraMap_smul, TensorProduct.tmul_smul]
  have hLw : ∀ i, L (∑ k, algebraMap ℂ K (a (i, k)) • v k) = 0 := by
    intro i
    rw [map_sum]
    simp only [map_smul, hLv, hsm]
    rw [← TensorProduct.tmul_sum]
    have : ∑ k, algebraMap ℂ A (a (i, k)) • KaehlerDifferential.D R A (Ideal.Quotient.mk I (X k)) =
        KaehlerDifferential.D R A (algebraMap R A (X i)) := by
      change _ = KaehlerDifferential.D R A (Ideal.Quotient.mk I (a3r_lin (a3r_mat a) (X i)))
      rw [a3r_lin_X, map_sum, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hc : Ideal.Quotient.mk I (C (a3r_mat a i k) * X k) =
          (C (a (i, k)) : R) • Ideal.Quotient.mk I (X k) := by
        rw [Algebra.smul_def, map_mul]
        congr 1
        change _ = Ideal.Quotient.mk I (a3r_lin (a3r_mat a) (C (a (i, k))))
        rw [a3r_lin_C]
        rfl
      rw [hc, Derivation.map_smul, ← algebraMap_smul A (C (a (i, k)) : R)]
      congr 1
      rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
    rw [this, Derivation.map_algebraMap, tmul_zero]
  have hzero : ∀ z, L z = 0 := by
    intro z
    have hz : z ∈ Submodule.span K (Set.range fun i => ∑ k, algebraMap ℂ K (a (i, k)) • v k) :=
      ha ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact hLw i
    | zero => exact map_zero L
    | add y y' _ _ hy hy' => rw [map_add, hy, hy', add_zero]
    | smul r y _ hy => rw [map_smul, hy, smul_zero]
  have hsub : Subsingleton (K ⊗[A] Ω[A⁄R]) := ⟨fun x y => by
    obtain ⟨x', rfl⟩ := hLsurj x
    obtain ⟨y', rfl⟩ := hLsurj y
    rw [hzero, hzero]⟩
  have hnot : (⟨𝔶, inferInstance⟩ : PrimeSpectrum A) ∉ Module.support A Ω[A⁄R] := by
    rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct]
    exact not_nontrivial_iff_subsingleton.2 hsub
  have hloc : (⟨𝔶, inferInstance⟩ : PrimeSpectrum A) ∈ Algebra.unramifiedLocus R A := by
    rw [Algebra.unramifiedLocus_eq_compl_support]
    exact hnot
  exact hloc

end Unramified

end HodgeLean.Adapters
