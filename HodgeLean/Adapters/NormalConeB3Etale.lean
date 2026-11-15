import HodgeLean.Adapters.NormalConeB3Defs

/-! # Diagonal cone coefficient: étale coordinates and the diagonal

For `A` étale over `k[x₁, …, xₙ]`, the differences `xᵢ ⊗ 1 - 1 ⊗ xᵢ` form a weakly regular sequence
in `A ⊗ₖ A` (they come from the regular sequence `Xᵢ - xᵢ` of `A[X₁, …, Xₙ]` by flat base change),
and after inverting an element `t` with `μ t = 1` they generate the kernel of the multiplication.
-/

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory Limits AlgebraicGeometry TensorProduct RingTheory.Sequence Pointwise
universe u

/-- A sequence `r :: rs` is weakly regular when `r` is a nonzerodivisor and `rs` is weakly regular
in a quotient ring by `r` presented by a surjection with kernel `(r)`.
Source: Mathlib, `RingTheory.Sequence.isWeaklyRegular_cons_iff`. -/
theorem a3b3_isWeaklyRegular_cons_of_surjective {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : Function.Surjective φ) (r : R) (hker : RingHom.ker φ = Ideal.span {r})
    (hr : IsSMulRegular R r) (rs : List R) (h : IsWeaklyRegular S (rs.map φ)) :
    IsWeaklyRegular R (r :: rs) := by
  rw [isWeaklyRegular_cons_iff]
  refine ⟨hr, ?_⟩
  have h1 : (r • ⊤ : Submodule R R) = RingHom.ker φ := by
    rw [hker, ← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top]
  let e : QuotSMulTop r R ≃+ S :=
    (Submodule.quotEquivOfEq _ _ h1).toAddEquiv.trans
      (RingHom.quotientKerEquivOfSurjective hφ).toAddEquiv
  refine (e.isWeaklyRegular_congr (bs := rs.map φ) ?_).2 h
  refine List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr fun a _ x => ?_)
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
  rw [← map_smul]
  change φ (a * x) = φ a * φ x
  exact map_mul φ a x

/-- The differences `Xᵢ - aᵢ` form a weakly regular sequence in a polynomial ring.
Source: Matsumura, *Commutative Ring Theory*, §16; Mathlib, `MvPolynomial.finSuccEquiv` and
`Polynomial.ker_evalRingHom`. -/
theorem a3b3_mvPolynomial_isWeaklyRegular (A : Type*) [CommRing A] : ∀ (n : ℕ) (a : Fin n → A),
    IsWeaklyRegular (MvPolynomial (Fin n) A)
      (List.ofFn fun i => MvPolynomial.X i - MvPolynomial.C (a i))
  | 0, a => by
    rw [List.ofFn_zero]
    exact IsWeaklyRegular.nil _ _
  | n + 1, a => by
    rw [List.ofFn_succ]
    set e := MvPolynomial.finSuccEquiv A n
    let φ : MvPolynomial (Fin (n + 1)) A →+* MvPolynomial (Fin n) A :=
      (Polynomial.evalRingHom (MvPolynomial.C (a 0))).comp e.toRingEquiv.toRingHom
    have hC : ∀ c : A, e (MvPolynomial.C c) = Polynomial.C (MvPolynomial.C c) := fun c => by
      rw [← MvPolynomial.algebraMap_eq, AlgEquiv.commutes, Polynomial.algebraMap_apply,
        MvPolynomial.algebraMap_eq]
    have he0 : e (MvPolynomial.X 0 - MvPolynomial.C (a 0)) =
        Polynomial.X - Polynomial.C (MvPolynomial.C (a 0)) := by
      rw [map_sub, MvPolynomial.finSuccEquiv_X_zero, ← MvPolynomial.algebraMap_eq,
        AlgEquiv.commutes, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]
    refine a3b3_isWeaklyRegular_cons_of_surjective φ ?_ _ ?_ ?_ _ ?_
    · intro q
      refine ⟨e.symm (Polynomial.C q), ?_⟩
      change Polynomial.eval _ (e (e.symm _)) = q
      rw [AlgEquiv.apply_symm_apply, Polynomial.eval_C]
    · have hk : RingHom.ker φ = (RingHom.ker (Polynomial.evalRingHom
          (MvPolynomial.C (a 0)))).comap e.toRingEquiv.toRingHom := rfl
      rw [hk, Polynomial.ker_evalRingHom, ← he0]
      ext x
      simp only [Ideal.mem_comap, Ideal.mem_span_singleton']
      constructor
      · rintro ⟨c, hc⟩
        refine ⟨e.symm c, e.injective ?_⟩
        rw [map_mul, AlgEquiv.apply_symm_apply]
        exact hc
      · rintro ⟨c, rfl⟩
        exact ⟨e c, (map_mul e c _).symm⟩
    · intro x y hxy
      apply e.injective
      apply (Polynomial.monic_X_sub_C (MvPolynomial.C (a 0))).isRegular.left
      simpa only [smul_eq_mul, map_mul, he0] using congrArg e hxy
    · have : (List.ofFn fun i : Fin n =>
          MvPolynomial.X i.succ - MvPolynomial.C (a i.succ)).map φ =
          List.ofFn fun i : Fin n => MvPolynomial.X i - MvPolynomial.C (a i.succ) := by
        rw [List.map_ofFn]
        congr 1
        funext i
        have hX : e (MvPolynomial.X i.succ) = Polynomial.C (MvPolynomial.X i) :=
          MvPolynomial.finSuccEquiv_X_succ
        simp [φ, hC, hX]
      rw [this]
      exact a3b3_mvPolynomial_isWeaklyRegular A n (fun i => a i.succ)

/-- For `A` flat over `P = k[x₁, …, xₙ]`, the differences `xᵢ ⊗ 1 - 1 ⊗ xᵢ` form a weakly regular
sequence in `A ⊗ₖ A`.
Source: Mathlib, `RingTheory.Sequence.IsWeaklyRegular.of_flat` and
`Algebra.IsPushout.tensorProduct_tensorProduct`. -/
theorem a3b3_tensor_isWeaklyRegular {k A : Type*} [CommRing k] [CommRing A] [Algebra k A] (n : ℕ)
    [Algebra (MvPolynomial (Fin n) k) A] [IsScalarTower k (MvPolynomial (Fin n) k) A]
    [Module.Flat (MvPolynomial (Fin n) k) A] :
    IsWeaklyRegular (A ⊗[k] A) (List.ofFn fun i =>
      algebraMap (MvPolynomial (Fin n) k) A (MvPolynomial.X i) ⊗ₜ[k] (1 : A) -
        (1 : A) ⊗ₜ[k] algebraMap (MvPolynomial (Fin n) k) A (MvPolynomial.X i)) := by
  set P := MvPolynomial (Fin n) k
  let x : Fin n → A := fun i => algebraMap P A (MvPolynomial.X i)
  -- the sequence in `P ⊗ₖ A ≅ A[X]`
  let e : P ⊗[k] A ≃+* MvPolynomial (Fin n) A :=
    (Algebra.TensorProduct.comm k P A).toRingEquiv.trans
      (MvPolynomial.algebraTensorAlgEquiv (σ := Fin n) k A).toRingEquiv
  have he : ∀ i, e (MvPolynomial.X i ⊗ₜ[k] (1 : A) - (1 : P) ⊗ₜ[k] x i) =
      MvPolynomial.X i - MvPolynomial.C (x i) := by
    intro i
    simp only [e, map_sub, RingEquiv.trans_apply, AlgEquiv.coe_toRingEquiv,
      Algebra.TensorProduct.comm_tmul]
    erw [MvPolynomial.algebraTensorAlgEquiv_tmul, MvPolynomial.algebraTensorAlgEquiv_tmul]
    simp [MvPolynomial.smul_eq_C_mul]
  have h0 : IsWeaklyRegular (P ⊗[k] A) (List.ofFn fun i =>
      MvPolynomial.X i ⊗ₜ[k] (1 : A) - (1 : P) ⊗ₜ[k] x i) := by
    have := a3b3_mvPolynomial_isWeaklyRegular A n x
    have hl : (List.ofFn fun i => MvPolynomial.X i ⊗ₜ[k] (1 : A) - (1 : P) ⊗ₜ[k] x i).map e =
        List.ofFn fun i => MvPolynomial.X i - MvPolynomial.C (x i) := by
      rw [List.map_ofFn]; congr 1; funext i; exact he i
    rw [← hl] at this
    exact (e.toAddEquiv.isWeaklyRegular_congr (List.forall₂_map_right_iff.mpr
      (List.forall₂_same.mpr fun r _ y => map_mul e r y))).2 this
  -- flat base change to `A ⊗ₖ A`
  let : Algebra (P ⊗[k] A) (A ⊗[k] A) :=
    (Algebra.TensorProduct.map (IsScalarTower.toAlgHom k P A) (AlgHom.id k A)).toRingHom.toAlgebra
  have : IsScalarTower P (P ⊗[k] A) (A ⊗[k] A) := by
    refine IsScalarTower.of_algebraMap_eq fun a => ?_
    simp [RingHom.algebraMap_toAlgebra, Algebra.TensorProduct.algebraMap_apply]
  have hpush : Algebra.IsPushout P A (P ⊗[k] A) (A ⊗[k] A) :=
    Algebra.IsPushout.tensorProduct_tensorProduct k A P A (by
      ext a; simp [RingHom.algebraMap_toAlgebra])
  have : Module.Flat (P ⊗[k] A) (A ⊗[k] A) :=
    Module.Flat.isBaseChange (R := P) (M := A) (S := P ⊗[k] A) _ hpush.symm.out
  have := h0.of_flat (S := A ⊗[k] A)
  convert this using 1
  rw [List.map_ofFn]
  congr 1
  funext i
  simp [RingHom.algebraMap_toAlgebra, x]
  rfl

section Diagonal
variable {k P S : Type*} [CommRing k] [CommRing P] [CommRing S] [Algebra k P] [Algebra k S]
  [Algebra P S] [IsScalarTower k P S]

/-- The ideal of `S ⊗_k S` generated by `a ⊗ 1 - 1 ⊗ a` for `a` in the image of `P`; the universe
polymorphic form of `a3m_diagIdeal`.
Source: Iversen, *Generic local structure of the morphisms in commutative algebra*, I.2.3. -/
def a3b3_diagIdeal (k P S : Type*) [CommRing k] [CommRing P] [CommRing S] [Algebra k P]
    [Algebra k S]
    [Algebra P S] (s : Set P) : Ideal (S ⊗[k] S) :=
  Ideal.span ((fun p : P => algebraMap P S p ⊗ₜ[k] (1 : S) - (1 : S) ⊗ₜ[k] algebraMap P S p) '' s)

/-- If `s` generates `P` as a `k`-algebra, then `a ⊗ 1 - 1 ⊗ a` lies in the ideal for every `a`
in the image of `P`.
Source: Mathlib, `Algebra.adjoin_induction`. -/
theorem a3b3_mem_diagIdeal_of_adjoin {s : Set P} (hs : Algebra.adjoin k s = ⊤) (p : P) :
    algebraMap P S p ⊗ₜ[k] (1 : S) - (1 : S) ⊗ₜ[k] algebraMap P S p ∈
      a3b3_diagIdeal k P S s := by
  have hp : p ∈ Algebra.adjoin k s := hs ▸ Algebra.mem_top
  induction hp using Algebra.adjoin_induction with
  | mem x hx => exact Ideal.subset_span ⟨x, hx, rfl⟩
  | algebraMap r =>
    rw [← IsScalarTower.algebraMap_apply, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul,
      sub_self]
    exact zero_mem _
  | add x y _ _ hx hy =>
    rw [map_add, add_tmul, tmul_add]
    convert add_mem hx hy using 1
    abel
  | mul x y _ _ hx hy =>
    rw [map_mul]
    have : (algebraMap P S x * algebraMap P S y) ⊗ₜ[k] (1 : S) -
        (1 : S) ⊗ₜ[k] (algebraMap P S x * algebraMap P S y) =
        (algebraMap P S x ⊗ₜ[k] (1 : S)) *
            (algebraMap P S y ⊗ₜ[k] (1 : S) - (1 : S) ⊗ₜ[k] algebraMap P S y) +
          ((1 : S) ⊗ₜ[k] algebraMap P S y) *
            (algebraMap P S x ⊗ₜ[k] (1 : S) - (1 : S) ⊗ₜ[k] algebraMap P S x) := by
      simp only [mul_sub, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [mul_comm (algebraMap P S y)]
      abel
    rw [this]
    exact add_mem (Ideal.mul_mem_left _ _ hy) (Ideal.mul_mem_left _ _ hx)

/-- The diagonal element: if `S` is unramified over `P` and `s` generates `P` over `k`, some
`t ∈ S ⊗_k S` maps to `1` under multiplication and multiplies the kernel of multiplication into the
ideal generated by the `a ⊗ 1 - 1 ⊗ a`, `a ∈ s`.
Source: Iversen, *Generic local structure of the morphisms in commutative algebra*, I.2.3;
Mathlib, `Algebra.FormallyUnramified.iff_exists_tensorProduct`. -/
theorem a3b3_exists_diag_elem {s : Set P} (hs : Algebra.adjoin k s = ⊤)
    [Algebra.FormallyUnramified P S] [Algebra.EssFiniteType P S] :
    ∃ t : S ⊗[k] S, Algebra.TensorProduct.lmul' k t = 1 ∧
      ∀ a ∈ KaehlerDifferential.ideal k S, a * t ∈ a3b3_diagIdeal k P S s := by
  set J := a3b3_diagIdeal k P S s
  let q : S ⊗[k] S →+* (S ⊗[k] S) ⧸ J := Ideal.Quotient.mk J
  have hdiag : ∀ p : P, q (algebraMap P S p ⊗ₜ[k] (1 : S)) = q ((1 : S) ⊗ₜ[k] algebraMap P S p) :=
    fun p => Ideal.Quotient.eq.2 (a3b3_mem_diagIdeal_of_adjoin hs p)
  let f : S →ₐ[P] (S ⊗[k] S) ⧸ J :=
    { q.comp Algebra.TensorProduct.includeLeftRingHom with commutes' := fun _ => rfl }
  let g : S →ₐ[P] (S ⊗[k] S) ⧸ J :=
    { q.comp (Algebra.TensorProduct.includeRight : S →ₐ[k] S ⊗[k] S).toRingHom with
      commutes' := fun p => (hdiag p).symm }
  let ψ : S ⊗[P] S →ₐ[P] (S ⊗[k] S) ⧸ J :=
    Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)
  have hψ : ∀ a b : S, ψ (a ⊗ₜ[P] b) = q (a ⊗ₜ[k] b) := by
    intro a b
    simp only [ψ]
    change q (a ⊗ₜ[k] 1) * q (1 ⊗ₜ[k] b) = _
    rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have hJker : J ≤ RingHom.ker (Algebra.TensorProduct.lmul' k : S ⊗[k] S →ₐ[k] S) := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨p, -, rfl⟩
    simp [RingHom.mem_ker, Algebra.TensorProduct.lmul'_apply_tmul]
  let χ : (S ⊗[k] S) ⧸ J →+* S := Ideal.Quotient.lift J
    (Algebra.TensorProduct.lmul' k : S ⊗[k] S →ₐ[k] S).toRingHom hJker
  have hχψ : ∀ x : S ⊗[P] S, χ (ψ x) = Algebra.TensorProduct.lmul' P x := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul a b =>
      rw [hψ]
      simp [χ, q, Algebra.TensorProduct.lmul'_apply_tmul]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]
  obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (ψ (Algebra.FormallyUnramified.elem P S))
  refine ⟨t, ?_, ?_⟩
  · have h1 := hχψ (Algebra.FormallyUnramified.elem P S)
    rw [Algebra.FormallyUnramified.lmul_elem, ← ht] at h1
    simpa [χ] using h1
  · intro a ha
    rw [← KaehlerDifferential.span_range_eq_ideal] at ha
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change q (a * t) = 0
    induction ha using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, rfl⟩ := hx
      rw [map_mul]
      change q _ * Ideal.Quotient.mk J t = 0
      rw [ht]
      have : q ((1 : S) ⊗ₜ[k] b - b ⊗ₜ[k] (1 : S)) = ψ ((1 : S) ⊗ₜ[P] b - b ⊗ₜ[P] (1 : S)) := by
        rw [map_sub, map_sub, hψ, hψ]
      rw [this, ← map_mul, Algebra.FormallyUnramified.one_tmul_sub_tmul_one_mul_elem, map_zero]
    | zero => simp
    | add x y _ _ hx hy => rw [add_mul, map_add, hx, hy, add_zero]
    | smul r x _ hx => rw [smul_eq_mul, mul_assoc, map_mul, hx, mul_zero]

end Diagonal

/-- Étale coordinates make the diagonal a regular embedding: for `A` étale over `k[x₁, …, xₙ]` there
is `t ∈ A ⊗ₖ A` with `μ t = 1` such that, in every localization away from `t`, the kernel of the
multiplication is generated by the weakly regular sequence of the `xᵢ ⊗ 1 - 1 ⊗ xᵢ`.
Source: Stacks Project, Lemma 31.21.3 (tag 063L); Iversen, *Generic local structure of the
morphisms in commutative algebra*, I.2.3. -/
theorem a3b3_etale_diagonal {k A : Type*} [CommRing k] [CommRing A] [Algebra k A] (n : ℕ)
    [Algebra (MvPolynomial (Fin n) k) A] [IsScalarTower k (MvPolynomial (Fin n) k) A]
    [Algebra.Etale (MvPolynomial (Fin n) k) A] :
    ∃ t : A ⊗[k] A, Algebra.TensorProduct.lmul' k t = 1 ∧
      ∀ (B : Type*) [CommRing B] [Algebra (A ⊗[k] A) B] [IsLocalization.Away t B],
        (KaehlerDifferential.ideal k A).map (algebraMap (A ⊗[k] A) B) =
          Ideal.ofList ((List.ofFn fun i =>
            algebraMap (MvPolynomial (Fin n) k) A (MvPolynomial.X i) ⊗ₜ[k] (1 : A) -
              (1 : A) ⊗ₜ[k] algebraMap (MvPolynomial (Fin n) k) A (MvPolynomial.X i)).map
                (algebraMap (A ⊗[k] A) B)) ∧
        IsWeaklyRegular B ((List.ofFn fun i =>
            algebraMap (MvPolynomial (Fin n) k) A (MvPolynomial.X i) ⊗ₜ[k] (1 : A) -
              (1 : A) ⊗ₜ[k] algebraMap (MvPolynomial (Fin n) k) A (MvPolynomial.X i)).map
                (algebraMap (A ⊗[k] A) B)) := by
  set P := MvPolynomial (Fin n) k
  set rs : List (A ⊗[k] A) := List.ofFn fun i =>
    algebraMap P A (MvPolynomial.X i) ⊗ₜ[k] (1 : A) -
      (1 : A) ⊗ₜ[k] algebraMap P A (MvPolynomial.X i)
  have hrs : Ideal.ofList rs = a3b3_diagIdeal k P A (Set.range MvPolynomial.X) := by
    simp only [Ideal.ofList, a3b3_diagIdeal, rs]
    congr 1
    ext b
    simp [List.mem_ofFn]
  obtain ⟨t, ht1, ht⟩ := a3b3_exists_diag_elem (k := k) (P := P) (S := A)
    (MvPolynomial.adjoin_range_X (R := k) (σ := Fin n))
  refine ⟨t, ht1, fun B _ _ _ => ⟨?_, ?_⟩⟩
  · rw [← Ideal.map_ofList, hrs]
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro a ha
      obtain ⟨u, hu⟩ := (IsLocalization.Away.algebraMap_isUnit (S := B) t).exists_right_inv
      rw [Ideal.mem_comap]
      have : algebraMap (A ⊗[k] A) B a = algebraMap (A ⊗[k] A) B (a * t) * u := by
        rw [map_mul, mul_assoc, hu, mul_one]
      rw [this]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (ht a ha))
    · refine Ideal.map_mono (Ideal.span_le.2 ?_)
      rintro _ ⟨p, -, rfl⟩
      simp [KaehlerDifferential.ideal, RingHom.mem_ker, Algebra.TensorProduct.lmul'_apply_tmul]
  · exact (a3b3_tensor_isWeaklyRegular n).of_isLocalization B (Submonoid.powers t)

end HodgeLean.Adapters
