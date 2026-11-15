import HodgeLean.Adapters.IntersectionProductDiagonalLocal

/-! # Serre's vanishing theorem on a smooth affine variety

Let `k` be algebraically closed and `S` a finitely generated `k`-domain of dimension `d`, étale over
`k[x_1, …, x_d]`. For primes `𝔭`, `𝔮` of `S` and a prime `R` minimal over `𝔭 + 𝔮` with
`ht R < ht 𝔭 + ht 𝔮` (equivalently `dim S_R/𝔭 + dim S_R/𝔮 < dim S_R`),
`Σ_{i ≤ m} (-1)^i ℓ(Tor_i^S(S/𝔭, S/𝔮)_R) = 0` for `m ≥ d` (`a3w_vanishing_affine`).

The proof is Serre's reduction to the diagonal. Let `B` be the local ring of `S ⊗_k S` at `(R, R)`:
* `Tor_i^S(S/𝔭, S/𝔮) ≅ Tor_i^{S ⊗ S}((S/𝔭) ⊗_k (S/𝔮), S)` (`a3d_tor_diag`), a module killed by the
  kernel of the multiplication, so its length at `R` is the length over `B` of its base change
  (`a3v_locLen_eq`, `a3w_length_eq`);
* `B ⊗ S ≅ B ⧸ (x_i ⊗ 1 - 1 ⊗ x_i)` (`a3w_extSD`), a quotient by a regular sequence of length `d`
  (`a3v_xs_isWeaklyRegular`);
* the base change `M_B` of `(S/𝔭) ⊗_k (S/𝔮)` is killed by `𝔭 ⊗ 1` and `1 ⊗ 𝔮`, so a prime in its
  support containing the `x_i ⊗ 1 - 1 ⊗ x_i` is the closed point (`a3w_supp_closed`, from the
  minimality of `R`) and every prime in its support has dimension below `d` (`a3w_supp_dim`,
  from the dimension formula in `S ⊗_k S`);
* Serre's vanishing against a quotient by a regular sequence (`a3s_vanishing`) applies.

Source: Serre, *Algèbre locale, multiplicités*, Chapitre V, B.3, Théorème 1 and its proof.
HC no distance; AV milestone no distance.
-/

open CategoryTheory CategoryTheory.Limits MonoidalCategory TensorProduct IsLocalRing

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace HodgeLean.Adapters

section iso
variable (k : Type) [Field k] {S : Type} [CommRing S] [Algebra k S] (d : ℕ)
  [Algebra (MvPolynomial (Fin d) k) S] [IsScalarTower k (MvPolynomial (Fin d) k) S]
  [Algebra.Etale (MvPolynomial (Fin d) k) S] (R : Ideal S) [R.IsPrime]

omit [IsScalarTower k (MvPolynomial (Fin d) k) S] [Algebra.Etale (MvPolynomial (Fin d) k) S]
  [Algebra (MvPolynomial (Fin d) k) S] [R.IsPrime] in
/-- `S_Δ ≅ (S ⊗ S) ⧸ ker μ`. -/
def a3w_SDquot : ModuleCat.of (S ⊗[k] S) ((S ⊗[k] S) ⧸ RingHom.ker (a3d_mu k S)) ≅
    a3d_SD k S :=
  LinearEquiv.toModuleIso (X₂ := (a3d_SD k S : Type))
    (LinearEquiv.ofBijective
      { toFun := fun x => (show a3d_SD k S from Ideal.Quotient.lift _ (a3d_mu k S) (fun _ h => h) x)
        map_add' := fun x y => map_add _ x y
        map_smul' := fun t x => by
          obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
          change Ideal.Quotient.lift _ (a3d_mu k S) _ (Ideal.Quotient.mk _ (t * x)) =
            a3d_mu k S t * Ideal.Quotient.lift _ (a3d_mu k S) _ (Ideal.Quotient.mk _ x)
          simp }
      (RingHom.quotientKerEquivOfSurjective (f := a3d_mu k S)
        (fun s => ⟨s ⊗ₜ[k] (1 : S), by simp⟩)).bijective)

/-- `B ⊗_{S ⊗ S} S_Δ ≅ B ⧸ (x_i ⊗ 1 - 1 ⊗ x_i)`, the iterated quotient. -/
def a3w_extSD : (ModuleCat.extendScalars (algebraMap (S ⊗[k] S) (a3v_B k S R))).obj (a3d_SD k S) ≅
    a3c_iterQuot (a3v_xs k d R) (ModuleCat.of (a3v_B k S R) (a3v_B k S R)) :=
  (ModuleCat.extendScalars _).mapIso (a3w_SDquot k).symm ≪≫
    (show (ModuleCat.extendScalars (algebraMap (S ⊗[k] S) (a3v_B k S R))).obj
        (ModuleCat.of (S ⊗[k] S) ((S ⊗[k] S) ⧸ RingHom.ker (a3d_mu k S))) ≅
        ModuleCat.of (a3v_B k S R) (a3v_B k S R ⧸
          (RingHom.ker (a3d_mu k S)).map (algebraMap (S ⊗[k] S) (a3v_B k S R))) from
      letI := (algebraMap (S ⊗[k] S) (a3v_B k S R)).toAlgebra
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (a3v_B k S R)
        (RingHom.ker (a3d_mu k S))).toLinearEquiv.toModuleIso.symm) ≪≫
    (Submodule.quotEquivOfEq _ _ (by
      rw [a3v_ofList_xs, Ideal.smul_eq_mul, Ideal.mul_top])).toModuleIso ≪≫
    (a3c_iterQuotEquiv (a3v_xs k d R) (ModuleCat.of (a3v_B k S R) (a3v_B k S R))).toModuleIso.symm

end iso
section ann
variable (k : Type) [Field k] {S : Type} [CommRing S] [Algebra k S] (𝔭 𝔮 : Ideal S)

/-- The `S ⊗_k S`-module `(S ⧸ 𝔭) ⊗_k (S ⧸ 𝔮)` of the reduction to the diagonal. -/
abbrev a3w_XM : ModuleCat.{0} (S ⊗[k] S) := a3d_XM k S (S ⧸ 𝔮) (ModuleCat.of S (S ⧸ 𝔭))

theorem a3w_ext_ann (p : S) (hp : p ∈ 𝔭)
    (a : (ModuleCat.extendScalars (a3d_inl k S)).obj (ModuleCat.of S (S ⧸ 𝔭))) :
    algebraMap S (S ⊗[k] S) p • a = 0 := by
  induction a using TensorProduct.inductionOn with
  | tmul t m =>
    have hm : p • (show ModuleCat.of S (S ⧸ 𝔭) from m) = 0 := by
      obtain ⟨m, rfl⟩ := Ideal.Quotient.mk_surjective m
      change Ideal.Quotient.mk 𝔭 (p * m) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mul_mem_right _ _ hp)
    change (p • t) ⊗ₜ[S] (show ModuleCat.of S (S ⧸ 𝔭) from m) = 0
    rw [TensorProduct.smul_tmul, hm, TensorProduct.tmul_zero]
  | add a a' ha ha' => rw [smul_add, ha, ha', add_zero]

theorem a3w_XM_ann_left (p : S) (hp : p ∈ 𝔭) (x : a3w_XM k 𝔭 𝔮) :
    algebraMap S (S ⊗[k] S) p • x = 0 := by
  induction x using TensorProduct.inductionOn with
  | tmul a b => rw [TensorProduct.smul_tmul', a3w_ext_ann k 𝔭 p hp, TensorProduct.zero_tmul]
  | add x y hx hy => rw [smul_add, hx, hy, add_zero]

theorem a3w_XN_ann (q : S) (hq : q ∈ 𝔮) (b : a3d_XN k S (S ⧸ 𝔮)) :
    ((1 : S) ⊗ₜ[k] q : S ⊗[k] S) • b = 0 := by
  induction b using TensorProduct.inductionOn with
  | tmul s n =>
    change ((1 : S) ⊗ₜ[k] q : S ⊗[k] S) • a3d_XN.mk k S (S ⧸ 𝔮) s n = 0
    rw [a3d_XN_smul_mk]
    obtain ⟨n, rfl⟩ := Ideal.Quotient.mk_surjective n
    have : q • Ideal.Quotient.mk 𝔮 n = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mul_mem_right _ _ hq)
    rw [this]
    exact TensorProduct.tmul_zero _ _
  | add a a' ha ha' => rw [smul_add, ha, ha', add_zero]

theorem a3w_XM_ann_right (q : S) (hq : q ∈ 𝔮) (x : a3w_XM k 𝔭 𝔮) :
    ((1 : S) ⊗ₜ[k] q : S ⊗[k] S) • x = 0 := by
  induction x using TensorProduct.inductionOn with
  | tmul a b => rw [← TensorProduct.tmul_smul, a3w_XN_ann k 𝔮 q hq, TensorProduct.tmul_zero]
  | add x y hx hy => rw [smul_add, hx, hy, add_zero]

/-- `S ⊗_k (S ⧸ 𝔮)` is generated by `1 ⊗ 1` over `S ⊗_k S`. -/
instance a3w_XN_finite : Module.Finite (S ⊗[k] S) (a3d_XN k S (S ⧸ 𝔮)) := by
  refine ⟨⟨{a3d_XN.mk k S (S ⧸ 𝔮) 1 1}, ?_⟩⟩
  rw [eq_top_iff]
  rintro x -
  induction x using TensorProduct.inductionOn with
  | tmul s n =>
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective n
    have : a3d_XN.mk k S (S ⧸ 𝔮) s (Ideal.Quotient.mk 𝔮 b) =
        (s ⊗ₜ[k] b : S ⊗[k] S) • a3d_XN.mk k S (S ⧸ 𝔮) 1 1 := by
      rw [a3d_XN_smul_mk, mul_one, Algebra.smul_def, mul_one]
      rfl
    change a3d_XN.mk k S (S ⧸ 𝔮) s (Ideal.Quotient.mk 𝔮 b) ∈ _
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  | add x y hx hy => exact add_mem hx hy

/-- `(S ⊗ S) ⊗_S (S ⧸ 𝔭)` is generated by `1 ⊗ 1`. -/
instance a3w_ext_finite :
    Module.Finite (S ⊗[k] S) ((ModuleCat.extendScalars (a3d_inl k S)).obj
      (ModuleCat.of S (S ⧸ 𝔭))) := by
  let := (a3d_inl k S).toAlgebra
  exact Module.Finite.base_change S (S ⊗[k] S) (S ⧸ 𝔭)

instance a3w_XM_finite : Module.Finite (S ⊗[k] S) (a3w_XM k 𝔭 𝔮) := by
  change Module.Finite (S ⊗[k] S) (TensorProduct (S ⊗[k] S) _ (a3d_XN k S (S ⧸ 𝔮)))
  infer_instance

end ann

section extLen
open scoped ChangeOfRings

/-- Extension of scalars along an algebra map is the usual base change. -/
def a3w_extEquiv {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (M : ModuleCat.{0} A) :
    ((ModuleCat.extendScalars (algebraMap A B)).obj M : Type) ≃ₗ[B] B ⊗[A] M :=
  let e0 : ((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B) : Type) ≃ₗ[A] B :=
    { AddEquiv.refl _ with
      map_smul' := fun a b => by
        change algebraMap A B a * (show B from b) = a • (show B from b)
        rw [Algebra.smul_def] }
  let e := TensorProduct.congr e0 (LinearEquiv.refl A M)
  { e.toAddEquiv with
    map_smul' := fun b x => by
      induction x using TensorProduct.inductionOn with
      | tmul b' m =>
        change e ((b * show B from b') ⊗ₜ[A, algebraMap A B] m) = b • e (b' ⊗ₜ[A, algebraMap A B] m)
        rfl
      | add x y hx hy =>
        change e (b • (x + y)) = b • e (x + y)
        change e (b • x) = b • e x at hx
        change e (b • y) = b • e y at hy
        rw [smul_add, map_add, map_add, hx, hy, smul_add] }

/-- Extension of scalars along an algebra map has the length of the usual base change. -/
theorem a3w_length_extendScalars {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
    (M : ModuleCat.{0} A) :
    Module.length B ((ModuleCat.extendScalars (algebraMap A B)).obj M) =
      Module.length B (B ⊗[A] M) :=
  (a3w_extEquiv M).length_eq

/-- `B ⊗_A (A ⧸ I) ≅ B ⧸ I B` for extension of scalars. -/
def a3w_extQuot {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (I : Ideal A) :
    (ModuleCat.extendScalars (algebraMap A B)).obj (ModuleCat.of A (A ⧸ I)) ≅
      ModuleCat.of B (B ⧸ I.map (algebraMap A B)) :=
  ((a3w_extEquiv (ModuleCat.of A (A ⧸ I))).trans
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I).symm.toLinearEquiv).toModuleIso

end extLen

section supp
variable (k : Type) [Field k] {S : Type} [CommRing S] [Algebra k S] (d : ℕ)
  [Algebra (MvPolynomial (Fin d) k) S] [IsScalarTower k (MvPolynomial (Fin d) k) S]
  [Algebra.Etale (MvPolynomial (Fin d) k) S] (𝔭 𝔮 R : Ideal S) [R.IsPrime]

/-- The base change of `(S ⧸ 𝔭) ⊗_k (S ⧸ 𝔮)` to `B`. -/
abbrev a3w_MB : ModuleCat.{0} (a3v_B k S R) :=
  (ModuleCat.extendScalars (algebraMap (S ⊗[k] S) (a3v_B k S R))).obj (a3w_XM k 𝔭 𝔮)

omit [IsScalarTower k (MvPolynomial (Fin d) k) S] [Algebra.Etale (MvPolynomial (Fin d) k) S] in
instance a3w_MB_finite : Module.Finite (a3v_B k S R) (a3w_MB k 𝔭 𝔮 R) := by
  let := (algebraMap (S ⊗[k] S) (a3v_B k S R)).toAlgebra
  exact Module.Finite.base_change (S ⊗[k] S) (a3v_B k S R) (a3w_XM k 𝔭 𝔮)

omit [IsScalarTower k (MvPolynomial (Fin d) k) S] [Algebra.Etale (MvPolynomial (Fin d) k) S] in
theorem a3w_mem_annihilator (t : S ⊗[k] S) (ht : ∀ x : a3w_XM k 𝔭 𝔮, t • x = 0) :
    algebraMap (S ⊗[k] S) (a3v_B k S R) t ∈ Module.annihilator (a3v_B k S R) (a3w_MB k 𝔭 𝔮 R) := by
  rw [Module.mem_annihilator]
  intro m
  induction m using TensorProduct.inductionOn with
  | tmul b x =>
    change (t • b) ⊗ₜ[S ⊗[k] S] x = 0
    rw [TensorProduct.smul_tmul, ht x, TensorProduct.tmul_zero]
  | add m m' hm hm' => rw [smul_add, hm, hm', add_zero]

omit [IsScalarTower k (MvPolynomial (Fin d) k) S] [Algebra.Etale (MvPolynomial (Fin d) k) S] in
/-- The primes in the support of `M_B` contain `𝔭 ⊗ 1` and `1 ⊗ 𝔮`. -/
theorem a3w_supp_mem (𝔔 : PrimeSpectrum (a3v_B k S R))
    (h𝔔 : 𝔔 ∈ Module.support (a3v_B k S R) (a3w_MB k 𝔭 𝔮 R)) :
    (∀ p ∈ 𝔭, algebraMap S (S ⊗[k] S) p ∈ 𝔔.asIdeal.comap (algebraMap (S ⊗[k] S) (a3v_B k S R))) ∧
      ∀ q ∈ 𝔮, ((1 : S) ⊗ₜ[k] q : S ⊗[k] S) ∈
        𝔔.asIdeal.comap (algebraMap (S ⊗[k] S) (a3v_B k S R)) := by
  rw [Module.mem_support_iff_of_finite] at h𝔔
  exact ⟨fun p hp => h𝔔 (a3w_mem_annihilator k 𝔭 𝔮 R _ (a3w_XM_ann_left k 𝔭 𝔮 p hp)),
    fun q hq => h𝔔 (a3w_mem_annihilator k 𝔭 𝔮 R _ (a3w_XM_ann_right k 𝔭 𝔮 q hq))⟩

/-- A prime in the support of `M_B` containing the coordinate differences is the closed point. -/
theorem a3w_supp_closed (hR : R ∈ (𝔭 ⊔ 𝔮).minimalPrimes) (𝔔 : PrimeSpectrum (a3v_B k S R))
    (h𝔔 : 𝔔 ∈ Module.support (a3v_B k S R) (a3w_MB k 𝔭 𝔮 R))
    (hx : Ideal.ofList (a3v_xs k d R) ≤ 𝔔.asIdeal) : 𝔔 = closedPoint (a3v_B k S R) := by
  obtain ⟨hp, hq⟩ := a3w_supp_mem k 𝔭 𝔮 R 𝔔 h𝔔
  set Q := 𝔔.asIdeal.comap (algebraMap (S ⊗[k] S) (a3v_B k S R))
  have hQM : Q ≤ a3v_M k S R := by
    rw [← IsLocalization.AtPrime.under_maximalIdeal (a3v_B k S R) (a3v_M k S R)]
    exact Ideal.comap_mono (IsLocalRing.le_maximalIdeal 𝔔.isPrime.ne_top)
  have hI : RingHom.ker (a3d_mu k S) ≤ Q := by
    rw [a3v_ofList_xs] at hx
    exact Ideal.map_le_iff_le_comap.1 hx
  have hdiff : ∀ t : S ⊗[k] S, t - algebraMap S (S ⊗[k] S) (a3d_mu k S t) ∈ Q := fun t =>
    hI (by rw [RingHom.mem_ker, map_sub, a3v_mu_inl, sub_self])
  set R' := Q.comap (algebraMap S (S ⊗[k] S))
  have hR'R : R' ≤ R := fun s hs => by
    have := hQM hs
    change a3d_mu k S (algebraMap S (S ⊗[k] S) s) ∈ R at this
    rwa [a3v_mu_inl] at this
  have hpq : 𝔭 ⊔ 𝔮 ≤ R' := by
    refine sup_le (fun p h => hp p h) (fun q h => ?_)
    change algebraMap S (S ⊗[k] S) q ∈ Q
    have h1 := hdiff ((1 : S) ⊗ₜ[k] q)
    have h2 : algebraMap S (S ⊗[k] S) (a3d_mu k S ((1 : S) ⊗ₜ[k] q)) =
        algebraMap S (S ⊗[k] S) q := by simp
    rw [h2] at h1
    have := Q.sub_mem (hq q h) h1
    rwa [sub_sub_cancel] at this
  have hRR' : R ≤ R' := hR.2 ⟨Ideal.comap_isPrime _ _, hpq⟩ hR'R
  have hMQ : a3v_M k S R ≤ Q := fun t ht => by
    have h1 : algebraMap S (S ⊗[k] S) (a3d_mu k S t) ∈ Q := hRR' ht
    have := Q.add_mem (hdiff t) h1
    rwa [sub_add_cancel] at this
  have hQ : Q = a3v_M k S R := le_antisymm hQM hMQ
  ext1
  change 𝔔.asIdeal = maximalIdeal (a3v_B k S R)
  rw [← IsLocalization.map_under (a3v_M k S R).primeCompl (a3v_B k S R) 𝔔.asIdeal]
  change Q.map _ = _
  rw [hQ, Localization.AtPrime.map_eq_maximalIdeal]

omit [Algebra (MvPolynomial (Fin d) k) S] [IsScalarTower k (MvPolynomial (Fin d) k) S]
  [Algebra.Etale (MvPolynomial (Fin d) k) S] in
/-- The primes in the support of `M_B` have dimension below `d` when
`ht R < ht 𝔭 + ht 𝔮`: `dim B ⧸ 𝔔 ≤ dim B - ht 𝔔 ≤ (d + ht R) - (ht 𝔭 + ht 𝔮)`, since `𝔔` lies
over a prime of `S ⊗_k S` containing the kernel of `S ⊗_k S → (S ⧸ 𝔭) ⊗_k (S ⧸ 𝔮)`. -/
theorem a3w_supp_dim [IsAlgClosed k] [IsDomain S] [Algebra.FiniteType k S]
    (hdim : ringKrullDim S = d) [𝔭.IsPrime] [𝔮.IsPrime]
    (hlt : R.height < 𝔭.height + 𝔮.height) (𝔔 : PrimeSpectrum (a3v_B k S R))
    (h𝔔 : 𝔔 ∈ Module.support (a3v_B k S R) (a3w_MB k 𝔭 𝔮 R)) :
    ringKrullDim (a3v_B k S R ⧸ 𝔔.asIdeal) < d := by
  obtain ⟨hp, hq⟩ := a3w_supp_mem k 𝔭 𝔮 R 𝔔 h𝔔
  have : Algebra.FiniteType k (S ⊗[k] S) := Algebra.FiniteType.trans (S := S) inferInstance
    inferInstance
  have : IsDomain (S ⊗[k] S) := hc9k8_isDomain_tensorProduct
  set Q := 𝔔.asIdeal.comap (algebraMap (S ⊗[k] S) (a3v_B k S R))
  have : Q.IsPrime := Ideal.comap_isPrime _ _
  -- the quotient `(S ⧸ 𝔭) ⊗ (S ⧸ 𝔮)` maps onto `(S ⊗ S) ⧸ Q`
  let f := Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k 𝔭) (Ideal.Quotient.mkₐ k 𝔮)
  have hf : Function.Surjective f := Algebra.TensorProduct.map_surjective _ _
    (Ideal.Quotient.mkₐ_surjective k 𝔭) (Ideal.Quotient.mkₐ_surjective k 𝔮)
  have hker : RingHom.ker f ≤ Q := by
    rw [Algebra.TensorProduct.map_ker _ _ (Ideal.Quotient.mkₐ_surjective k 𝔭)
      (Ideal.Quotient.mkₐ_surjective k 𝔮)]
    refine sup_le (Ideal.map_le_iff_le_comap.2 fun p h => ?_)
      (Ideal.map_le_iff_le_comap.2 fun q h => ?_)
    · exact hp p (Ideal.Quotient.eq_zero_iff_mem.1 h)
    · exact hq q (Ideal.Quotient.eq_zero_iff_mem.1 h)
  let g : (S ⧸ 𝔭) ⊗[k] (S ⧸ 𝔮) →+* (S ⊗[k] S) ⧸ Q :=
    (Ideal.Quotient.factor hker).comp
      (RingHom.quotientKerEquivOfSurjective hf).symm.toRingHom
  have hg : Function.Surjective g :=
    (Ideal.Quotient.factor_surjective hker).comp (RingHom.quotientKerEquivOfSurjective hf).symm.surjective
  have hQdim := ringKrullDim_le_of_surjective g hg
  have : Nontrivial (S ⧸ 𝔭) := Ideal.Quotient.nontrivial_iff.mpr Ideal.IsPrime.ne_top'
  have : Nontrivial (S ⧸ 𝔮) := Ideal.Quotient.nontrivial_iff.mpr Ideal.IsPrime.ne_top'
  rw [hc9k8_ringKrullDim_tensorProduct] at hQdim
  -- the dimension formulas
  have h𝔭 := hc9k8_height_add_ringKrullDim_quotient (k := k) 𝔭
  have h𝔮 := hc9k8_height_add_ringKrullDim_quotient (k := k) 𝔮
  have hRd := hc9k8_height_add_ringKrullDim_quotient (k := k) R
  rw [hdim] at h𝔭 h𝔮 hRd
  have hT := hc9k8_height_add_ringKrullDim_quotient (k := k) Q
  rw [hc9k8_ringKrullDim_tensorProduct, hdim] at hT
  have hB := a3c_height_add_ringKrullDim_quotient_of_isLocalization (k := k) (a3v_M k S R)
    (a3v_B k S R) 𝔔.asIdeal
  rw [← IsLocalization.height_under (a3v_M k S R).primeCompl 𝔔.asIdeal] at hB
  obtain ⟨b, e𝔭, hb, he𝔭, hb'⟩ := a3m_withBot_add_eq_nat h𝔭
  obtain ⟨c, e𝔮, hc, he𝔮, hc'⟩ := a3m_withBot_add_eq_nat h𝔮
  obtain ⟨a, eR, ha, heR, ha'⟩ := a3m_withBot_add_eq_nat hRd
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height (a3v_M k S R) (a3v_B k S R),
    a3v_height_M k d R hdim a ha] at hB
  have hT' : (Q.height : WithBot ℕ∞) + ringKrullDim ((S ⊗[k] S) ⧸ Q) = ((d + d : ℕ) : WithBot ℕ∞) := by
    rw [hT]; push_cast; rfl
  obtain ⟨h, e, hh, he, hhe⟩ := a3m_withBot_add_eq_nat hT'
  obtain ⟨h', f', hh', hf', hhf⟩ := a3m_withBot_add_eq_nat hB
  have hQ : Q = 𝔔.asIdeal.under (S ⊗[k] S) := rfl
  rw [← hQ, hh] at hh'
  have hhh : h' = h := by exact_mod_cast hh'.symm
  rw [he, he𝔭, he𝔮] at hQdim
  have hle : e ≤ e𝔭 + e𝔮 := by exact_mod_cast hQdim
  rw [ha, hb, hc] at hlt
  have hlt' : a < b + c := by exact_mod_cast hlt
  rw [hf']
  exact_mod_cast (by omega : f' < d)

/-- The lengths in Serre's alternating sum at `R` are the lengths of `Tor` over `B` against the
quotient by the coordinate differences. -/
theorem a3w_length_eq (i : ℕ) :
    a3e_locLen ⟨R, inferInstance⟩ (((Tor (ModuleCat.{0} S) i).obj
      (ModuleCat.of S (S ⧸ 𝔭))).obj (ModuleCat.of S (S ⧸ 𝔮))) =
    Module.length (a3v_B k S R) (((Tor (ModuleCat.{0} (a3v_B k S R)) i).obj
      (a3w_MB k 𝔭 𝔮 R)).obj (a3c_iterQuot (a3v_xs k d R)
        (ModuleCat.of (a3v_B k S R) (a3v_B k S R)))) := by
  obtain ⟨e0⟩ := a3d_tor_diag k S (S ⧸ 𝔮) (ModuleCat.of S (S ⧸ 𝔭)) i
  rw [a3e_locLen_congr _ e0.toLinearEquiv]
  set F := ((Tor (ModuleCat.{0} (S ⊗[k] S)) i).obj (a3w_XM k 𝔭 𝔮)).obj (a3d_SD k S)
  have hF : ∀ a ∈ RingHom.ker (a3d_mu k S), ∀ f : F, a • f = 0 := by
    intro a ha f
    refine a3c_smul_tor_eq_zero_of_mem_annihilator_right _ _ a ?_ i f
    rw [Module.mem_annihilator]
    intro x
    change a3d_mu k S a * (show S from x) = 0
    rw [RingHom.mem_ker.1 ha, zero_mul]
  rw [← a3v_locLen_eq k S R F hF]
  let f := algebraMap (S ⊗[k] S) (a3v_B k S R)
  have hf : f.Flat := RingHom.flat_algebraMap_iff.mpr
    (IsLocalization.flat (a3v_B k S R) (a3v_M k S R).primeCompl)
  obtain ⟨eb⟩ := a3q_tor_baseChange f hf (a3w_XM k 𝔭 𝔮) (a3d_SD k S) i
  have e2 := ((Tor (ModuleCat.{0} (a3v_B k S R)) i).obj (a3w_MB k 𝔭 𝔮 R)).mapIso
    (a3w_extSD k d R).symm
  rw [(e2 ≪≫ eb).toLinearEquiv.length_eq]
  rw [a3w_length_extendScalars]
  exact a3q_locLen_eq_length ⟨a3v_M k S R, inferInstance⟩ _ _
    (TensorProduct.mk _ (a3v_B k S R) F 1)

/-- Serre's vanishing theorem on a smooth affine variety with étale coordinates: let `k` be
algebraically closed, `S` a finitely generated `k`-domain of dimension `d`, étale over
`k[x_1, …, x_d]`, and `𝔭`, `𝔮`, `R` primes of `S` with `R` minimal over `𝔭 + 𝔮` and
`ht R < ht 𝔭 + ht 𝔮` (that is, `dim S_R/𝔭 + dim S_R/𝔮 < dim S_R`). Then
`Σ_{i ≤ m} (-1)^i ℓ(Tor_i^S(S/𝔭, S/𝔮)_R) = 0` for `m ≥ d`.
The proof is the reduction to the diagonal: these lengths are those of
`Tor_i^B((S/𝔭 ⊗_k S/𝔮)_B, B/(x ⊗ 1 - 1 ⊗ x))` over the local ring `B` of `S ⊗_k S` at `(R, R)`, where
the `x_i ⊗ 1 - 1 ⊗ x_i` form a regular sequence of length `d` and the support of
`(S/𝔭 ⊗_k S/𝔮)_B` has dimension below `d`.
Source: Serre, *Algèbre locale, multiplicités*, Chapitre V, B.3, Théorème 1 and its proof
(réduction à la diagonale). -/
theorem a3w_vanishing_affine [IsAlgClosed k] [IsDomain S] [Algebra.FiniteType k S]
    (hdim : ringKrullDim S = d) [𝔭.IsPrime] [𝔮.IsPrime] (hR : R ∈ (𝔭 ⊔ 𝔮).minimalPrimes)
    (hlt : R.height < 𝔭.height + 𝔮.height) (m : ℕ) (hm : d ≤ m) :
    ∑ i ∈ Finset.range (m + 1), (-1 : ℤ) ^ i *
      ((a3e_locLen ⟨R, inferInstance⟩ (((Tor (ModuleCat.{0} S) i).obj
        (ModuleCat.of S (S ⧸ 𝔭))).obj (ModuleCat.of S (S ⧸ 𝔮)))).toNat : ℤ) = 0 := by
  have : Algebra.FiniteType k (S ⊗[k] S) := Algebra.FiniteType.trans (S := S) inferInstance
    inferInstance
  have : IsNoetherianRing (S ⊗[k] S) := Algebra.FiniteType.isNoetherianRing k _
  obtain ⟨hreg, hmem⟩ := a3v_xs_isWeaklyRegular k d R hdim
  have hv := a3s_vanishing (B := a3v_B k S R) d (a3v_xs k d R) (a3v_xs_length k d R) hreg hmem
    (a3w_MB k 𝔭 𝔮 R) (fun 𝔔 h𝔔 hx => a3w_supp_closed k d 𝔭 𝔮 R hR 𝔔 h𝔔 hx)
    (fun 𝔔 h𝔔 => a3w_supp_dim k d 𝔭 𝔮 R hdim hlt 𝔔 h𝔔) m hm
  unfold a3s_chi at hv
  rw [← hv]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [a3w_length_eq k d 𝔭 𝔮 R i]

end supp

end HodgeLean.Adapters
