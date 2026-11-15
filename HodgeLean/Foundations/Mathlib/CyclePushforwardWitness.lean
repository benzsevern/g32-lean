module

public import Mathlib

/-! # Residue degrees at generic points of affine schemes, Mathlib-only lemmas

At a point `x` of `Spec R` with `x.asIdeal = ⊥`, for a domain `R`, the residue field `κ(x)` is a
fraction field of `R` along the global evaluation `R ≅ Γ(Spec R) → κ(x)`. For an injective ring
map `φ : R → S` of domains, the residue degree of `Spec.map φ` at the generic point of `Spec S`
is then `finrank R S`. The squaring map `X ↦ X²` makes `K[X]` free of rank `2` over itself, with
basis `{1, X}`. These feed the witness theorems of `HodgeLean.Adapters.CyclePushforward`.
HC no distance; AV milestone no distance.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial

namespace HodgeLean.Adapters

universe u

/-- The `R`-algebra structure on `κ(x)` for a point `x` of `Spec R`: the global evaluation
`R ≅ Γ(Spec R) → κ(x)`.
Source: Mathlib, `Scheme.ΓSpecIso` and `Scheme.Γevaluation`. -/
abbrev a1pw_evalAlgebra (R : CommRingCat.{u}) (x : Spec R) : Algebra R ((Spec R).residueField x) :=
  ((Scheme.ΓSpecIso R).inv ≫ (Spec R).Γevaluation x).hom.toAlgebra

/-- At a point of `Spec R` with zero prime ideal, for a domain `R`, the residue field is a fraction
field of `R` along the global evaluation.
Source: Mathlib, `Scheme.Spec.residueFieldIso` and the instance
`IsFractionRing R (⊥ : Ideal R).ResidueField`. -/
theorem a1pw_isFractionRing_residueField (R : CommRingCat.{u}) [IsDomain R] (x : Spec R)
    (hx : x.asIdeal = ⊥) :
    letI := a1pw_evalAlgebra R x
    IsFractionRing R ((Spec R).residueField x) := by
  let := a1pw_evalAlgebra R x
  have := x.isPrime
  have hfr : IsFractionRing R x.asIdeal.ResidueField := by
    obtain ⟨I, hI⟩ := x
    change I = ⊥ at hx
    subst hx
    infer_instance
  let e : x.asIdeal.ResidueField ≃ₐ[R] (Spec R).residueField x :=
    { (Scheme.Spec.residueFieldIso R x).symm.commRingCatIsoToRingEquiv with
      commutes' := fun r => by
        have := congrArg (fun g => g.hom r) (Scheme.Spec.algebraMap_residueFieldIso_inv R x)
        simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
        exact this }
  exact IsLocalization.isLocalization_of_algEquiv _ e

/-- An injective map of domains `φ : R → S` sends the zero prime of `S` to the zero prime of `R`.
Source: Mathlib, `Ideal.comap_bot_of_injective`. -/
theorem a1pw_Spec_map_asIdeal_eq_bot {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (hφ : Function.Injective φ) (x : Spec S) (hx : x.asIdeal = ⊥) :
    ((Spec.map φ) x).asIdeal = ⊥ := by
  change Ideal.comap φ.hom x.asIdeal = ⊥
  rw [hx]
  exact Ideal.comap_bot_of_injective _ hφ

/-- The residue degree of `Spec.map φ` at a point of `Spec S` with zero prime ideal, for an
injective map of domains `φ : R → S`, is `finrank R S` along `φ`.
Source: Fulton, *Intersection Theory*, second edition, §1.4, `deg(V/W) = [K(V) : K(W)]`;
Mathlib, `IsFractionRing.finrank_eq`. -/
theorem a1pw_residueDegree_Spec_map {R S : CommRingCat.{u}} [IsDomain R] [IsDomain S]
    (φ : R ⟶ S) (hφ : Function.Injective φ) (x : Spec S) (hx : x.asIdeal = ⊥) :
    letI := φ.hom.toAlgebra
    (Spec.map φ).residueDegree x = Module.finrank R S := by
  let : Algebra R S := φ.hom.toAlgebra
  let := a1pw_evalAlgebra R ((Spec.map φ) x)
  let := a1pw_evalAlgebra S x
  let : Algebra ((Spec R).residueField ((Spec.map φ) x)) ((Spec S).residueField x) :=
    ((Spec.map φ).residueFieldMap x).hom.toAlgebra
  let : Algebra R ((Spec S).residueField x) :=
    ((algebraMap S ((Spec S).residueField x)).comp φ.hom).toAlgebra
  have : IsScalarTower R S ((Spec S).residueField x) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower R ((Spec R).residueField ((Spec.map φ) x)) ((Spec S).residueField x) := by
    refine IsScalarTower.of_algebraMap_eq fun r => ?_
    simp only [RingHom.algebraMap_toAlgebra, RingHom.comp_apply, CommRingCat.hom_comp]
    rw [Scheme.Γevaluation_naturality_apply]
    congr 1
    have := congrArg (fun g => g.hom r) (Scheme.ΓSpecIso_inv_naturality φ)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
    exact this
  have := a1pw_isFractionRing_residueField R _ (a1pw_Spec_map_asIdeal_eq_bot φ hφ x hx)
  have := a1pw_isFractionRing_residueField S x hx
  exact IsFractionRing.finrank_eq R ((Spec R).residueField ((Spec.map φ) x)) S
    ((Spec S).residueField x)

/-- The residue degree of the structure map `Spec R → Spec k` at a point with zero prime ideal is
`0` when the domain `R` is not a finite `k`-module: `R` embeds `k`-linearly into `κ(x)`, which is
then infinite over `k`.
Source: Mathlib, `Scheme.Hom.residueDegree_eq_finrank`, `Module.Finite.of_injective` and
`Module.finrank_of_not_finite`. -/
theorem a1pw_residueDegree_Spec_map_eq_zero {k : Type u} [Field k] (R : Type u) [CommRing R]
    [IsDomain R] [Algebra k R] (hR : ¬ Module.Finite k R) (x : Spec (.of R))
    (hx : x.asIdeal = ⊥) :
    (Spec.map (CommRingCat.ofHom (algebraMap k R))).residueDegree x = 0 := by
  let : Algebra k ((Spec (.of R)).residueField x) := Algebra.compHom _
    (((Spec (.of R)).Γevaluation x).hom.comp ((Scheme.ΓSpecIso (.of k)).inv ≫
      (Spec.map (CommRingCat.ofHom (algebraMap k R))).appTop).hom)
  rw [Scheme.Hom.residueDegree_eq_finrank]
  apply Module.finrank_of_not_finite
  intro hfin
  apply hR
  let := a1pw_evalAlgebra (.of R) x
  have hfr := a1pw_isFractionRing_residueField (.of R) x hx
  let ev : R →ₗ[k] (Spec (.of R)).residueField x :=
    { toFun := algebraMap R _
      map_add' := map_add _
      map_smul' := fun c r => by
        rw [Algebra.smul_def, map_mul, Algebra.smul_def, RingHom.id_apply]
        congr 1
        have := congrArg (fun g => g.hom c)
          (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap k R)))
        simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
        simp only [RingHom.algebraMap_toAlgebra, CommRingCat.hom_comp,
          RingHom.comp_apply, RingHom.id_apply]
        rw [this] }
  exact Module.Finite.of_injective ev (IsFractionRing.injective (CommRingCat.of R) _)

/-- `aeval (X ^ 2)` is `expand 2`. -/
theorem a1pw_aeval_X_sq_eq_expand {K : Type*} [CommRing K] (f : K[X]) :
    aeval (R := K) (X ^ 2 : K[X]) f = expand K 2 f := by
  rw [expand_eq_comp_X_pow, comp, aeval_def, algebraMap_eq]

/-- Every polynomial is `a(X²) + b(X²) X`, with `a = contract 2 f` and `b = contract 2 (divX f)`.
Source: Mathlib, `Polynomial.coeff_expand` and `Polynomial.coeff_contract`. -/
theorem a1pw_expand_decomp {K : Type*} [CommRing K] (f : K[X]) :
    expand K 2 (contract 2 f) + expand K 2 (contract 2 (divX f)) * X = f := by
  ext n
  rw [coeff_add]
  rcases n with _ | n
  · simp [coeff_expand two_pos, coeff_contract two_ne_zero]
  · rw [coeff_mul_X, coeff_expand two_pos, coeff_expand two_pos, coeff_contract two_ne_zero,
      coeff_contract two_ne_zero, coeff_divX]
    rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · have h1 : ¬ 2 ∣ m + m + 1 := by omega
      have h2 : 2 ∣ m + m := ⟨m, by ring⟩
      rw [ite_eq_right h1, ite_eq_left h2, zero_add, show (m + m) / 2 * 2 + 1 = m + m + 1 by omega]
    · have h1 : 2 ∣ 2 * m + 1 + 1 := ⟨m + 1, by ring⟩
      have h2 : ¬ 2 ∣ 2 * m + 1 := by omega
      rw [ite_eq_left h1, ite_eq_right h2, add_zero, show (2 * m + 1 + 1) / 2 * 2 = 2 * m + 1 + 1 by omega]

/-- `a(X²) + b(X²) X = 0` forces `a = 0` and `b = 0`: the two terms have even and odd support.
Source: Mathlib, `Polynomial.coeff_expand`. -/
theorem a1pw_expand_indep {K : Type*} [CommRing K] (a b : K[X])
    (h : expand K 2 a + expand K 2 b * X = 0) : a = 0 ∧ b = 0 := by
  constructor
  · ext n
    have := congrArg (fun p => coeff p (2 * n)) h
    simp only [coeff_add, coeff_zero] at this
    rcases n with _ | n
    · simpa [coeff_expand two_pos] using this
    · rw [show 2 * (n + 1) = (2 * n + 1) + 1 by ring, coeff_mul_X, coeff_expand two_pos,
        coeff_expand two_pos, ite_eq_left ⟨n + 1, by ring⟩, ite_eq_right (by omega), add_zero,
        show (2 * n + 1 + 1) / 2 = n + 1 by omega] at this
      simpa using this
  · ext n
    have := congrArg (fun p => coeff p (2 * n + 1)) h
    simp only [coeff_add, coeff_zero] at this
    rw [coeff_mul_X, coeff_expand two_pos, coeff_expand two_pos, ite_eq_right (by omega),
      ite_eq_left ⟨n, rfl⟩, zero_add, show 2 * n / 2 = n by omega] at this
    simpa using this

/-- An algebra `B` over `A` with `B = A ⊕ A t` (every element is uniquely `a + b t`) has
rank `2`.
Source: Mathlib, `Module.Basis.mk` and `Module.finrank_eq_card_basis`. -/
theorem a1pw_finrank_eq_two {A B : Type*} [CommRing A] [Nontrivial A] [CommRing B] [Algebra A B]
    (t : B) (hli : ∀ a b : A, algebraMap A B a + algebraMap A B b * t = 0 → a = 0 ∧ b = 0)
    (hsp : ∀ f : B, ∃ a b : A, algebraMap A B a + algebraMap A B b * t = f) :
    Module.finrank A B = 2 := by
  have hli' : LinearIndependent A ![(1 : B), t] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_two] at hg
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Algebra.smul_def, mul_one] at hg
    obtain ⟨h0, h1⟩ := hli _ _ hg
    intro i
    fin_cases i
    · exact h0
    · exact h1
  have hsp' : ⊤ ≤ Submodule.span A (Set.range ![(1 : B), t]) := by
    intro f _
    obtain ⟨a, b, rfl⟩ := hsp f
    refine Submodule.add_mem _ ?_ ?_
    · rw [← mul_one (algebraMap A B a), ← Algebra.smul_def]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)
    · rw [← Algebra.smul_def]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩)
  rw [Module.finrank_eq_card_basis (Module.Basis.mk hli' hsp'), Fintype.card_fin]

/-- `K[X]` over itself along `X ↦ X²` is free of rank `2`, with basis `{1, X}`.
Source: Lang, *Algebra*, revised third edition, V, §1; the decomposition
`f = a(X²) + b(X²) X`. -/
theorem a1pw_finrank_aeval_X_sq (K : Type*) [CommRing K] [Nontrivial K] :
    @Module.finrank K[X] K[X] _ _
      (aeval (R := K) (X ^ 2 : K[X])).toRingHom.toAlgebra.toModule = 2 := by
  let := (aeval (R := K) (X ^ 2 : K[X])).toRingHom.toAlgebra
  have hmap : ∀ a : K[X], algebraMap K[X] K[X] a = expand K 2 a := fun a => by
    rw [RingHom.algebraMap_toAlgebra, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      a1pw_aeval_X_sq_eq_expand]
  refine a1pw_finrank_eq_two X (fun a b h => ?_) (fun f => ⟨contract 2 f, contract 2 (divX f), ?_⟩)
  · rw [hmap, hmap] at h
    exact a1pw_expand_indep a b h
  · rw [hmap, hmap]
    exact a1pw_expand_decomp f

end HodgeLean.Adapters
