import HodgeLean.Adapters.KleimanCoheightCharts
import HodgeLean.Foundations.Mathlib.CyclePushforwardCore

/-! # Dimension of a point and transcendence degree of its residue field

For a scheme `X` locally of finite type over `ℂ`, the height of a point `x` in the specialization
order (the dimension of `closure {x}`) is the transcendence degree of `κ(x)` over `ℂ`. On an affine
chart `Spec A` this is the dimension of `A ⧸ p`, which Noether normalization identifies with the
transcendence degree of the residue field at `p`. The degree of a morphism over `ℂ` at a point is
therefore positive exactly when the height does not drop.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial

namespace HodgeLean.Adapters

theorem a1d_trdeg_eq_of_eval {k A K : Type} [Field k] [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] [Field K] [Algebra k K] (φ : A →ₐ[k] K)
    (hφ : ∀ y : K, ∃ a s : A, φ s ≠ 0 ∧ φ a = y * φ s) :
    ∃ n : ℕ, ringKrullDim (A ⧸ RingHom.ker φ) = n ∧ Algebra.trdeg k K = n := by
  set P := RingHom.ker φ
  have : P.IsPrime := RingHom.ker_isPrime φ
  let B := A ⧸ P
  let ψ : B →ₐ[k] K := Ideal.kerLiftAlg φ
  have hψ : Function.Injective ψ := Ideal.kerLiftAlg_injective φ
  have : IsDomain B := Ideal.Quotient.isDomain P
  obtain ⟨n, hdim, htr⟩ := Algebra.FiniteType.exists_ringKrullDim_eq_and_trdeg_eq (k := k) (A := B)
  refine ⟨n, hdim, ?_⟩
  let : Algebra B K := ψ.toRingHom.toAlgebra
  have : IsScalarTower k B K := IsScalarTower.of_algebraMap_eq fun c => (ψ.commutes c).symm
  have : FaithfulSMul B K := (faithfulSMul_iff_algebraMap_injective _ _).mpr hψ
  have : Algebra.IsAlgebraic B K := by
    refine ⟨fun y => ?_⟩
    obtain ⟨a, s, hs, ha⟩ := hφ y
    refine ⟨C (Ideal.Quotient.mk P s) * X - C (Ideal.Quotient.mk P a), ?_, ?_⟩
    · intro h
      have := congrArg (fun p => p.coeff 1) h
      simp only [coeff_sub, coeff_C_mul_X, coeff_C, one_ne_zero, ite_true, ite_false, sub_zero,
        coeff_zero] at this
      exact hs (by
        have h2 : ψ (Ideal.Quotient.mk P s) = φ s := Ideal.kerLiftAlg_mk φ s
        rw [← h2, this, map_zero])
    · simp only [map_sub, map_mul, aeval_C, aeval_X]
      change ψ (Ideal.Quotient.mk P s) * y - ψ (Ideal.Quotient.mk P a) = 0
      rw [Ideal.kerLiftAlg_mk, Ideal.kerLiftAlg_mk, ha, mul_comm, sub_self]
  have h := trdeg_add_eq k B (A := K)
  have hz : Algebra.trdeg B K = 0 := trdeg_eq_zero
  rw [hz, add_zero] at h
  rw [← h, htr]

theorem a1d_fg_of_eval {k A K : Type} [Field k] [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] [Field K] [Algebra k K] (φ : A →ₐ[k] K)
    (hφ : ∀ y : K, ∃ a s : A, φ s ≠ 0 ∧ φ a = y * φ s) :
    Algebra.EssFiniteType k K := by
  classical
  rw [← IntermediateField.fg_top_iff]
  obtain ⟨t, ht⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra k A).FG)
  refine ⟨t.image φ, top_le_iff.mp fun y _ => ?_⟩
  have hmem : ∀ a : A, φ a ∈ IntermediateField.adjoin k ((t.image φ : Finset K) : Set K) := by
    intro a
    have ha : a ∈ Algebra.adjoin k (t : Set A) := ht ▸ Algebra.mem_top
    have : φ a ∈ (Algebra.adjoin k (t : Set A)).map φ := ⟨a, ha, rfl⟩
    rw [AlgHom.map_adjoin] at this
    apply IntermediateField.algebra_adjoin_le_adjoin
    simpa using this
  obtain ⟨a, s, hs, ha⟩ := hφ y
  have : y = φ a / φ s := by rw [ha, mul_div_cancel_right₀ _ hs]
  rw [this]
  exact div_mem (hmem a) (hmem s)

theorem a1d_finite_of_isAlgebraic {k L K : Type} [Field k] [Field L] [Field K] [Algebra k L]
    [Algebra k K] [Algebra L K] [IsScalarTower k L K] [Algebra.EssFiniteType k K]
    [Algebra.IsAlgebraic L K] : Module.Finite L K := by
  have : Algebra.EssFiniteType L K := Algebra.EssFiniteType.of_comp k L K
  obtain ⟨t, ht⟩ := IntermediateField.fg_top L K
  have : FiniteDimensional L (IntermediateField.adjoin L (t : Set K)) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  rw [ht] at this
  exact Module.Finite.equiv IntermediateField.topEquiv.toLinearEquiv

theorem a1d_evaluation_ker {X : Scheme} {U : X.Opens} (hU : IsAffineOpen U) (x : X)
    (hx : x ∈ U) :
    RingHom.ker (X.evaluation U x hx).hom = (hU.primeIdealOf ⟨x, hx⟩).asIdeal ∧
      ∀ y : X.residueField x, ∃ a s : Γ(X, U), X.evaluation U x hx s ≠ 0 ∧
        X.evaluation U x hx a = y * X.evaluation U x hx s := by
  let : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hx⟩
  have hloc := hU.isLocalization_stalk ⟨x, hx⟩
  have hev : ∀ a, X.evaluation U x hx a =
      X.residue x (algebraMap Γ(X, U) (X.presheaf.stalk x) a) := fun a => rfl
  constructor
  · ext a
    rw [RingHom.mem_ker]
    change IsLocalRing.residue _ (algebraMap Γ(X, U) (X.presheaf.stalk x) a) = 0 ↔ _
    rw [IsLocalRing.residue_eq_zero_iff]
    exact IsLocalization.AtPrime.to_map_mem_maximal_iff _ _ a
  · intro y
    obtain ⟨t, rfl⟩ := X.residue_surjective x y
    obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.mk'_surjective
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl t
    refine ⟨a, s, ?_, ?_⟩
    · rw [hev]
      change IsLocalRing.residue _ (algebraMap Γ(X, U) (X.presheaf.stalk x) s) ≠ 0
      rw [Ne, IsLocalRing.residue_eq_zero_iff, IsLocalization.AtPrime.to_map_mem_maximal_iff _ (hU.primeIdealOf ⟨x, hx⟩).asIdeal]
      exact s.2
    · rw [hev, hev, ← map_mul, ← hs, IsLocalization.mk'_spec]

/-- The global evaluation `Γ(X, ⊤) → κ(x)` factors through the restriction to `U`. -/
theorem a1d_appLE_evaluation {X : Over (Spec (CommRingCat.of ℂ))} (U : X.left.Opens) (x : X.left)
    (hx : x ∈ U) (e) :
    X.hom.appLE ⊤ U e ≫ X.left.evaluation U x hx = X.hom.appTop ≫ X.left.Γevaluation x := by
  rw [Scheme.Hom.appLE, ← Scheme.germ_residue, Category.assoc,
    ← Category.assoc (X.left.presheaf.map _), TopCat.Presheaf.germ_res]
  rfl

/-- On an affine chart of a scheme locally of finite type over `ℂ`, the height of a point is a
natural number equal to the transcendence degree of its residue field. -/
theorem a1d_height_chart {X : Over (Spec (CommRingCat.of ℂ))} [LocallyOfFiniteType X.hom]
    (x : X.left) (U : X.left.Opens) (hU : IsAffineOpen U) (q : Spec Γ(X.left, U))
    (hq : hU.fromSpec q = x) :
    letI : Algebra ℂ (X.left.residueField x) :=
      ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ X.hom.appTop ≫ X.left.Γevaluation x).hom.toAlgebra
    Algebra.EssFiniteType ℂ (X.left.residueField x) ∧
      ∃ n : ℕ, Order.height q = n ∧ Algebra.trdeg ℂ (X.left.residueField x) = n := by
  have hx : x ∈ U := by
    change x ∈ (U : Set X.left); rw [← hU.range_fromSpec]; exact ⟨q, hq⟩
  have hq' : q = hU.primeIdealOf ⟨x, hx⟩ :=
    hU.fromSpec.isOpenEmbedding.injective (hq.trans (hU.fromSpec_primeIdealOf ⟨x, hx⟩).symm)
  subst hq'
  let : Algebra ℂ (X.left.residueField x) :=
    ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ X.hom.appTop ≫ X.left.Γevaluation x).hom.toAlgebra
  have e : U ≤ X.hom ⁻¹ᵁ ⊤ := by simp
  let : Algebra ℂ Γ(X.left, U) :=
    ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ X.hom.appLE ⊤ U e).hom.toAlgebra
  have : Algebra.FiniteType ℂ Γ(X.left, U) := by
    refine RingHom.finiteType_algebraMap.mp ?_
    change ((X.hom.appLE ⊤ U e).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom).FiniteType
    refine RingHom.FiniteType.comp ?_ ?_
    · exact HasRingHomProperty.appLE (P := @LocallyOfFiniteType) X.hom ‹_›
        ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ e
    · exact RingHom.FiniteType.of_surjective _
        ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv).2)
  let φ : Γ(X.left, U) →ₐ[ℂ] X.left.residueField x :=
    { (X.left.evaluation U x hx).hom with
      commutes' := fun c => by
        change (((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ X.hom.appLE ⊤ U e) ≫
          X.left.evaluation U x hx) c = _
        rw [Category.assoc, a1d_appLE_evaluation]
        rfl }
  obtain ⟨hker, hφ⟩ := a1d_evaluation_ker hU x hx
  obtain ⟨n, hdim, htr⟩ := a1d_trdeg_eq_of_eval φ hφ
  refine ⟨a1d_fg_of_eval φ hφ, n, ?_, htr⟩
  have h := hc9k8_height_spec Γ(X.left, U) (hU.primeIdealOf ⟨x, hx⟩)
  have hk : RingHom.ker φ = (hU.primeIdealOf ⟨x, hx⟩).asIdeal := hker
  rw [← hk, hdim] at h
  exact_mod_cast h

/-- For a scheme locally of finite type over `ℂ`, the height of a point in the specialization order
(the dimension of `closure {x}`) is the transcendence degree of `κ(x)` over `ℂ`.
Source: Hartshorne, *Algebraic Geometry*, Exercise II.3.20. -/
theorem a1d_height_eq_trdeg {X : Over (Spec (CommRingCat.of ℂ))} [LocallyOfFiniteType X.hom]
    (x : X.left) :
    letI : Algebra ℂ (X.left.residueField x) :=
      ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ X.hom.appTop ≫ X.left.Γevaluation x).hom.toAlgebra
    Algebra.EssFiniteType ℂ (X.left.residueField x) ∧
      ∃ n : ℕ, Order.height x = n ∧ Algebra.trdeg ℂ (X.left.residueField x) = n := by
  let : Algebra ℂ (X.left.residueField x) :=
    ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ X.hom.appTop ≫ X.left.Γevaluation x).hom.toAlgebra
  obtain ⟨U, hU', hxU, -⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ (⊤ : X.left.Opens) from trivial)
  obtain ⟨hfg, n, hn, htr⟩ := a1d_height_chart x U hU' (hU'.primeIdealOf ⟨x, hxU⟩)
    (hU'.fromSpec_primeIdealOf ⟨x, hxU⟩)
  refine ⟨hfg, n, le_antisymm ?_ ?_, htr⟩
  · refine hc9k8_height_le_of_upperSets _ _ fun z _ => ?_
    obtain ⟨V, hV', hzV, -⟩ := exists_isAffineOpen_mem_and_subset
      (show z ∈ (⊤ : X.left.Opens) from trivial)
    refine ⟨Set.range hV'.fromSpec,
      hc9k8_isUpperSet_of_isOpen _ hV'.fromSpec.isOpenEmbedding.isOpen_range,
      by rw [hV'.range_fromSpec]; exact hzV, fun hy => ?_⟩
    obtain ⟨q, hq⟩ := hy
    have e : (⟨x, ⟨q, hq⟩⟩ : Set.range hV'.fromSpec) = hc9k8_rangeOrderIso hV'.fromSpec q :=
      Subtype.ext hq.symm
    rw [e, Order.height_orderIso]
    obtain ⟨-, m, hm, htr'⟩ := a1d_height_chart x V hV' q hq
    have hmn : m = n := by
      have := htr'.symm.trans htr
      exact_mod_cast this
    rw [hm, hmn]
  · let p : Spec Γ(X.left, U) := hU'.primeIdealOf ⟨x, hxU⟩
    have hpx : hU'.fromSpec p = x := hU'.fromSpec_primeIdealOf ⟨x, hxU⟩
    have h1 : Order.height p ≤ Order.height (hU'.fromSpec p) :=
      calc Order.height p = Order.height (hc9k8_rangeOrderIso hU'.fromSpec p) :=
            (Order.height_orderIso _ _).symm
        _ ≤ _ := hc9k8_height_subtype_le _ _
    rw [hpx, hn] at h1
    exact h1

/-- Over `ℂ`, for schemes locally of finite type, the degree of `f` at `x` is positive exactly
when the dimension of `closure {x}` does not drop under `f`.
Source: Fulton, *Intersection Theory*, second edition, §1.4; Hartshorne, *Algebraic Geometry*,
Exercise II.3.20. -/
theorem a1d_degree_pos_iff {X Y : Over (Spec (CommRingCat.of ℂ))} (f : X ⟶ Y)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] (x : X.left) :
    0 < a1p_degree f.left x ↔ Order.height (f.left x) = Order.height x := by
  let : Algebra ℂ (X.left.residueField x) :=
    ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ X.hom.appTop ≫ X.left.Γevaluation x).hom.toAlgebra
  let : Algebra ℂ (Y.left.residueField (f.left x)) :=
    ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ Y.hom.appTop ≫
      Y.left.Γevaluation (f.left x)).hom.toAlgebra
  let : Algebra (Y.left.residueField (f.left x)) (X.left.residueField x) :=
    (f.left.residueFieldMap x).hom.toAlgebra
  have : IsScalarTower ℂ (Y.left.residueField (f.left x)) (X.left.residueField x) := by
    refine IsScalarTower.of_algebraMap_eq fun c => ?_
    change _ = f.left.residueFieldMap x (Y.left.Γevaluation (f.left x) (Y.hom.appTop _))
    rw [Scheme.Γevaluation_naturality_apply]
    change _ = X.left.Γevaluation x ((Y.hom.appTop ≫ f.left.appTop) _)
    rw [← Scheme.Hom.comp_appTop, Over.w f]
    rfl
  obtain ⟨hfg, n, hn, htr⟩ := a1d_height_eq_trdeg x
  obtain ⟨-, m, hm, htr'⟩ := a1d_height_eq_trdeg (f.left x)
  have hadd := trdeg_add_eq ℂ (Y.left.residueField (f.left x)) (A := X.left.residueField x)
  rw [htr, htr'] at hadd
  rw [hn, hm, Nat.cast_inj]
  have key : 0 < a1p_degree f.left x ↔
      Algebra.IsAlgebraic (Y.left.residueField (f.left x)) (X.left.residueField x) := by
    change 0 < Module.finrank (Y.left.residueField (f.left x)) (X.left.residueField x) ↔ _
    constructor
    · intro h
      have := Module.finite_of_finrank_pos h
      exact Algebra.IsAlgebraic.of_finite _ _
    · intro h
      have := a1d_finite_of_isAlgebraic (k := ℂ) (L := Y.left.residueField (f.left x))
        (K := X.left.residueField x)
      exact Module.finrank_pos
  rw [key, ← trdeg_eq_zero_iff]
  constructor
  · intro h0
    rw [h0, add_zero] at hadd
    exact_mod_cast hadd
  · intro hmn
    subst hmn
    have hlt : Algebra.trdeg (Y.left.residueField (f.left x)) (X.left.residueField x) <
        Cardinal.aleph0 :=
      lt_of_le_of_lt (le_add_self.trans hadd.le) (Cardinal.natCast_lt_aleph0 (n := m))
    obtain ⟨t, ht⟩ := Cardinal.lt_aleph0.mp hlt
    rw [ht] at hadd ⊢
    have : m + t = m := by exact_mod_cast hadd
    have : t = 0 := by omega
    simp [this]

end HodgeLean.Adapters
