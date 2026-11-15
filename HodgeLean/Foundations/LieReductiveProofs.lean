import Mathlib.Algebra.Lie.LieTheorem
import Mathlib.Algebra.Lie.Semisimple.Basic
import Mathlib.Algebra.Lie.BaseChange
import Mathlib.RingTheory.Artinian.Module
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Proof obligations for complete reducibility of linear Lie algebras -/

noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing

namespace HodgeLean.Foundations

open LieAlgebra

/-- The trace pairing of a faithful finite-dimensional representation of a
semisimple algebra separates points in characteristic zero. -/
theorem pol2_trace_separates
    {K B V : Type*} [Field K] [CharZero K] [Ring B] [Algebra K B]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [IsSemisimpleRing B] (ρ : B →ₐ[K] Module.End K V)
    (hρ : Function.Injective ρ) (x : B)
    (hx : ∀ y : B, LinearMap.trace K V (ρ (y * x)) = 0) : x = 0 := by
  let I : Ideal B :=
    { carrier := {z | ∀ y : B, LinearMap.trace K V (ρ (y * z)) = 0}
      zero_mem' := by intro y; simp only [mul_zero, map_zero]
      add_mem' := by
        intro a b ha hb y
        simp only [mul_add, map_add, ha y, hb y, add_zero]
      smul_mem' := by
        intro a b hb y
        exact (mul_assoc y a b) ▸ hb (y * a) }
  obtain ⟨e, he, hI⟩ := IsSemisimpleRing.ideal_eq_span_idempotent I
  have heI : e ∈ I := hI ▸ Ideal.subset_span (Set.mem_singleton e)
  have hetr : LinearMap.trace K V (ρ e) = 0 := by
    simpa only [one_mul] using heI 1
  have hezero : e = 0 := hρ <| by
    simpa only [map_zero] using
      LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero (he.map ρ) hetr
  have hIx : x ∈ I := hx
  rw [hI, hezero, Ideal.span_singleton_eq_bot.mpr rfl] at hIx
  exact hIx

/-- A separating representation trace pairing detects semisimplicity of a
finite-dimensional associative algebra. -/
theorem pol2_semisimple_of_trace_separates
    {K B V : Type*} [Field K] [Ring B] [Algebra K B]
    [FiniteDimensional K B] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (ρ : B →ₐ[K] Module.End K V)
    (hsep : ∀ x : B, (∀ y : B, LinearMap.trace K V (ρ (y * x)) = 0) → x = 0) :
    IsSemisimpleRing B := by
  letI : IsArtinianRing B := isArtinian_of_tower K (inferInstance : IsArtinian K B)
  apply IsArtinianRing.isSemisimpleRing_iff_jacobson.mpr
  apply le_antisymm _ bot_le
  intro x hx
  change x = 0
  apply hsep x
  intro y
  have hy : y * x ∈ Ring.jacobson B := (Ring.jacobson B).mul_mem_left y hx
  obtain ⟨n, hn⟩ := IsSemiprimaryRing.isNilpotent (R := B)
  have hpow : (y * x) ^ n = 0 := by
    have := Ideal.pow_mem_pow hy n
    rwa [hn, Ideal.zero_eq_bot, Submodule.mem_bot] at this
  exact (LinearMap.isNilpotent_trace_of_isNilpotent
    (show IsNilpotent (ρ (y * x)) from ⟨n, by rw [← map_pow, hpow, map_zero]⟩)).eq_zero

/-- Scalar extension of an associative algebra representation. -/
def pol2_baseChangeRepresentation
    {K A B V : Type*} [Field K] [Field A] [Algebra K A]
    [Ring B] [Algebra K B] [AddCommGroup V] [Module K V]
    (ρ : B →ₐ[K] Module.End K V) :
    TensorProduct K A B →ₐ[A] Module.End A (TensorProduct K A V) :=
  AlgHom.liftEquiv K A B _ ((Module.End.baseChangeHom K A V).comp ρ)

/-- Trace on pure tensors in the extended representation. -/
theorem pol2_trace_baseChange_tmul
    {K A B V : Type*} [Field K] [Field A] [Algebra K A]
    [Ring B] [Algebra K B] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (ρ : B →ₐ[K] Module.End K V) (a : A) (b : B) :
    LinearMap.trace A _ (pol2_baseChangeRepresentation ρ (TensorProduct.tmul K a b)) =
      a * algebraMap K A (LinearMap.trace K V (ρ b)) := by
  change LinearMap.trace A _ (a • (ρ b).baseChange A) = _
  rw [map_smul, LinearMap.trace_baseChange, smul_eq_mul]

/-- Trace separation is preserved by an arbitrary extension of the ground field. -/
theorem pol2_trace_separates_baseChange
    {K A B V : Type*} [Field K] [Field A] [Algebra K A]
    [Ring B] [Algebra K B] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (ρ : B →ₐ[K] Module.End K V)
    (hsep : ∀ x : B, (∀ y : B, LinearMap.trace K V (ρ (y * x)) = 0) → x = 0)
    (x : TensorProduct K A B)
    (hx : ∀ y, LinearMap.trace A _ (pol2_baseChangeRepresentation ρ (y * x)) = 0) :
    x = 0 := by
  classical
  let b := Module.Free.chooseBasis K A
  obtain ⟨c, rfl⟩ := TensorProduct.eq_repr_basis_left b x
  have hc : ∀ i, c i = 0 := by
    intro i
    by_cases hi : i ∈ c.support
    · apply hsep
      intro y
      have h := hx (TensorProduct.tmul K (1 : A) y)
      simp only [Finsupp.sum, Finset.mul_sum, Algebra.TensorProduct.tmul_mul_tmul,
        one_mul, map_sum, pol2_trace_baseChange_tmul] at h
      have hcoord := congrArg (fun z : A => b.repr z i) h
      simp only [← Algebra.smul_def, mul_comm (b _) _, ← Algebra.smul_def,
        map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply,
        Finsupp.coe_smul, Pi.smul_apply, Module.Basis.repr_self, Finsupp.single_apply,
        smul_eq_mul, mul_ite, mul_one, mul_zero, map_zero, Finsupp.zero_apply] at hcoord
      simpa only [Finset.sum_ite_eq', hi, ite_true] using hcoord
    · rw [Finsupp.notMem_support_iff.mp hi]
  have : c = 0 := Finsupp.ext hc
  simp only [this, Finsupp.sum_zero_index]

/-- A finite-dimensional faithful semisimple module makes its acting
subalgebra semisimple. -/
theorem pol2_semisimple_subalgebra
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (B : Subalgebra K (Module.End K V))
    [IsSemisimpleModule B V] : IsSemisimpleRing B := by
  let b := Module.finBasis K V
  let f : B →ₗ[B] (Fin (Module.finrank K V) → V) :=
    LinearMap.pi fun i => LinearMap.toSpanSingleton B V (b i)
  apply IsSemisimpleModule.of_injective f
  intro x y h
  apply Subtype.ext
  apply b.ext
  intro i
  exact congrFun h i

/-- A Lie-stable subspace is stable under the associative algebra generated
by the Lie algebra. -/
def pol2_associativeSubmodule
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (L : LieSubalgebra K (Module.End K V)) (W : LieSubmodule K L V) :
    Submodule (Algebra.adjoin K (L : Set (Module.End K V))) V where
  carrier := W
  zero_mem' := W.zero_mem
  add_mem' := W.add_mem
  smul_mem' := by
    rintro ⟨a, ha₀⟩ v hv
    change a v ∈ W
    have ha : ∀ v ∈ W, a v ∈ W := by
      induction ha₀ using Algebra.adjoin_induction with
      | mem x hx => exact fun v hv => W.lie_mem (x := ⟨x, hx⟩) hv
      | algebraMap r => exact fun v hv => W.smul_mem r hv
      | add x y hx hy ihx ihy => exact fun v hv => W.add_mem (ihx v hv) (ihy v hv)
      | mul x y hx hy ihx ihy => exact fun v hv => ihx (y v) (ihy v hv)
    exact ha v hv

/-- Stable complements for the Lie action give semisimplicity for its
generated associative algebra action. -/
theorem pol2_semisimple_adjoin
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (L : LieSubalgebra K (Module.End K V))
    (hcomp : ∀ W : LieSubmodule K L V, ∃ W' : LieSubmodule K L V,
      IsCompl (W : Submodule K V) (W' : Submodule K V)) :
    IsSemisimpleRing (Algebra.adjoin K (L : Set (Module.End K V))) := by
  let B := Algebra.adjoin K (L : Set (Module.End K V))
  have : IsSemisimpleModule B V := by
    apply (isSemisimpleModule_iff B V).mpr
    refine ⟨fun W => ?_⟩
    let N : LieSubmodule K L V :=
      { W.restrictScalars K with
        lie_mem := by
          intro x v hv
          exact W.smul_mem (⟨x, Algebra.subset_adjoin x.property⟩ : B) hv }
    obtain ⟨N', hN'⟩ := hcomp N
    refine ⟨pol2_associativeSubmodule L N', ?_⟩
    exact (Submodule.isCompl_restrictScalars_iff K).mp hN'
  exact pol2_semisimple_subalgebra B

theorem pol2_stable_complements_baseChange_aux
    {K A V : Type*} [Field K] [Field A] [Algebra K A] [IsScalarTower K A A]
    [CharZero K] [IsAlgClosed A] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (L : LieSubalgebra K (Module.End K V))
    (hcomp : ∀ W : LieSubmodule K L V, ∃ W' : LieSubmodule K L V,
      IsCompl (W : Submodule K V) (W' : Submodule K V)) :
    ∀ W : LieSubmodule A (TensorProduct K A L) (TensorProduct K A V),
      ∃ W' : LieSubmodule A (TensorProduct K A L) (TensorProduct K A V),
        IsCompl (W : Submodule A (TensorProduct K A V))
          (W' : Submodule A (TensorProduct K A V)) := by
  classical
  let B := Algebra.adjoin K (L : Set (Module.End K V))
  let M := TensorProduct K A V
  let C := TensorProduct K A B
  let ρ : C →ₐ[A] Module.End A M := pol2_baseChangeRepresentation B.val
  have : IsSemisimpleRing B := pol2_semisimple_adjoin L hcomp
  have : IsSemisimpleRing C := pol2_semisimple_of_trace_separates ρ
    (pol2_trace_separates_baseChange B.val
      (pol2_trace_separates B.val Subtype.val_injective))
  letI : Module C M := Module.compHom M ρ.toRingHom
  have : IsScalarTower A C M := IsScalarTower.of_algebraMap_smul fun a v => by
    change ρ (algebraMap A C a) v = a • v
    rw [ρ.commutes]
    rfl
  have hact (a : A) (x : L) (v : M) :
      ρ (TensorProduct.tmul K a (⟨x, Algebra.subset_adjoin x.property⟩ : B)) v =
        ⁅TensorProduct.tmul K a x, v⁆ := by
    induction v using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact (lie_zero _).symm
    | tmul b v => rfl
    | add v w hv hw => rw [map_add, hv, hw]; exact (lie_add _ _ _).symm
  intro W
  have hstable (b : B) : ∀ v ∈ W, (b : Module.End K V).baseChange A v ∈ W := by
    rcases b with ⟨b, hb⟩
    induction hb using Algebra.adjoin_induction with
    | mem x hx =>
      intro v hv
      have h := W.lie_mem (x := TensorProduct.tmul K (1 : A) (⟨x, hx⟩ : L)) hv
      rw [← hact] at h
      change (1 : A) • x.baseChange A v ∈ W at h
      simpa only [one_smul] using h
    | algebraMap r =>
      intro v hv
      change ((Module.End.baseChangeHom K A V) (algebraMap K (Module.End K V) r)) v ∈ W
      rw [AlgHom.commutes, IsScalarTower.algebraMap_eq K A (Module.End A M)]
      exact W.smul_mem (algebraMap K A r) hv
    | add x y hx hy ihx ihy =>
      intro v hv
      rw [LinearMap.baseChange_add, LinearMap.add_apply]
      exact W.add_mem (ihx v hv) (ihy v hv)
    | mul x y hx hy ihx ihy =>
      intro v hv
      rw [LinearMap.baseChange_mul, Module.End.mul_apply]
      exact ihx _ (ihy v hv)
  let N : Submodule C M :=
    { carrier := W
      zero_mem' := W.zero_mem
      add_mem' := W.add_mem
      smul_mem' := by
        intro c v hv
        change ρ c v ∈ W
        induction c using TensorProduct.induction_on with
        | zero => simp only [map_zero, LinearMap.zero_apply, W.zero_mem]
        | tmul a b =>
          change a • (b : Module.End K V).baseChange A v ∈ W
          exact W.smul_mem a (hstable b v hv)
        | add c d hc hd =>
          rw [map_add, LinearMap.add_apply]
          exact W.add_mem hc hd }
  obtain ⟨N', hN'⟩ := exists_isCompl N
  let W' : LieSubmodule A (TensorProduct K A L) M :=
    { N'.restrictScalars A with
      lie_mem := by
        intro x v hv
        change ⁅x, v⁆ ∈ N'
        induction x using TensorProduct.induction_on with
        | zero => rw [zero_lie]; exact N'.zero_mem
        | tmul a x =>
          rw [← hact]
          exact N'.smul_mem (TensorProduct.tmul K a
            (⟨x, Algebra.subset_adjoin x.property⟩ : B)) hv
        | add x y hx hy =>
          rw [add_lie]
          exact N'.add_mem hx hy }
  exact ⟨W', (Submodule.isCompl_restrictScalars_iff A).mpr hN'⟩

theorem pol2_radical_acts_scalar_on_irreducible_aux
    {A V : Type*} [Field A] [CharZero A] [IsAlgClosed A]
    [AddCommGroup V] [Module A V] [FiniteDimensional A V]
    (L : LieSubalgebra A (Module.End A V))
    (hirr : ∀ W : Submodule A V,
      (∀ X ∈ L, W.map (X : Module.End A V) ≤ W) → W = ⊥ ∨ W = ⊤)
    (X : L) (hX : X ∈ radical A L) :
    ∃ a : A, (X : Module.End A V) = a • 1 := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · exact ⟨0, LinearMap.ext fun v => Subsingleton.elim _ _⟩
  obtain ⟨χ, hχ⟩ : ∃ χ : Module.Dual A (radical A L),
      Nontrivial (LieModule.weightSpace V χ) :=
    LieModule.exists_nontrivial_weightSpace_of_isSolvable A (radical A L) V
  let N : LieSubmodule A L V := LieModule.weightSpaceOfIsLieTower A V χ
  have hN : (N : Submodule A V) = ⊤ := by
    refine (hirr N fun Y hY => ?_).resolve_left ?_
    · rintro u ⟨v, hv, rfl⟩
      exact N.lie_mem (x := ⟨Y, hY⟩) hv
    · intro h
      have : Nontrivial N := hχ
      obtain ⟨⟨u, hu⟩, hu0⟩ := exists_ne (0 : N)
      have : u ∈ (⊥ : Submodule A V) := h ▸ hu
      exact hu0 (Subtype.ext ((Submodule.mem_bot A).mp this))
  refine ⟨χ ⟨X, hX⟩, LinearMap.ext fun v => ?_⟩
  have hv : v ∈ N := by
    change v ∈ (N : Submodule A V)
    rw [hN]
    exact Submodule.mem_top
  have hv' :=
    (LieModule.mem_weightSpace (L := radical A L) (R := A) χ v).mp hv ⟨X, hX⟩
  simpa using hv'

/-- A solvable ideal commutes on a module whose stable subspaces split. -/
theorem pol2_solvable_ideal_commutes
    {A L M : Type*} [Field A] [CharZero A] [IsAlgClosed A]
    [LieRing L] [LieAlgebra A L] [AddCommGroup M] [Module A M]
    [FiniteDimensional A M] [LieRingModule L M] [LieModule A L M]
    (I : LieIdeal A L) [IsSolvable I]
    (hc : ∀ W : LieSubmodule A L M, ∃ W' : LieSubmodule A L M,
      IsCompl (W : Submodule A M) (W' : Submodule A M))
    (x : I) (y : L) (v : M) : ⁅(x : L), ⁅y, v⁆⁆ = ⁅y, ⁅(x : L), v⁆⁆ := by
  classical
  let N : LieSubmodule A L M := ⨆ χ : Module.Dual A I,
    LieModule.weightSpaceOfIsLieTower A M χ
  obtain ⟨P, hP⟩ := hc N
  have hP0 : (P : Submodule A M) = ⊥ := by
    by_contra h
    have : Nontrivial P := (Submodule.nontrivial_iff_ne_bot).mpr h
    obtain ⟨χ, hχ⟩ := LieModule.exists_nontrivial_weightSpace_of_isSolvable A I P
    obtain ⟨⟨w, hw⟩, hw0⟩ := exists_ne (0 : LieModule.weightSpace P χ)
    have hwN : (w : M) ∈ N := by
      apply LieSubmodule.mem_iSup_of_mem χ
      change (w : M) ∈ LieModule.weightSpace M χ
      rw [LieModule.mem_weightSpace] at hw ⊢
      intro z
      exact congrArg Subtype.val (hw z)
    have hwz : (w : M) = 0 := (Submodule.disjoint_def.mp hP.disjoint) _ hwN w.property
    exact hw0 (Subtype.ext (Subtype.ext hwz))
  have hN : (N : Submodule A M) = ⊤ := by
    have := hP.sup_eq_top
    rwa [hP0, sup_bot_eq] at this
  let f : Module.End A M :=
    (LieModule.toEnd A L M (x : L)) * LieModule.toEnd A L M y -
      (LieModule.toEnd A L M y) * LieModule.toEnd A L M (x : L)
  have hker : (N : Submodule A M) ≤ LinearMap.ker f := by
    rw [LieSubmodule.iSup_toSubmodule]
    apply iSup_le
    intro χ w hw
    change ⁅(x : L), ⁅y, w⁆⁆ - ⁅y, ⁅(x : L), w⁆⁆ = 0
    have hw' := (LieModule.mem_weightSpace χ w).mp hw x
    have hyw := (LieModule.mem_weightSpace χ ⁅y, w⁆).mp
      ((LieModule.weightSpaceOfIsLieTower A M χ).lie_mem (x := y) hw) x
    change ⁅(x : L), w⁆ = χ x • w at hw'
    change ⁅(x : L), ⁅y, w⁆⁆ = χ x • ⁅y, w⁆ at hyw
    rw [hw', hyw, lie_smul, sub_self]
  have hv := hker (hN ▸ (Submodule.mem_top : v ∈ (⊤ : Submodule A M)))
  exact sub_eq_zero.mp hv

theorem pol2_radical_le_center_of_stable_complements_aux
    {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (L : LieSubalgebra K (Module.End K V))
    (hcomp : ∀ W : Submodule K V,
      (∀ A ∈ L, W.map (A : Module.End K V) ≤ W) →
      ∃ W' : Submodule K V,
        (∀ A ∈ L, W'.map (A : Module.End K V) ≤ W') ∧ IsCompl W W') :
    radical K L ≤ center K L := by
  let A := AlgebraicClosure K
  let T := TensorProduct K A L
  let M := TensorProduct K A V
  let I : LieIdeal A T := (radical K L).baseChange A
  have : IsSolvable I := by
    obtain ⟨n, hn⟩ := IsSolvable.solvable K (radical K L)
    apply IsSolvable.mk (R := A) (k := n)
    rw [LieIdeal.derivedSeries_eq_bot_iff]
    change derivedSeriesOfIdeal A T n ((radical K L).baseChange A) = ⊥
    rw [derivedSeriesOfIdeal_baseChange,
      (LieIdeal.derivedSeries_eq_bot_iff _ _).mp hn, LieSubmodule.baseChange_bot]
  have hc : ∀ W : LieSubmodule K L V, ∃ W' : LieSubmodule K L V,
      IsCompl (W : Submodule K V) (W' : Submodule K V) := by
    intro W
    obtain ⟨P, hP, hcompl⟩ := hcomp W (by
      rintro X hX u ⟨v, hv, rfl⟩
      exact W.lie_mem (x := ⟨X, hX⟩) hv)
    let P' : LieSubmodule K L V :=
      { toSubmodule := P
        lie_mem := by
          intro x v hv
          exact hP x x.property ⟨v, hv, rfl⟩ }
    exact ⟨P', hcompl⟩
  intro x hx
  rw [LieModule.mem_maxTrivSubmodule]
  intro y
  apply Subtype.ext
  apply LinearMap.ext
  intro v
  have h := pol2_solvable_ideal_commutes I
    (pol2_stable_complements_baseChange_aux L hc)
    ⟨TensorProduct.tmul K (1 : A) x,
      LieSubmodule.tmul_mem_baseChange_of_mem 1 hx⟩
    (TensorProduct.tmul K (1 : A) y) (TensorProduct.tmul K (1 : A) v)
  have h' : TensorProduct.tmul K (1 : A) ((x : Module.End K V) ((y : Module.End K V) v)) =
      TensorProduct.tmul K (1 : A) ((y : Module.End K V) ((x : Module.End K V) v)) := by
    change ⁅TensorProduct.tmul K (1 : A) x, ⁅TensorProduct.tmul K (1 : A) y, TensorProduct.tmul K (1 : A) v⁆⁆ =
      ⁅TensorProduct.tmul K (1 : A) y, ⁅TensorProduct.tmul K (1 : A) x, TensorProduct.tmul K (1 : A) v⁆⁆ at h
    simpa only [LieAlgebra.ExtendScalars.bracket_tmul, one_mul, LieSubalgebra.coe_bracket_of_module, Module.End.lie_apply] using h
  have hz : (x : Module.End K V) ((y : Module.End K V) v) = (y : Module.End K V) ((x : Module.End K V) v) :=
    sub_eq_zero.mp ((Module.FaithfullyFlat.one_tmul_eq_zero_iff K V (A := A) _).mp
      (by rw [TensorProduct.tmul_sub, h', sub_self]))
  change (y : Module.End K V) ((x : Module.End K V) v) - (x : Module.End K V) ((y : Module.End K V) v) = 0
  exact sub_eq_zero.mpr hz.symm


theorem pol2_radical_eq_center_of_le_aux
    {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
    [FiniteDimensional K L] (h : radical K L ≤ center K L) :
    radical K L = center K L := by
  exact le_antisymm h (center_le_radical K L)

theorem pol2_radical_eq_center_of_stable_complements_aux
    {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (L : LieSubalgebra K (Module.End K V))
    (hcomp : ∀ W : Submodule K V,
      (∀ A ∈ L, W.map (A : Module.End K V) ≤ W) →
      ∃ W' : Submodule K V,
        (∀ A ∈ L, W'.map (A : Module.End K V) ≤ W') ∧ IsCompl W W') :
    radical K L = center K L := by
  apply pol2_radical_eq_center_of_le_aux
  exact pol2_radical_le_center_of_stable_complements_aux L hcomp

/-- A submodule bound on one derived term propagates through a bracket bound. -/
theorem pol2_derived_step
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    (n : ℕ) (P Q : Submodule K L)
    (hP : (derivedSeries K L n : Submodule K L) ≤ P)
    (hQ : ∀ x ∈ P, ∀ y ∈ P, ⁅x, y⁆ ∈ Q) :
    (derivedSeries K L (n + 1) : Submodule K L) ≤ Q := by
  change (derivedSeriesOfIdeal K L (n + 1) ⊤).toSubmodule ≤ Q
  rw [derivedSeriesOfIdeal_succ, LieSubmodule.lieIdeal_oper_eq_linear_span']
  apply Submodule.span_le.mpr
  rintro z ⟨x, hx, y, hy, rfl⟩
  exact hQ x (hP hx) y (hP hy)

theorem pol2_exists_upperTriangular_nonreductive_aux :
    ∃ L : LieSubalgebra ℚ (Module.End ℚ (Fin 2 → ℚ)),
      radical ℚ L ≠ center ℚ L ∧
      ¬(∀ W : Submodule ℚ (Fin 2 → ℚ),
        (∀ A ∈ L, W.map (A : Module.End ℚ (Fin 2 → ℚ)) ≤ W) →
        ∃ W' : Submodule ℚ (Fin 2 → ℚ),
          (∀ A ∈ L, W'.map (A : Module.End ℚ (Fin 2 → ℚ)) ≤ W') ∧ IsCompl W W') := by
  let U : LieSubalgebra ℚ (Matrix (Fin 2) (Fin 2) ℚ) :=
    { carrier := {a | a 1 0 = 0}
      zero_mem' := rfl
      add_mem' := by intro a b ha hb; change a 1 0 + b 1 0 = 0; rw [ha, hb, add_zero]
      smul_mem' := by intro r a ha; change r * a 1 0 = 0; rw [ha, mul_zero]
      lie_mem' := by
        intro a b ha hb
        change a 1 0 = 0 at ha
        change b 1 0 = 0 at hb
        change (a * b - b * a) 1 0 = 0
        simp [Matrix.mul_apply, Fin.sum_univ_two, ha, hb] }
  let P : Submodule ℚ U :=
    { carrier := {a | (a : Matrix (Fin 2) (Fin 2) ℚ) 0 0 = 0 ∧
        (a : Matrix (Fin 2) (Fin 2) ℚ) 1 1 = 0}
      zero_mem' := ⟨rfl, rfl⟩
      add_mem' := by
        intro a b ha hb
        exact ⟨by change a.val 0 0 + b.val 0 0 = 0; rw [ha.1, hb.1, add_zero],
          by change a.val 1 1 + b.val 1 1 = 0; rw [ha.2, hb.2, add_zero]⟩
      smul_mem' := by
        intro r a ha
        exact ⟨by change r * a.val 0 0 = 0; rw [ha.1, mul_zero],
          by change r * a.val 1 1 = 0; rw [ha.2, mul_zero]⟩ }
  have h1 : (derivedSeries ℚ U 1 : Submodule ℚ U) ≤ P := by
    apply pol2_derived_step 0 ⊤ P le_top
    intro a ha b hb
    change (a.val * b.val - b.val * a.val) 0 0 = 0 ∧
      (a.val * b.val - b.val * a.val) 1 1 = 0
    have ha' : a.val 1 0 = 0 := a.property
    have hb' : b.val 1 0 = 0 := b.property
    simp [Matrix.mul_apply, Fin.sum_univ_two, ha', hb', mul_comm]
  have h2 : (derivedSeries ℚ U 2 : Submodule ℚ U) ≤ ⊥ := by
    apply pol2_derived_step 1 P ⊥ h1
    intro a ha b hb
    apply Subtype.ext
    have ha' : a.val 1 0 = 0 := a.property
    have hb' : b.val 1 0 = 0 := b.property
    change a.val * b.val - b.val * a.val = 0
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ha.1, ha.2, hb.1, hb.2, ha', hb']
  have : IsSolvable U := IsSolvable.mk (R := ℚ) (le_antisymm h2 bot_le)
  let e := (Matrix.toLinAlgEquiv' (R := ℚ) (n := Fin 2)).toLieEquiv
  let L := U.map e.toLieHom
  let f : U ≃ₗ⁅ℚ⁆ L := U.equivMapOfInjective e.toLieHom e.injective
  have : IsSolvable L := (solvable_iff_equiv_solvable f).mp inferInstance
  have hne : radical ℚ L ≠ center ℚ L := by
    intro h
    have : IsLieAbelian L := (isLieAbelian_iff_center_eq_top ℚ L).mpr
      (h.symm.trans (radical_eq_top_of_isSolvable ℚ L))
    have : IsLieAbelian U := (lie_abelian_iff_equiv_lie_abelian f).mpr inferInstance
    let a : U := ⟨!![1, 0; 0, 0], rfl⟩
    let b : U := ⟨!![0, 1; 0, 0], rfl⟩
    have hz := congrArg (fun z : U => z.val 0 1) (trivial_lie_zero U U a b)
    norm_num [a, b, LieSubalgebra.coe_bracket, Ring.lie_def,
      Matrix.mul_apply, Fin.sum_univ_two] at hz
  refine ⟨L, hne, ?_⟩
  intro hc
  exact hne (pol2_radical_eq_center_of_stable_complements_aux L hc)


theorem pol2_gl2_charTwo_counterexample_aux :
    (∀ W : Submodule (ZMod 2) (Fin 2 → ZMod 2),
      (∀ A ∈ (⊤ : LieSubalgebra (ZMod 2)
          (Module.End (ZMod 2) (Fin 2 → ZMod 2))),
        W.map (A : Module.End (ZMod 2) (Fin 2 → ZMod 2)) ≤ W) →
      ∃ W' : Submodule (ZMod 2) (Fin 2 → ZMod 2),
        (∀ A ∈ (⊤ : LieSubalgebra (ZMod 2)
            (Module.End (ZMod 2) (Fin 2 → ZMod 2))),
          W'.map (A : Module.End (ZMod 2) (Fin 2 → ZMod 2)) ≤ W') ∧ IsCompl W W') ∧
    radical (ZMod 2) (⊤ :
      LieSubalgebra (ZMod 2) (Module.End (ZMod 2) (Fin 2 → ZMod 2))) ≠
    center (ZMod 2) (⊤ :
      LieSubalgebra (ZMod 2) (Module.End (ZMod 2) (Fin 2 → ZMod 2))) := by
  constructor
  · classical
    intro W hW
    by_cases hbot : W = ⊥
    · subst W
      exact ⟨⊤, fun _ _ => le_top, isCompl_bot_top⟩
    have htop : W = ⊤ := by
      obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
      obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
        by_contra h
        exact hw0 (funext fun i => by simpa using not_exists.mp h i)
      apply top_unique
      intro v hv
      let f : Module.End (ZMod 2) (Fin 2 → ZMod 2) :=
        (w i)⁻¹ • ((LinearMap.toSpanSingleton (ZMod 2) _ v).comp (LinearMap.proj i))
      have hf : f w = v := by
        change (w i)⁻¹ • (w i • v) = v
        rw [smul_smul, inv_mul_cancel₀ hi, one_smul]
      exact hW f (LieSubalgebra.mem_top _) ⟨w, hw, hf⟩
    subst W
    refine ⟨⊥, ?_, isCompl_top_bot⟩
    intro f hf
    simp only [Submodule.map_bot, le_refl]
  · let B := Matrix (Fin 2) (Fin 2) (ZMod 2)
    let P : Submodule (ZMod 2) B :=
      { carrier := {a | a 0 0 + a 1 1 = 0}
        zero_mem' := by change (0 : ZMod 2) + 0 = 0; exact add_zero _
        add_mem' := by
          intro a b ha hb
          change (a 0 0 + b 0 0) + (a 1 1 + b 1 1) = 0
          change a 0 0 + a 1 1 = 0 at ha
          change b 0 0 + b 1 1 = 0 at hb
          linear_combination ha + hb
        smul_mem' := by
          intro r a ha
          change r * a 0 0 + r * a 1 1 = 0
          rw [← mul_add, ha, mul_zero] }
    let Q : Submodule (ZMod 2) B :=
      { carrier := {a | a 0 0 = a 1 1 ∧ a 0 1 = 0 ∧ a 1 0 = 0}
        zero_mem' := ⟨rfl, rfl, rfl⟩
        add_mem' := by
          intro a b ha hb
          exact ⟨congrArg₂ (· + ·) ha.1 hb.1,
            by change a 0 1 + b 0 1 = 0; rw [ha.2.1, hb.2.1, add_zero],
            by change a 1 0 + b 1 0 = 0; rw [ha.2.2, hb.2.2, add_zero]⟩
        smul_mem' := by
          intro r a ha
          exact ⟨congrArg (r * ·) ha.1,
            by change r * a 0 1 = 0; rw [ha.2.1, mul_zero],
            by change r * a 1 0 = 0; rw [ha.2.2, mul_zero]⟩ }
    have h1 : (derivedSeries (ZMod 2) B 1 : Submodule (ZMod 2) B) ≤ P := by
      apply pol2_derived_step 0 ⊤ P le_top
      intro a ha b hb
      change (a * b - b * a) 0 0 + (a * b - b * a) 1 1 = 0
      dsimp [B] at a b ⊢
      simp only [Matrix.mul_apply, Fin.sum_univ_two]
      ring
    have h2 : (derivedSeries (ZMod 2) B 2 : Submodule (ZMod 2) B) ≤ Q := by
      apply pol2_derived_step 1 P Q h1
      have h : ∀ a b : Matrix (Fin 2) (Fin 2) (ZMod 2),
          a 0 0 + a 1 1 = 0 → b 0 0 + b 1 1 = 0 →
          (a * b - b * a) 0 0 = (a * b - b * a) 1 1 ∧
          (a * b - b * a) 0 1 = 0 ∧ (a * b - b * a) 1 0 = 0 := by decide
      intro a ha b hb
      exact h a b ha hb
    have h3 : (derivedSeries (ZMod 2) B 3 : Submodule (ZMod 2) B) ≤ ⊥ := by
      apply pol2_derived_step 2 Q ⊥ h2
      intro a ha b hb
      change a * b - b * a = 0
      dsimp [B] at a b ⊢
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, ha.2.1, ha.2.2, hb.2.1, hb.2.2,
          mul_comm] <;> rfl
    have : IsSolvable B := IsSolvable.mk (R := ZMod 2) (le_antisymm h3 bot_le)
    let e := (Matrix.toLinAlgEquiv' (R := ZMod 2) (n := Fin 2)).toLieEquiv
    have : IsSolvable (Module.End (ZMod 2) (Fin 2 → ZMod 2)) :=
      (solvable_iff_equiv_solvable e).mp inferInstance
    let L : LieSubalgebra (ZMod 2) (Module.End (ZMod 2) (Fin 2 → ZMod 2)) := ⊤
    intro h
    have : IsLieAbelian L := (isLieAbelian_iff_center_eq_top (ZMod 2) L).mpr
      (h.symm.trans (radical_eq_top_of_isSolvable (ZMod 2) L))
    have : IsLieAbelian (Module.End (ZMod 2) (Fin 2 → ZMod 2)) :=
      (lie_abelian_iff_equiv_lie_abelian (LieSubalgebra.topEquiv : L ≃ₗ⁅ZMod 2⁆ Module.End (ZMod 2) (Fin 2 → ZMod 2))).mp inferInstance
    have : IsLieAbelian B := (lie_abelian_iff_equiv_lie_abelian e).mpr inferInstance
    have hz := congrArg (fun z : B => z 0 1)
      (trivial_lie_zero B B !![1, 0; 0, 0] !![0, 1; 0, 0])
    dsimp [B] at hz
    norm_num [Ring.lie_def, Matrix.mul_apply, Fin.sum_univ_two] at hz


end HodgeLean.Foundations
