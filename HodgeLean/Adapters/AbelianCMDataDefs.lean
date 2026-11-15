import HodgeLean.Adapters.AbelianEndomorphisms
import HodgeLean.Adapters.AbelianEndomorphisms3Defs
import HodgeLean.Adapters.AbelianHomPullbackDefs
import HodgeLean.Adapters.HodgeHigherDegreeAbelianDefs
import HodgeLean.Foundations.PowersVocabularyDefs

/-! # CM data from endomorphisms, stage G4 of the Powers flagship: definitions (FROZEN)

Definitions for `AbelianCMData`, stage G4 of formalizing PW v0.3, Theorem 4.2 (`thm:gen`). For
an abelian variety `A` and a `ℚ`-algebra map `θ : L →ₐ[ℚ] End⁰(A)`:

* `abelianEnd0Action A`: the action of `End⁰(A) = ℚ ⊗[ℤ] End(A)` on `HQ A 1` by pullback, the
  `ℚ`-linear extension of `abelianEndAction`. Pullback is contravariant, so it is an algebra map
  into the opposite ring `(Module.End ℚ (HQ A 1))ᵐᵒᵖ`.
* `pwAction A θ : L →ₐ[ℚ] Module.End ℚ (HQ A 1)`: the action of `L` through `θ`. As `L` is
  commutative, the order reversal disappears and it is an algebra map into `Module.End`.
  `pwActionRange A θ` is its range, the subalgebra `R` of PW-0's `gkLie`, `HodgeLieIsGk` and
  `cmPowerSpan`.
* `pwOrder A θ`: the subring `O = θ⁻¹(End(A))` of `L`, and `pwOrderEnd A θ a` a chosen
  endomorphism with `1 ⊗ f = θ a`.
* `AbelianPowerData A Y r`: group homomorphisms `p_i : Y ⟶ A`, `s_i : A ⟶ Y` with the biproduct
  identities, a stand-in for `Y = A^r`. `P.sumMap a = Σ a_i ∘ p_i : Y ⟶ A` for `a ∈ End(A)^r`,
  and `P.pwSumMap θ a`, the map `f_a` of Theorem 4.2, for `a ∈ O^r`.
* `pwPowerPullback A θ a`: PW-0's model pullback `cmPowerPullback` with coefficients `θ(a_i)`,
  for `a ∈ L^r`.
* `pwWeilAction A θ u d hu hpres`: Blocks' `WeilAction` of `J = pwAction A θ u` on the weight-one
  Hodge structure of `A`, for `u² = -d`, given the preservation of the Hodge pieces `hpres`.

No definition asserts a Hodge, generation or algebraicity property, nor that `pwOrder` is an
order. HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Foundations

namespace HodgeLean.Adapters

variable (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A] [IsIntegral A.left]
  [Smooth A.hom] [IsProjective A.hom]

/-- The action of `End(A)` on `HQ A 1`, as a ring map into the opposite ring.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.2 (rational representation
`ρ_r`, here contravariant); `spec_abelianEndAction_one`, `_mul`, `_zero`, `_add`. -/
def g4_endRingHom : AbelianEnd A →+* (Module.End ℚ (HQ A 1))ᵐᵒᵖ where
  toFun f := MulOpposite.op (abelianEndAction A f)
  map_one' := by rw [spec_abelianEndAction_one]; rfl
  map_mul' f g := by rw [spec_abelianEndAction_mul]; rfl
  map_zero' := by rw [spec_abelianEndAction_zero]; rfl
  map_add' f g := by rw [spec_abelianEndAction_add]; rfl

example (f : AbelianEnd A) : g4_endRingHom A f = MulOpposite.op (abelianEndAction A f) := rfl

/-- **The action of `End⁰(A)` on `HQ A 1`.** The `ℚ`-linear extension of `abelianEndAction` to
`End⁰(A) = ℚ ⊗[ℤ] End(A)`: `q ⊗ f ↦ q • f^*`. Pullback reverses composition, so it is a
`ℚ`-algebra map into the opposite ring of `Module.End ℚ (HQ A 1)`.
Source: Mumford, *Abelian Varieties*, §19 (`End⁰(X) = End(X) ⊗_ℤ ℚ` and its action on
`H₁(X, ℚ)`); Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.2; Mathlib
`Algebra.TensorProduct.lift`. -/
def abelianEnd0Action : AbelianEnd0 A →ₐ[ℚ] (Module.End ℚ (HQ A 1))ᵐᵒᵖ :=
  Algebra.TensorProduct.lift (Algebra.ofId ℚ _) (g4_endRingHom A).toIntAlgHom
    fun q _ => by rw [Algebra.ofId_apply]; exact Algebra.commute_algebraMap_left q _

example : abelianEnd0Action A 1 = 1 := map_one _

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- **The action of `L` on `HQ A 1` through `θ : L →ₐ[ℚ] End⁰(A)`**: `x ↦ (θ x)^*`. The action of
`End⁰(A)` lands in the opposite ring; on the commutative `L` the two orders agree, so this is a
`ℚ`-algebra map into `Module.End ℚ (HQ A 1)` itself.
Source: PW v0.3, Subsection 2.1 (the CM field `L` acting through `End⁰(A)` on `V = H¹(A, ℚ)`);
`abelianEnd0Action`. -/
def pwAction (θ : L →ₐ[ℚ] AbelianEnd0 A) : L →ₐ[ℚ] Module.End ℚ (HQ A 1) where
  toFun x := (abelianEnd0Action A (θ x)).unop
  map_one' := by rw [map_one, map_one, MulOpposite.unop_one]
  map_mul' x y := by
    rw [mul_comm x y, map_mul, map_mul, MulOpposite.unop_mul]
  map_zero' := by rw [map_zero, map_zero, MulOpposite.unop_zero]
  map_add' x y := by rw [map_add, map_add, MulOpposite.unop_add]
  commutes' q := by rw [AlgHom.commutes, AlgHom.commutes, MulOpposite.algebraMap_apply,
    MulOpposite.unop_op]

example (θ : L →ₐ[ℚ] AbelianEnd0 A) (x : L) :
    pwAction A θ x = (abelianEnd0Action A (θ x)).unop := rfl

/-- The image of `L` in `Module.End ℚ (HQ A 1)`: the subalgebra `R` of PW-0's `gkLie`,
`HodgeLieIsGk` and `cmPowerSpan` for an actual abelian variety.
Source: PW v0.3, Subsection 2.3 (`Lef(A)` is the centralizer of `L`); `pwAction`. -/
def pwActionRange (θ : L →ₐ[ℚ] AbelianEnd0 A) : Subalgebra ℚ (Module.End ℚ (HQ A 1)) :=
  (pwAction A θ).range

example (θ : L →ₐ[ℚ] AbelianEnd0 A) (x : L) : pwAction A θ x ∈ pwActionRange A θ :=
  ⟨x, rfl⟩

/-- **The order `O = θ⁻¹(End(A))`**: the elements of `L` whose image in `End⁰(A)` is an actual
endomorphism `1 ⊗ f`. It is a subring of `L`.
Source: PW v0.3, Theorem 4.2 (an order `𝒪` of `L` acting on `A`); Mumford, *Abelian Varieties*,
§19 (`End(A)` is a lattice in `End⁰(A)`). -/
def pwOrder (θ : L →ₐ[ℚ] AbelianEnd0 A) : Subring L where
  carrier := {a | ∃ f : AbelianEnd A, (1 : ℚ) ⊗ₜ[ℤ] f = θ a}
  mul_mem' := by
    rintro a b ⟨f, hf⟩ ⟨g, hg⟩
    exact ⟨f * g, by rw [map_mul, ← hf, ← hg, Algebra.TensorProduct.tmul_mul_tmul, one_mul]⟩
  one_mem' := ⟨1, by rw [map_one, Algebra.TensorProduct.one_def]⟩
  add_mem' := by
    rintro a b ⟨f, hf⟩ ⟨g, hg⟩
    exact ⟨f + g, by rw [map_add, ← hf, ← hg, TensorProduct.tmul_add]⟩
  zero_mem' := ⟨0, by rw [map_zero, TensorProduct.tmul_zero]⟩
  neg_mem' := by
    rintro a ⟨f, hf⟩
    exact ⟨-f, by rw [map_neg, ← hf, TensorProduct.tmul_neg]⟩

example (θ : L →ₐ[ℚ] AbelianEnd0 A) (a : L) :
    a ∈ pwOrder A θ ↔ ∃ f : AbelianEnd A, (1 : ℚ) ⊗ₜ[ℤ] f = θ a := Iff.rfl

/-- A chosen endomorphism `f` with `1 ⊗ f = θ a`, for `a ∈ O`.
Source: PW v0.3, Theorem 4.2 (the action of `𝒪` on `A`); `pwOrder`. -/
def pwOrderEnd (θ : L →ₐ[ℚ] AbelianEnd0 A) (a : pwOrder A θ) : AbelianEnd A :=
  a.2.choose

example (θ : L →ₐ[ℚ] AbelianEnd0 A) (a : pwOrder A θ) :
    (1 : ℚ) ⊗ₜ[ℤ] pwOrderEnd A θ a = θ a :=
  a.2.choose_spec

/-- **Power data**: an abelian `Y` with `r` group homomorphisms `p_i : Y ⟶ A` and `s_i : A ⟶ Y`
satisfying the biproduct identities `p_j ∘ s_i = δ_ij` (`1` is the zero homomorphism, the
constant map to the identity point) and `Σ_i s_i ∘ p_i = 𝟙 Y` (sum in the group `Y ⟶ Y`). The
power `A^r` with its projections and inclusions is the intended instance; it is not built here.
Source: PW v0.3, Theorem 4.2 (the powers `A^r`); Mac Lane, *Categories for the Working
Mathematician*, §VIII.2 (biproducts in additive categories); Mumford, *Abelian Varieties*, §19
(the category of abelian varieties is additive). -/
structure AbelianPowerData (A Y : Over (Spec ↧ℂ)) [GrpObj A] [GrpObj Y] [IsCommMonObj Y]
    (r : ℕ) where
  /-- The projections `p_i : Y ⟶ A`. -/
  proj : Fin r → (Y ⟶ A)
  /-- The inclusions `s_i : A ⟶ Y`. -/
  incl : Fin r → (A ⟶ Y)
  proj_isMonHom : ∀ i, IsMonHom (proj i)
  incl_isMonHom : ∀ i, IsMonHom (incl i)
  /-- `p_j ∘ s_i = δ_ij`. -/
  incl_proj : ∀ i j, incl i ≫ proj j = if i = j then 𝟙 A else 1
  /-- `Σ_i s_i ∘ p_i = 𝟙 Y`. -/
  sum_proj_incl : ∏ i, (proj i ≫ incl i) = 𝟙 Y

/-- The first power: `Y = A`, `p = s = 𝟙 A`. -/
example : AbelianPowerData A A 1 where
  proj _ := 𝟙 A
  incl _ := 𝟙 A
  proj_isMonHom _ := inferInstance
  incl_isMonHom _ := inferInstance
  incl_proj i j := by rw [Subsingleton.elim i j, ite_eq_left_iff.2 fun h => (h rfl).elim, Category.comp_id]
  sum_proj_incl := by rw [Fin.prod_univ_one, Category.comp_id]

namespace AbelianPowerData

variable {A} {Y : Over (Spec ↧ℂ)} [GrpObj Y] [IsCommMonObj Y] {r : ℕ}

/-- `Σ_i a_i ∘ p_i : Y ⟶ A` for endomorphisms `a_i` of `A` (product in the commutative group
`Y ⟶ A`).
Source: PW v0.3, Theorem 4.2 (the maps `f_a : A^r → A`, `(x_i) ↦ Σ a_i x_i`). -/
def sumMap (P : AbelianPowerData A Y r) (a : Fin r → AbelianEnd A) : Y ⟶ A :=
  ∏ i, (P.proj i ≫ (a i).hom)

example (P : AbelianPowerData A Y r) (a : Fin r → AbelianEnd A) :
    P.sumMap a = ∏ i, (P.proj i ≫ (a i).hom) := rfl

/-- **The map `f_a : A^r → A`** of Theorem 4.2, for `a ∈ O^r`: `P.sumMap` at the chosen
endomorphisms `pwOrderEnd A θ (a i)`.
Source: PW v0.3, Theorem 4.2 (`f_a : A^r → A`, `a ∈ 𝒪^r`). -/
def pwSumMap (P : AbelianPowerData A Y r) {L : Type*} [Field L] [Algebra ℚ L]
    (θ : L →ₐ[ℚ] AbelianEnd0 A) (a : Fin r → pwOrder A θ) : Y ⟶ A :=
  P.sumMap fun i => pwOrderEnd A θ (a i)

example (P : AbelianPowerData A Y r) (θ : L →ₐ[ℚ] AbelianEnd0 A) (a : Fin r → pwOrder A θ) :
    P.pwSumMap θ a = ∏ i, (P.proj i ≫ (pwOrderEnd A θ (a i)).hom) := rfl

end AbelianPowerData

/-- **The model pullback for `a ∈ L^r`**: PW-0's `cmPowerPullback` over `R = pwActionRange A θ`
with coefficients `θ(a_i)^*`, `x ↦ Σ_i θ(a_i)^* x ⊗ e_i : HQ A 1 → HQ A 1 ⊗ ℚ^r`.
Source: PW v0.3, Theorem 4.2 and its proof, paragraph "Weil classes" (`f_a^*` on `H¹`);
`cmPowerPullback` (`Foundations/PowersVocabularyDefs.lean`). -/
def pwPowerPullback (θ : L →ₐ[ℚ] AbelianEnd0 A) {r : ℕ} (a : Fin r → L) :
    HQ A 1 →ₗ[ℚ] HQ A 1 ⊗[ℚ] (Fin r → ℚ) :=
  cmPowerPullback (pwActionRange A θ) fun i => ⟨pwAction A θ (a i), a i, rfl⟩

example (θ : L →ₐ[ℚ] AbelianEnd0 A) {r : ℕ} (a : Fin r → L) (x : HQ A 1) :
    pwPowerPullback A θ a x = ∑ i, pwAction A θ (a i) x ⊗ₜ[ℚ] (Pi.single i 1 : Fin r → ℚ) := by
  simp [pwPowerPullback, cmPowerPullback]

/-- **The Weil action of `k = ℚ(u)` on `H¹(A)`**: Blocks' `WeilAction` with `J = pwAction A θ u`
on the weight-one Hodge structure `abelianWeightOneHodgeStructure A`, for `u² = -d`. The
preservation of the Hodge pieces is the argument `hpres`; it holds for every `u`
(`spec_g4_pwAction_map_le`), so the definition makes no assumption on `A`.
Source: PW v0.3, Subsection 2.2 (`W_k(A)` for `k = ℚ(u) ⊆ L` acting on `V`); van Geemen, *An
introduction to the Hodge conjecture for abelian varieties*, §5; `HodgeBlocks.WeilAction`. -/
def pwWeilAction (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) (d : ℚ) (hu : u ^ 2 = -algebraMap ℚ L d)
    (hpres : ∀ pq, (cohomologyHodgePiece A 1 pq).map ((pwAction A θ u).baseChange ℂ) ≤
      cohomologyHodgePiece A 1 pq) :
    letI := (finiteBetti_abelian A).finite 1
    HodgeBlocks.WeilAction (abelianWeightOneHodgeStructure A) d :=
  letI := (finiteBetti_abelian A).finite 1
  { J := pwAction A θ u
    J_sq := by
      rw [← Module.End.mul_eq_comp, ← map_mul, ← pow_two, hu, map_neg, AlgHom.commutes,
        Algebra.algebraMap_eq_smul_one, neg_smul]
      rfl
    preserves := hpres }

example (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) (d : ℚ) (hu : u ^ 2 = -algebraMap ℚ L d)
    (hpres : ∀ pq, (cohomologyHodgePiece A 1 pq).map ((pwAction A θ u).baseChange ℂ) ≤
      cohomologyHodgePiece A 1 pq) :
    letI := (finiteBetti_abelian A).finite 1
    (pwWeilAction A θ u d hu hpres).J = pwAction A θ u := rfl

end HodgeLean.Adapters
