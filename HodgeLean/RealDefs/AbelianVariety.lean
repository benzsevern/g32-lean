import HodgeLean.RealDefs.CupFiltered
import HodgeLean.RealDefs.FundamentalClassUnit
import HodgeLean.Blocks.Milestone.HardLefschetz

/-! # The abelian-variety layer of `Blocks/` over the real `H^*(X(ℂ); ℚ)`

Roadmap `docs/roadmap/layer3.md` §2(c) and §3 C6, C7, C9 / C10.

* `CupProduct.cupWedgeMap` (C6): `a₁ ∧ ⋯ ∧ a_m ↦ a₁ ∪ ⋯ ∪ a_m`, from `⋀^m H¹` to `H^m`. Its
  alternation is derived from `graded_comm` in bidegree `(1, 1)` over `ℚ`
  (`CupProduct.cup_self_eq_zero`); no field is added for it. It sends the degree-zero unit to
  `unitClass X` (`cupWedgeMap_zero`), is the identification `⋀¹ H¹ ≃ H¹` in degree one
  (`cupWedgeMap_one`), and is multiplicative (`cupWedgeMap_wedge`).
* `TorusCohomology` (C7): the torus theorem, `⋀^m H¹ ≅ H^m` by cup product and `dim H¹ = 2g`.
* `CycleClassMultiplicative` (C9): cycle classes multiply. It implies `AlgebraicTimesDivisor`
  (`algebraicTimesDivisor_of_cycleClassMultiplicative`).
* `abelianVarietyCohomologyOf`: the Blocks `AbelianVarietyCohomology (HQ X 1)` of a real `X`,
  whose `cohomology m` is the Hodge structure of `H^m(X(ℂ); ℚ)` moved to `⋀^m H¹`
  (`isHodgeClass_abelianVarietyCohomologyOf_iff`).
* `isAlgebraicOf`, `cycleClassPredicateOf` and the transfer `hdg_le_span_of_hodgeConjectureFor`
  (C10): the Blocks `HodgeConjectureFor` for the package gives upstream's
  `Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p`.
* `hdg_le_span_abelian_g1`, `_g2`, `_g3`: the Blocks theorems `hodgeConjecture_g1`, `g2`, `g3`
  carried through the transfer, with each Blocks premise derived from real-side hypotheses.

C8 (`CycleClassIsHodge`) lives in `CupFiltered.lean`. Statements are over `HQ X n` for the
kernel-time reason recorded in `Operations`. -/

open CategoryTheory AlgebraicGeometry ComplexPoint TopologicalSpace
open scoped TensorProduct

namespace HodgeLean.RealDefs

variable {X : Over (Spec ↧ℂ)} [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]

namespace CupProduct

/-- A degree-one class cups to zero with itself: `graded_comm` in bidegree `(1, 1)` gives
`a ∪ a = -(a ∪ a)`, and `ℚ` has characteristic zero. -/
theorem cup_self_eq_zero (μ : CupProduct X) {k : ℕ} (h : 1 + 1 = k) (a : HQ X 1) :
    μ.cup h a a = 0 := by
  have hc := μ.graded_comm h h a a
  rw [show (-1 : ℚ) ^ (1 * 1) = -1 by norm_num, neg_one_smul] at hc
  have h2 : (2 : ℚ) • μ.cup h a a = 0 := by
    rw [two_smul]
    nth_rewrite 1 [hc]
    exact neg_add_cancel _
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

/-- Degree-one classes anticommute. -/
theorem cup_comm_one (μ : CupProduct X) {k : ℕ} (h : 1 + 1 = k) (a b : HQ X 1) :
    μ.cup h b a = -μ.cup h a b := by
  rw [μ.graded_comm h h a b, show (-1 : ℚ) ^ (1 * 1) = -1 by norm_num, neg_one_smul]

/-- One step of the cup of `m` degree-one classes: `a ↦ (a ∪ -) ∘ f`, linear in `a`. -/
noncomputable def cupLeftMulti (μ : CupProduct X) (m : ℕ)
    (f : MultilinearMap ℚ (fun _ : Fin m => HQ X 1) (HQ X m)) :
    HQ X 1 →ₗ[ℚ] MultilinearMap ℚ (fun _ : Fin m => HQ X 1) (HQ X (m + 1)) where
  toFun a := (μ.cup (Nat.add_comm 1 m) a).compMultilinearMap f
  map_add' a b := by ext; simp
  map_smul' c a := by ext; simp

/-- The multilinear map `(a₁, …, a_m) ↦ a₁ ∪ (a₂ ∪ ⋯ ∪ (a_m ∪ 1))`, with the unit as the empty
product. -/
noncomputable def cupMulti (μ : CupProduct X) :
    ∀ m : ℕ, MultilinearMap ℚ (fun _ : Fin m => HQ X 1) (HQ X m)
  | 0 => MultilinearMap.constOfIsEmpty ℚ _ (unitClass X)
  | m + 1 => (μ.cupLeftMulti m (cupMulti μ m)).uncurryLeft

theorem cupMulti_zero (μ : CupProduct X) (v : Fin 0 → HQ X 1) :
    μ.cupMulti 0 v = unitClass X :=
  rfl

theorem cupMulti_succ (μ : CupProduct X) (m : ℕ) (h : 1 + m = m + 1) (v : Fin (m + 1) → HQ X 1) :
    μ.cupMulti (m + 1) v = μ.cup h (v 0) (μ.cupMulti m (Fin.tail v)) :=
  rfl

/-- A degree-one class that already occurs among `w` cups `μ.cupMulti m w` to zero. -/
theorem cup_cupMulti_eq_zero (μ : CupProduct X) :
    ∀ (m : ℕ) (h : 1 + m = m + 1) (w : Fin m → HQ X 1) (k : Fin m),
      μ.cup h (w k) (μ.cupMulti m w) = 0
  | 0, _, _, k => k.elim0
  | m + 1, h, w, k => by
    rw [μ.cupMulti_succ m (Nat.add_comm 1 m),
      ← μ.assoc (rfl : 1 + 1 = 2) (Nat.add_comm 1 m) (by omega) h]
    refine Fin.cases ?_ (fun k' => ?_) k
    · rw [μ.cup_self_eq_zero, map_zero, LinearMap.zero_apply]
    · rw [μ.cup_comm_one, map_neg, LinearMap.neg_apply,
        μ.assoc (rfl : 1 + 1 = 2) (Nat.add_comm 1 m) (by omega) h]
      have := cup_cupMulti_eq_zero μ m (Nat.add_comm 1 m) (Fin.tail w) k'
      rw [Fin.tail] at this
      rw [this, map_zero, neg_zero]

/-- `μ.cupMulti m` vanishes on families with a repeated entry. -/
theorem cupMulti_eq_zero_of_eq (μ : CupProduct X) :
    ∀ (m : ℕ) (v : Fin m → HQ X 1) (i j : Fin m), v i = v j → i ≠ j → μ.cupMulti m v = 0
  | 0, _, i, _, _, _ => i.elim0
  | m + 1, v, i, j, hv, hij => by
    rw [μ.cupMulti_succ m (Nat.add_comm 1 m)]
    have key : ∀ (i j : Fin (m + 1)), v i = v j → i ≠ j → i = 0 →
        μ.cup (Nat.add_comm 1 m) (v 0) (μ.cupMulti m (Fin.tail v)) = 0 := by
      intro i j hv hij hi
      subst hi
      obtain ⟨j', rfl⟩ := Fin.exists_succ_eq.mpr hij.symm
      rw [hv]
      exact μ.cup_cupMulti_eq_zero m _ (Fin.tail v) j'
    by_cases hi : i = 0
    · exact key i j hv hij hi
    by_cases hj : j = 0
    · exact key j i hv.symm hij.symm hj
    obtain ⟨i', rfl⟩ := Fin.exists_succ_eq.mpr hi
    obtain ⟨j', rfl⟩ := Fin.exists_succ_eq.mpr hj
    rw [cupMulti_eq_zero_of_eq μ m (Fin.tail v) i' j' hv (fun h => hij (by rw [h])), map_zero]

/-- The alternating map `(a₁, …, a_m) ↦ a₁ ∪ ⋯ ∪ a_m`. -/
noncomputable def cupAlternating (μ : CupProduct X) (m : ℕ) :
    HQ X 1 [⋀^Fin m]→ₗ[ℚ] HQ X m where
  toMultilinearMap := μ.cupMulti m
  map_eq_zero_of_eq' v i j hv hij := μ.cupMulti_eq_zero_of_eq m v i j hv hij

/-- **The wedge map (C6)** `⋀^m H¹(X(ℂ); ℚ) → H^m(X(ℂ); ℚ)`, `a₁ ∧ ⋯ ∧ a_m ↦ a₁ ∪ ⋯ ∪ a_m`. -/
noncomputable def cupWedgeMap (μ : CupProduct X) (m : ℕ) : ⋀[ℚ]^m (HQ X 1) →ₗ[ℚ] HQ X m :=
  exteriorPower.alternatingMapLinearEquiv (μ.cupAlternating m)

theorem cupWedgeMap_ιMulti (μ : CupProduct X) (m : ℕ) (v : Fin m → HQ X 1) :
    μ.cupWedgeMap m (exteriorPower.ιMulti ℚ m v) = μ.cupMulti m v :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _

/-- The degree-zero unit of the exterior algebra goes to the unit of `H^0`. -/
theorem cupWedgeMap_zero (μ : CupProduct X) :
    μ.cupWedgeMap 0 (exteriorPower.ιMulti ℚ 0 Fin.elim0) = unitClass X :=
  μ.cupWedgeMap_ιMulti 0 _

/-- On `⋀^1`, the wedge map is the canonical identification `⋀^1 H¹ ≃ H¹`. -/
theorem cupWedgeMap_one (μ : CupProduct X) :
    μ.cupWedgeMap 1 = (exteriorPower.oneEquiv ℚ (HQ X 1)).toLinearMap := by
  refine exteriorPower.linearMap_ext (AlternatingMap.ext fun v => ?_)
  simp only [LinearMap.compAlternatingMap_apply, LinearEquiv.coe_coe,
    exteriorPower.oneEquiv_ιMulti]
  rw [cupWedgeMap_ιMulti, μ.cupMulti_succ 0 rfl]
  exact μ.cup_one (v 0)

/-- `cupMulti` turns concatenation into the cup product, with the target degree given by an
equation. -/
theorem cupMulti_append (μ : CupProduct X) (n : ℕ) (b : Fin n → HQ X 1) :
    ∀ (m : ℕ) (a : Fin m → HQ X 1) (k : ℕ) (h : m + n = k) (c : Fin k → HQ X 1),
      (∀ i : Fin m, c (Fin.cast h (Fin.castAdd n i)) = a i) →
      (∀ j : Fin n, c (Fin.cast h (Fin.natAdd m j)) = b j) →
      μ.cupMulti k c = μ.cup h (μ.cupMulti m a) (μ.cupMulti n b)
  | 0, a, k, h, c, _, hc2 => by
    obtain rfl : k = n := by omega
    rw [cupMulti_zero, μ.one_cup]
    congr 1
    funext j
    rw [← hc2 j]
    congr 1
    ext
    simp
  | m + 1, a, k, h, c, hc1, hc2 => by
    obtain rfl : k = m + n + 1 := by omega
    rw [μ.cupMulti_succ (m + n) (Nat.add_comm 1 _), μ.cupMulti_succ m (Nat.add_comm 1 m),
      μ.assoc (Nat.add_comm 1 m) rfl h (Nat.add_comm 1 _)]
    have h0 : c 0 = a 0 := by
      rw [← hc1 0]
      congr 1
    rw [h0, cupMulti_append μ n b m (Fin.tail a) (m + n) rfl (Fin.tail c)
      (fun i => by
        change c _ = a i.succ
        rw [← hc1 i.succ]
        congr 1)
      (fun j => by
        change c _ = b j
        rw [← hc2 j]
        congr 1
        ext
        simp
        omega)]

/-- The wedge of two decomposable vectors is the decomposable vector of the concatenation. -/
theorem wedge_ιMulti {M : Type*} [AddCommGroup M] [Module ℚ M] (m n : ℕ) (a : Fin m → M)
    (b : Fin n → M) :
    exteriorPower.wedge ℚ M m n (exteriorPower.ιMulti ℚ m a) (exteriorPower.ιMulti ℚ n b) =
      exteriorPower.ιMulti ℚ (m + n) (Fin.append a b) := by
  apply Subtype.ext
  change ExteriorAlgebra.ιMulti ℚ m a * ExteriorAlgebra.ιMulti ℚ n b = _
  rw [ExteriorAlgebra.ιMulti_mul_ιMulti]
  rfl

/-- **Multiplicativity of the wedge map**: it sends `v ∧ w` to `v ∪ w`. -/
theorem cupWedgeMap_wedge (μ : CupProduct X) (m n : ℕ) (v : ⋀[ℚ]^m (HQ X 1))
    (w : ⋀[ℚ]^n (HQ X 1)) :
    μ.cupWedgeMap (m + n) (exteriorPower.wedge ℚ _ m n v w) =
      μ.cup rfl (μ.cupWedgeMap m v) (μ.cupWedgeMap n w) := by
  have key : (exteriorPower.wedge ℚ (HQ X 1) m n).compr₂ (μ.cupWedgeMap (m + n)) =
      (μ.cup rfl).compl₁₂ (μ.cupWedgeMap m) (μ.cupWedgeMap n) := by
    refine exteriorPower.linearMap_ext (AlternatingMap.ext fun a => ?_)
    refine exteriorPower.linearMap_ext (AlternatingMap.ext fun b => ?_)
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.compr₂_apply,
      LinearMap.compl₁₂_apply]
    rw [wedge_ιMulti, cupWedgeMap_ιMulti, cupWedgeMap_ιMulti, cupWedgeMap_ιMulti]
    exact μ.cupMulti_append n b m a (m + n) rfl _ (fun i => Fin.append_left a b i)
      (fun j => Fin.append_right a b j)
  exact LinearMap.congr_fun₂ key v w

end CupProduct

section Torus

variable (μ : CupProduct X)

/-- **Torus cohomology (C7)**: for an abelian variety `X` of dimension `g`, `H¹(X(ℂ); ℚ)` has
dimension `2g`, and cup product identifies `⋀^m H¹(X(ℂ); ℚ)` with `H^m(X(ℂ); ℚ)` in every degree:
`μ.cupWedgeMap m` is bijective.

Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, Lemma 1.3.1.

Birkenhake–Lange state, for a complex torus `X = V / Λ` of dimension `g`, that the canonical map
`⋀^n H¹(X, ℤ) → H^n(X, ℤ)` induced by cup product is an isomorphism for every `n ≥ 1`, with
`H¹(X, ℤ) = Hom(Λ, ℤ)` free of rank `2g`. Tensoring with `ℚ` gives the rational statement; `n = 0`
is the unit (`ℚ → H^0`, `1 ↦ 1`, an isomorphism since `X(ℂ)` is connected). The structure takes as
given that upstream's sheaf cohomology `H^n(X; ℚ)` and `μ` are the singular cohomology and cup
product of the torus `X(ℂ)`, and that Krull dimension `dim X.left` is the complex dimension `g`.

**Consistency.** For an elliptic curve (`g = 1`), `X(ℂ)` is a real 2-torus, with Betti numbers
`1, 2, 1, 0, …`, and `dim ⋀^m ℚ² = 1, 2, 1, 0, …`. For an abelian surface (`g = 2`), the real
4-torus has Betti numbers `1, 4, 6, 4, 1, 0, …`, and `dim ⋀^m ℚ⁴ = C(4, m) = 1, 4, 6, 4, 1, 0, …`. For an abelian
threefold (`g = 3`), both sides are `C(6, m) = 1, 6, 15, 20, 15, 6, 1, 0, …`. In every case both
sides are `0` for `m > 2g`. None of this is proved here for upstream's `H^n`.

**Non-degeneracy.** At `m = 0`, `bijective` makes `H^0` a line spanned by
`cupWedgeMap 0 1 = unitClass X` (`CupProduct.cupWedgeMap_zero`), which is nonzero
(`unitClass_ne_zero'`), so the bijection is not between zero spaces. For `g ≥ 1`, `finrank_eq`
excludes `H¹ = 0`. -/
@[hodge_hypothesis]
structure TorusCohomology [GrpObj X] : Prop where
  finite : Module.Finite ℚ (HQ X 1)
  finrank_eq : Module.finrank ℚ (HQ X 1) = 2 * dim X.left
  bijective : ∀ m : ℕ, Function.Bijective (μ.cupWedgeMap m)

variable {μ} [GrpObj X]

/-- The torus isomorphism `⋀^m H¹(X(ℂ); ℚ) ≃ H^m(X(ℂ); ℚ)`, from `TorusCohomology.bijective`. -/
noncomputable def TorusCohomology.cupWedgeEquiv (hT : TorusCohomology μ) (m : ℕ) :
    ⋀[ℚ]^m (HQ X 1) ≃ₗ[ℚ] HQ X m :=
  LinearEquiv.ofBijective (μ.cupWedgeMap m) (hT.bijective m)

@[simp] theorem TorusCohomology.cupWedgeEquiv_apply (hT : TorusCohomology μ) (m : ℕ)
    (v : ⋀[ℚ]^m (HQ X 1)) : hT.cupWedgeEquiv m v = μ.cupWedgeMap m v :=
  rfl

end Torus

section Multiplicative

variable (X) in
omit [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] in
/-- The identification `HQ X m ≃ HQ X n` along an equation `m = n` of degrees. -/
noncomputable def HQ.castEquiv {m n : ℕ} (h : m = n) : HQ X m ≃ₗ[ℚ] HQ X n := by
  subst h
  exact LinearEquiv.refl ℚ _

omit [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] in
@[simp] theorem HQ.castEquiv_apply_self {m : ℕ} (h : m = m) (a : HQ X m) :
    HQ.castEquiv X h a = a :=
  rfl

/-- Recasting the degree of a cup product is the cup product into the recast degree. -/
theorem CupProduct.castEquiv_cup (μ : CupProduct X) {i j k k' : ℕ} (h : i + j = k) (h' : k = k')
    (a : HQ X i) (b : HQ X j) :
    HQ.castEquiv X h' (μ.cup h a b) = μ.cup (h.trans h') a b := by
  subst h'
  rfl

/-- **Cycle classes multiply (C9)**: the cup product of a codimension-`p` and a codimension-`q`
algebraic class is a codimension-`(p + q)` algebraic class.

Source: Fulton, *Intersection Theory*, 2nd ed., Ergeb. Math. Grenzgeb. (3) 2, Ch. 19, Corollary 19.2.

Fulton's Corollary 19.2 says that for a nonsingular complex variety the cycle map
`cl : A^*(X) → H^{2*}(X; ℤ)` is a ring homomorphism from the Chow ring (intersection product) to
cohomology (cup product). The intersection product of a codimension-`p` and a codimension-`q`
cycle class is a codimension-`(p + q)` cycle class, so its image lies in the span of
codimension-`(p + q)` cycle classes. The structure takes as given that upstream's
`cycleComponentSheafClass` agrees with Fulton's cycle map (tensored with `ℚ`) and that `μ` is the
cup product of `X(ℂ)`.

**Relation to `AlgebraicTimesDivisor`.** This generalizes `AlgebraicTimesDivisor.cup_mem`, which
is the case `p = 1` with the first factor a fixed divisor class `η`:
`algebraicTimesDivisor_of_cycleClassMultiplicative` derives `AlgebraicTimesDivisor μ η` from this
structure and `η ∈ algebraicCycleClassSpan X 1`.

**Consistency.** For `p = 0`, on a preconnected `X(ℂ)` the span of codimension-zero classes is
`H^0` (`algebraicCycleClassSpan_zero_eq_top`), spanned by `[X] = 1`, and `1 ∪ b = b`. For
`X = ℙ¹`, the only case with `p, q ≥ 1` lands in `H^4 = 0`. -/
@[hodge_hypothesis]
structure CycleClassMultiplicative (μ : CupProduct X) : Prop where
  mem : ∀ {p q : ℕ} (h : 2 * p + 2 * q = 2 * (p + q)) (a : HQ X (2 * p)) (b : HQ X (2 * q)),
      a ∈ algebraicCycleClassSpan X p → b ∈ algebraicCycleClassSpan X q →
      μ.cup h a b ∈ algebraicCycleClassSpan X (p + q)

/-- `CycleClassMultiplicative.mem` with the target codimension given by an equation. -/
theorem CycleClassMultiplicative.mem_of_eq {μ : CupProduct X} (hM : CycleClassMultiplicative μ)
    {p q r : ℕ} (h : 2 * p + 2 * q = 2 * r) (a : HQ X (2 * p)) (b : HQ X (2 * q))
    (ha : a ∈ algebraicCycleClassSpan X p) (hb : b ∈ algebraicCycleClassSpan X q) :
    μ.cup h a b ∈ algebraicCycleClassSpan X r := by
  obtain rfl : r = p + q := by omega
  exact hM.mem h a b ha hb

/-- Divisor closure (`AlgebraicTimesDivisor`) follows from multiplicativity of cycle classes and
`η` being a divisor class. -/
theorem algebraicTimesDivisor_of_cycleClassMultiplicative {μ : CupProduct X} {η : HQ X 2}
    (hM : CycleClassMultiplicative μ) (hη : η ∈ algebraicCycleClassSpan X 1) :
    AlgebraicTimesDivisor X μ η :=
  ⟨hη, fun {p} h a ha => hM.mem_of_eq (p := 1) (q := p) h η a hη ha⟩

end Multiplicative

section Package

variable {μ : CupProduct X} [GrpObj X]

omit [GrpObj X] in
/-- The unit of `H^0(X(ℂ); ℚ)` is algebraic: it is the class of `X` (`[X] = 1`). -/
theorem unitClass_mem_algebraicCycleClassSpan :
    (unitClass X : H^(2 * 0)(X; ℚ)) ∈ algebraicCycleClassSpan X 0 := by
  have hη := coheight_genericPoint X.left
  rw [← cycleComponentSheafClass_generic X (genericPoint X.left) hη]
  have hle : Submodule.span ℚ {cycleComponentSheafClass X (genericPoint X.left) hη} ≤
      algebraicCycleClassSpan X 0 :=
    le_sSup ⟨genericPoint X.left, hη, rfl⟩
  exact hle (Submodule.mem_span_singleton_self _)

/-- **The abelian-variety package of a real `X` (C6).** From finite Betti numbers (C1), the
Betti–de Rham comparison (C2), the Hodge decomposition (C4) and the torus theorem (C7), the Blocks
data `AbelianVarietyCohomology (HQ X 1)` with

* `g = dim X.left`, and `rank_eq` from `TorusCohomology.finrank_eq`;
* `weight1` the Hodge structure `cohomologyHodgeStructure` of `H¹(X(ℂ); ℚ)`;
* `cohomology m` the Hodge structure `cohomologyHodgeStructure` of `H^m(X(ℂ); ℚ)`, transported to
  `⋀^m H¹` along the torus isomorphism `cupWedgeEquiv m` (`QHodgeStructure.congr`).

So `cohomology m` is the Hodge structure of `H^m(X(ℂ); ℚ)`, transported to `⋀^m H¹`
(`isHodgeClass_abelianVarietyCohomologyOf_iff`), which is what the transfer
`hdg_le_span_of_hodgeConjectureFor` needs.

**Referee disclosure of `AbelianVarietyCohomology`.** That docstring says `weight1` and
`cohomology` are independent data, and that `cohomology m` need not be the Hodge structure induced
on `⋀^m` of `weight1`. This package answers the half about provenance: `weight1` and every
`cohomology m` are the Hodge structures of the real cohomology of one `X`, and `rank_eq` holds with
`g = dim X.left`. It does **not** answer the half about compatibility: no theorem here shows that
`cohomology m` equals `weight1.exteriorPower m` (the roadmap's `IsExteriorOfWeightOne`). That needs
`cupWedgeMap` to be a morphism of Hodge structures (from O5, `CupFiltered`). It is proved, under
C1, C2, C4, C7 and O5, as `isExteriorOfWeightOne_of_cupFiltered` in `AbelianExterior.lean`. -/
noncomputable def abelianVarietyCohomologyOf (hF : FiniteBetti X) (hB : BettiDeRhamIso X)
    (hD : HodgeDecomposition X) (hT : TorusCohomology μ) :
    letI := hT.finite
    HodgeBlocks.AbelianVarietyCohomology (HQ X 1) :=
  letI := hT.finite
  { g := dim X.left
    rank_eq := hT.finrank_eq
    weight1 := cohomologyHodgeStructure hF hB hD 1
    cohomology := fun m =>
      letI := hF.finite m
      HodgeBlocks.QHodgeStructure.congr (HQ X m) (cohomologyHodgeStructure hF hB hD m)
        (hT.cupWedgeEquiv m).symm }

/-- A class `v ∈ ⋀^(2p) H¹` is a Hodge class of the package's `cohomology (2p)` exactly when its
cup product `cupWedgeMap (2p) v` lies in upstream's `Hdg^p(X; ℚ)`. -/
theorem isHodgeClass_abelianVarietyCohomologyOf_iff (hF : FiniteBetti X) (hB : BettiDeRhamIso X)
    (hD : HodgeDecomposition X) (hT : TorusCohomology μ) (p : ℕ)
    (v : ⋀[ℚ]^(2 * p) (HQ X 1)) :
    letI := hT.finite
    HodgeBlocks.IsHodgeClass (p := (p : ℤ))
      ((abelianVarietyCohomologyOf hF hB hD hT).cohomology (2 * p)) v ↔
      (μ.cupWedgeMap (2 * p) v : H^(2 * p)(X; ℚ)) ∈ Hdg^p(X; ℚ) := by
  let := hT.finite
  let := hF.finite (2 * p)
  rw [mem_hodgeClasses_iff_tmul_mem, ← cohomologyHodgeStructure_H hF hB hD (2 * p)]
  change (1 : ℂ) ⊗ₜ[ℚ] v ∈ ((cohomologyHodgeStructure hF hB hD (2 * p)).H ((p : ℤ), (p : ℤ))).map
    (HodgeBlocks.QHodgeStructure.complexificationCongr (V := HQ X (2 * p))
      (W := ⋀[ℚ]^(2 * p) (HQ X 1)) (hT.cupWedgeEquiv (2 * p)).symm).toLinearMap
      ↔ _
  rw [Submodule.mem_map_equiv]
  rfl

end Package

section Transfer

variable (μ : CupProduct X)

/-- The algebraicity predicate on `⋀^* H¹(X(ℂ); ℚ)` that the transfer uses (C9/C10): `v` is
algebraic when it is `0`, or when its degree is `m = 2p` and its cup product `cupWedgeMap m v`,
read in `H^(2p)` along `m = 2p`, lies in `algebraicCycleClassSpan X p`. -/
def isAlgebraicOf : ∀ {m : ℕ}, ⋀[ℚ]^m (HQ X 1) → Prop := fun {m} v =>
  v = 0 ∨ ∃ (p : ℕ) (h : m = 2 * p),
    (HQ.castEquiv X h (μ.cupWedgeMap m v) : H^(2 * p)(X; ℚ)) ∈ algebraicCycleClassSpan X p

variable {μ}

/-- In degree `2p`, `v` is algebraic exactly when `cupWedgeMap (2p) v` is a rational combination
of codimension-`p` cycle classes. -/
theorem isAlgebraicOf_iff (p : ℕ) (v : ⋀[ℚ]^(2 * p) (HQ X 1)) :
    isAlgebraicOf μ v ↔
      (μ.cupWedgeMap (2 * p) v : H^(2 * p)(X; ℚ)) ∈ algebraicCycleClassSpan X p := by
  refine ⟨fun hv => ?_, fun hv => Or.inr ⟨p, rfl, hv⟩⟩
  rcases hv with rfl | ⟨q, h, hv⟩
  · rw [map_zero]
    exact Submodule.zero_mem _
  · obtain rfl : q = p := by omega
    exact hv

/-- An algebraic class in degree `m` is zero, or sits in even degree `m = 2p` with an algebraic cup
product. -/
theorem isAlgebraicOf_cases {m : ℕ} {v : ⋀[ℚ]^m (HQ X 1)} (hv : isAlgebraicOf μ v) :
    v = 0 ∨ ∃ (p : ℕ) (h : m = 2 * p),
      (HQ.castEquiv X h (μ.cupWedgeMap m v) : H^(2 * p)(X; ℚ)) ∈ algebraicCycleClassSpan X p :=
  hv

variable [GrpObj X]

/-- **The cycle-class predicate of a real `X` (C9/C10).** With multiplicativity of cycle classes
(C9), cycle classes being Hodge (C8) and `η` a divisor class, `isAlgebraicOf μ` satisfies the
Blocks interface `IsCycleClassPredicate` on the package `abelianVarietyCohomologyOf`, with
polarization the class of `η` in `⋀² H¹`. `one_mem` is `[X] = 1`
(`unitClass_mem_algebraicCycleClassSpan`), `wedge_mem` is multiplicativity of `cupWedgeMap` with
C9, and `isHodge` is C8 with `isHodgeClass_abelianVarietyCohomologyOf_iff`. -/
theorem cycleClassPredicateOf (hF : FiniteBetti X) (hB : BettiDeRhamIso X)
    (hD : HodgeDecomposition X) (hT : TorusCohomology μ) (hM : CycleClassMultiplicative μ)
    (hH : CycleClassIsHodge X) {η : HQ X 2} (hη : η ∈ algebraicCycleClassSpan X 1) :
    letI := hT.finite
    HodgeBlocks.IsCycleClassPredicate (abelianVarietyCohomologyOf hF hB hD hT)
      (fun {m} => isAlgebraicOf μ (m := m)) ((hT.cupWedgeEquiv 2).symm η) := by
  let := hT.finite
  refine
    { one_mem := Or.inr ⟨0, rfl, ?_⟩
      zero_mem := Or.inl rfl
      add_mem := ?_
      smul_mem := ?_
      wedge_mem := ?_
      isHodge := ?_
      polarization_mem := Or.inr ⟨1, rfl, ?_⟩ }
  · rw [HQ.castEquiv_apply_self, μ.cupWedgeMap_zero]
    exact unitClass_mem_algebraicCycleClassSpan
  · intro m v w hv hw
    rcases isAlgebraicOf_cases hv with rfl | ⟨p, rfl, hv⟩
    · rwa [zero_add]
    rcases isAlgebraicOf_cases hw with rfl | ⟨q, hq, hw⟩
    · rw [add_zero]
      exact Or.inr ⟨p, rfl, hv⟩
    obtain rfl : p = q := by omega
    rw [HQ.castEquiv_apply_self] at hv hw
    refine Or.inr ⟨p, rfl, ?_⟩
    rw [HQ.castEquiv_apply_self, map_add]
    exact Submodule.add_mem _ hv hw
  · intro m c v hv
    rcases isAlgebraicOf_cases hv with rfl | ⟨p, rfl, hv⟩
    · rw [smul_zero]
      exact Or.inl rfl
    refine Or.inr ⟨p, rfl, ?_⟩
    rw [map_smul, map_smul]
    exact Submodule.smul_mem _ c hv
  · intro m n v w hv hw
    rcases isAlgebraicOf_cases hv with rfl | ⟨p, rfl, hv⟩
    · rw [map_zero, LinearMap.zero_apply]
      exact Or.inl rfl
    rcases isAlgebraicOf_cases hw with rfl | ⟨q, rfl, hw⟩
    · rw [map_zero]
      exact Or.inl rfl
    refine Or.inr ⟨p + q, by ring, ?_⟩
    rw [μ.cupWedgeMap_wedge, CupProduct.castEquiv_cup]
    exact hM.mem _ _ _ hv hw
  · intro p v hv
    exact (isHodgeClass_abelianVarietyCohomologyOf_iff hF hB hD hT p v).mpr
      (hH.le p ((isAlgebraicOf_iff p v).mp hv))
  · rw [HQ.castEquiv_apply_self, ← hT.cupWedgeEquiv_apply, LinearEquiv.apply_symm_apply]
    exact hη

/-- **The transfer (C10).** For an abelian variety `X`, under finite Betti numbers (C1), the
Betti–de Rham comparison (C2), the Hodge decomposition (C4) and the torus theorem (C7), the Blocks
statement `HodgeConjectureFor` for the package `abelianVarietyCohomologyOf` and the predicate
`isAlgebraicOf μ` gives upstream's Hodge conjecture for `X`: `Hdg^p(X; ℚ) ≤
algebraicCycleClassSpan X p` for every `p`.

Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, Lemma 1.3.1 (through `TorusCohomology`); the transfer itself is proved here, with no further input.

A class `x ∈ Hdg^p(X; ℚ)` is the cup product of `v = (cupWedgeEquiv (2p)).symm x`, which is a Hodge
class of the package (`isHodgeClass_abelianVarietyCohomologyOf_iff`); the Blocks statement makes
`v` algebraic, and `isAlgebraicOf_iff` reads that as `x ∈ algebraicCycleClassSpan X p`. Neither
multiplicativity (C9) nor C8 is used here: they are what makes `isAlgebraicOf μ` a cycle-class
predicate (`cycleClassPredicateOf`), which the Blocks theorems that prove `HodgeConjectureFor`
need.

Checks: F-1689 -/
@[hodge_milestone] theorem hdg_le_span_of_hodgeConjectureFor (hF : FiniteBetti X)
    (hB : BettiDeRhamIso X) (hD : HodgeDecomposition X) (hT : TorusCohomology μ)
    (h : letI := hT.finite
      HodgeBlocks.HodgeConjectureFor (abelianVarietyCohomologyOf hF hB hD hT)
        (fun {m} => isAlgebraicOf μ (m := m))) :
    ∀ p : ℕ, Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p := by
  intro p x hx
  have he : (μ.cupWedgeMap (2 * p) ((hT.cupWedgeEquiv (2 * p)).symm x) : H^(2 * p)(X; ℚ)) = x :=
    (hT.cupWedgeEquiv (2 * p)).apply_symm_apply x
  have hv := (isHodgeClass_abelianVarietyCohomologyOf_iff hF hB hD hT p
    ((hT.cupWedgeEquiv (2 * p)).symm x)).mpr ((congrArg (· ∈ Hdg^p(X; ℚ)) he).mpr hx)
  exact (congrArg (· ∈ algebraicCycleClassSpan X p) he).mp ((isAlgebraicOf_iff p _).mp (h p _ hv))

omit [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] [GrpObj X] in
/-- The conclusion of `hdg_le_span_of_hodgeConjectureFor` is the inner statement of upstream's
`HodgeConjectureForAbelianVarietiesInDimensionLE`, for this `X`. -/
example (n : ℕ) (h : HodgeConjectureForAbelianVarietiesInDimensionLE n)
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] [GrpObj X]
    (hX : dim X.left ≤ n) : ∀ p : ℕ, Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p :=
  h X hX

end Transfer

section Restatements

variable {μ : CupProduct X}

/-- Recasting the degree of an exterior power commutes with the wedge map. -/
theorem CupProduct.cupWedgeMap_cast (μ : CupProduct X) {m n : ℕ} (h : m = n)
    (w : ⋀[ℚ]^m (HQ X 1)) : μ.cupWedgeMap n (h ▸ w) = HQ.castEquiv X h (μ.cupWedgeMap m w) := by
  subst h
  rfl

/-- The wedge map sends the `g`-th power of a polarization `ω` with `cupWedgeMap 2 ω = η` to the
Lefschetz power `L^g 1 = η^g`, where `1 = cupWedgeMap 0 1` (`CupProduct.cupWedgeMap_zero`). -/
theorem cupWedgeMap_polarizationPow (μ : CupProduct X) {η : HQ X 2} (ω : ⋀[ℚ]^2 (HQ X 1))
    (hω : μ.cupWedgeMap 2 ω = η) :
    ∀ (g : ℕ) (h : 0 + 2 * g = 2 * g),
      μ.cupWedgeMap (2 * g) (HodgeBlocks.polarizationPow ω g) =
        lefschetzPow X μ η g h (μ.cupWedgeMap 0 (exteriorPower.ιMulti ℚ 0 Fin.elim0))
  | 0, h => rfl
  | g + 1, h => by
    have e1 : μ.cupWedgeMap (2 * (g + 1)) (HodgeBlocks.polarizationPow ω (g + 1)) =
        μ.cup (by ring) (μ.cupWedgeMap (2 * g) (HodgeBlocks.polarizationPow ω g)) η := by
      refine (μ.cupWedgeMap_cast (m := 2 * g + 2) (by ring)
        (exteriorPower.wedge ℚ _ (2 * g) 2 (HodgeBlocks.polarizationPow ω g) ω)).trans ?_
      rw [μ.cupWedgeMap_wedge, CupProduct.castEquiv_cup, hω]
    rw [e1, cupWedgeMap_polarizationPow μ ω hω g (by ring),
      lefschetzPow_succ μ η g h (m' := 2 * g) (by ring) (by ring),
      μ.graded_comm (by ring) (by ring), Even.neg_one_pow ⟨2 * g, by ring⟩, one_smul]

variable [GrpObj X]

/-- Blocks `LefschetzOneOne` for the package, from upstream's Lefschetz (1,1). -/
theorem lefschetzOneOne_abelianVarietyCohomologyOf (hF : FiniteBetti X) (hB : BettiDeRhamIso X)
    (hD : HodgeDecomposition X) (hT : TorusCohomology μ) (h11 : LefschetzOneOneHyp) :
    letI := hT.finite
    HodgeBlocks.LefschetzOneOne (abelianVarietyCohomologyOf hF hB hD hT)
      (fun {m} => isAlgebraicOf μ (m := m)) := by
  let := hT.finite
  exact ⟨fun v hv => (isAlgebraicOf_iff 1 v).mpr
    (h11.holds X ((isHodgeClass_abelianVarietyCohomologyOf_iff hF hB hD hT 1 v).mp hv))⟩

/-- Blocks `PolarizationTopPowerNonzero` for the package, from Hard Lefschetz at `k = 0`
(`L^g : H^0 ≅ H^(2g)`) and `1 ≠ 0` in `H^0`. -/
theorem polarizationTopPowerNonzero_abelianVarietyCohomologyOf (hF : FiniteBetti X)
    (hB : BettiDeRhamIso X) (hD : HodgeDecomposition X) (hT : TorusCohomology μ) {η : HQ X 2}
    (hL : HardLefschetz X μ η) :
    letI := hT.finite
    HodgeBlocks.PolarizationTopPowerNonzero (abelianVarietyCohomologyOf hF hB hD hT)
      ((hT.cupWedgeEquiv 2).symm η) := by
  let := hT.finite
  refine ⟨fun h0 => unitClass_ne_zero' X ?_⟩
  have h : 0 + 2 * (dim X.left - 0) = 2 * dim X.left := by omega
  have hw := cupWedgeMap_polarizationPow μ ((hT.cupWedgeEquiv 2).symm η)
    (by rw [← hT.cupWedgeEquiv_apply, LinearEquiv.apply_symm_apply]) (dim X.left) h
  change HodgeBlocks.polarizationPow _ (dim X.left) = 0 at h0
  rw [h0, map_zero] at hw
  exact μ.cupWedgeMap_zero.symm.trans
    ((hL.bijective (Nat.zero_le _) h).1 (hw.symm.trans (map_zero _).symm))

/-- The Hard Lefschetz isomorphism `L = η ∪ - : H² ≅ H⁴` of an abelian threefold, as the Blocks
datum `HardLefschetzFromDegreeTwo` on the package, read on `⋀² H¹ ≅ ⋀⁴ H¹` through the torus
isomorphisms.

* `Lpow` is Hard Lefschetz at `k = 2` (`L^(3 − 2) : H² ≅ H⁴`).
* `Lpow_isHodge`, forward: `L` sends the `(1, 1)` piece to the `(2, 2)` piece, from O5
  (`CupFiltered`) and `η ∈ Hdg^1`, which is C8 applied to the divisor class `η`
  (`baseChange_lefschetzPow_mem_hodgePiece`). Backward: reflection of Hodge classes,
  `lefschetzReflectsHodge_of_cupFiltered` (C2, C4, O5, Hard Lefschetz, `η ∈ Hdg^1`).
* `Lpow_isAlgebraic`: divisor closure (`AlgebraicTimesDivisor`), iterated by
  `lefschetzPow_mem_algebraicCycleClassSpan`. -/
noncomputable def hardLefschetzFromDegreeTwoOf (hF : FiniteBetti X) (hB : BettiDeRhamIso X)
    (hD : HodgeDecomposition X) (hT : TorusCohomology μ) (hH : CycleClassIsHodge X) {η : HQ X 2}
    (hA : AlgebraicTimesDivisor X μ η) (hL : HardLefschetz X μ η) (hC : CupFiltered X μ)
    (hg : dim X.left = 3) :
    letI := hT.finite
    HodgeBlocks.HardLefschetzFromDegreeTwo (abelianVarietyCohomologyOf hF hB hD hT)
      (fun {m} => isAlgebraicOf μ (m := m)) (p2 := 2) (show dim X.left = 2 + 1 by omega)
      (by omega) :=
  letI := hT.finite
  have hh : 2 + 2 * (dim X.left - 2) = 2 * 2 := by omega
  let L : HQ X 2 ≃ₗ[ℚ] HQ X (2 * 2) :=
    LinearEquiv.ofBijective (lefschetzPow X μ η (dim X.left - 2) hh)
      (hL.bijective (by omega) hh)
  have hLpow : ∀ v, μ.cupWedgeMap (2 * 2)
      (((hT.cupWedgeEquiv 2).trans (L.trans (hT.cupWedgeEquiv (2 * 2)).symm)) v) =
      lefschetzPow X μ η (dim X.left - 2) hh (μ.cupWedgeMap 2 v) := fun v => by
    rw [← hT.cupWedgeEquiv_apply, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
      LinearEquiv.apply_symm_apply]
    rfl
  have hηH : (η : H^(2 * 1)(X; ℚ)) ∈ Hdg^1(X; ℚ) := hH.le 1 hA.η_mem
  { Lpow := (hT.cupWedgeEquiv 2).trans (L.trans (hT.cupWedgeEquiv (2 * 2)).symm)
    Lpow_isHodge := fun {v} => by
      refine (isHodgeClass_abelianVarietyCohomologyOf_iff hF hB hD hT 1 v).trans
        (Iff.trans ?_ (isHodgeClass_abelianVarietyCohomologyOf_iff hF hB hD hT 2 _).symm)
      rw [hLpow]
      refine ⟨fun hv => ?_, fun hv =>
        (lefschetzReflectsHodge_of_cupFiltered hB hD hC hL hηH).reflects (p := 1) hh (by omega)
          _ hv⟩
      have hη' : bettiDeRhamHQ X 2 (1 ⊗ₜ η) ∈ hodgePiece X 1 1 2 := by
        have := (mem_hodgeClasses_iff_tmul_mem 1 η).mp hηH
        simpa [cohomologyHodgePiece] using this
      have hv' : bettiDeRhamHQ X 2 (1 ⊗ₜ μ.cupWedgeMap 2 v) ∈ hodgePiece X 1 1 2 := by
        have := (mem_hodgeClasses_iff_tmul_mem 1 _).mp hv
        simpa [cohomologyHodgePiece] using this
      have key := baseChange_lefschetzPow_mem_hodgePiece hC hη' (dim X.left - 2) hh 1 1 _ hv'
      rw [LinearMap.baseChange_tmul] at key
      rw [mem_hodgeClasses_iff_tmul_mem, cohomologyHodgePiece,
        ite_eq_left_of_eq_true _ _ (eq_true (by norm_num)), Submodule.mem_comap]
      convert key using 2 <;> push_cast <;> omega
    Lpow_isAlgebraic := fun {v} hv => by
      have hv := (isAlgebraicOf_iff 1 v).mp hv
      refine (isAlgebraicOf_iff 2 _).mpr ?_
      rw [hLpow]
      exact lefschetzPow_mem_algebraicCycleClassSpan hA (dim X.left - 2) 1 2 hh _ hv }

/-- The degree argument for an abelian curve: the unit spans degree zero,
Lefschetz `(1,1)` handles degree two, and higher even degrees vanish. -/
theorem hdg_le_span_g1_of_degree_one (hT : TorusCohomology μ)
    (h11 : Hdg^1(X; ℚ) ≤ algebraicCycleClassSpan X 1) (hg : dim X.left = 1) :
    ∀ p : ℕ, Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p := by
  letI := hT.finite
  intro p x hx
  rcases p with _ | _ | p
  · let v := (hT.cupWedgeEquiv 0).symm x
    let c := exteriorPower.zeroEquiv ℚ (HQ X 1) v
    have hv : v = c • (exteriorPower.ιMulti ℚ 0 Fin.elim0 : ⋀[ℚ]^0 (HQ X 1)) := by
      apply (exteriorPower.zeroEquiv ℚ (HQ X 1)).injective
      simp [c]
    have he : μ.cupWedgeMap 0 v = x := (hT.cupWedgeEquiv 0).apply_symm_apply x
    rw [← he, hv, map_smul, CupProduct.cupWedgeMap_zero]
    exact Submodule.smul_mem _ c unitClass_mem_algebraicCycleClassSpan
  · exact h11 hx
  · haveI : Subsingleton (⋀[ℚ]^(2 * (p + 2)) (HQ X 1)) := by
      apply exteriorPower.subsingleton_of_span_eq_top_of_card_lt
        (ι := Fin (Module.finrank ℚ (HQ X 1))) (Module.finBasis ℚ (HQ X 1))
      · exact (Module.finBasis ℚ (HQ X 1)).span_eq
      · simp only [Nat.card_fin, hT.finrank_eq, hg]
        omega
    have hsub : Subsingleton (HQ X (2 * (p + 2))) :=
      (hT.cupWedgeEquiv _).symm.toEquiv.subsingleton
    have hx0 : x = 0 := hsub.elim x 0
    rw [hx0]
    exact Submodule.zero_mem _

/-- The Hodge conjecture for an abelian curve, by the degree argument.
The remaining package binders are retained for interface compatibility.
Source: the degree argument of `HodgeBlocks.hodgeConjecture_g1`, using the
unit class, Lefschetz `(1,1)` and exterior-power vanishing directly.

Checks: F-1690

HC no distance; AV milestone no distance. -/
@[hodge_milestone] theorem hdg_le_span_abelian_g1 (hF : FiniteBetti X) (hB : BettiDeRhamIso X)
    (hD : HodgeDecomposition X) (hT : TorusCohomology μ)
    (hH : CycleClassIsHodge X) (h11 : LefschetzOneOneHyp) (hg : dim X.left = 1) :
    ∀ p : ℕ, Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p := by
  exact hdg_le_span_g1_of_degree_one hT (h11.holds X) hg

/-- **The Hodge conjecture for an abelian surface, against upstream's `Hdg^p`.** Under the
hypotheses in the table below, for an abelian variety `X` of dimension two, `Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p` for every `p`: the
transfer applied to `HodgeBlocks.hodgeConjecture_g2`, with polarization the class of `η` in
`⋀² H¹`.

| hypothesis | role |
| --- | --- |
| `FiniteBetti`, `BettiDeRhamIso`, `HodgeDecomposition` (C1, C2, C4) | the Hodge structures of the package |
| `TorusCohomology` (C7) | `H^m ≅ ⋀^m H¹`, so the package is the cohomology of `X` |
| `CycleClassMultiplicative` (C9) | `IsCycleClassPredicate.wedge_mem` |
| `CycleClassIsHodge` (C8) | `IsCycleClassPredicate.isHodge` |
| `AlgebraicTimesDivisor` (O6) | only `η_mem`: `η` is a divisor class, so the polarization is algebraic |
| `HardLefschetz` (O3) | at `k = 0`, `L^2 : H^0 ≅ H^4`, giving `PolarizationTopPowerNonzero` with `1 ≠ 0` |
| `LefschetzOneOneHyp` | Blocks `LefschetzOneOne` |
| `dim X.left = 2` | the case |

`AlgebraicTimesDivisor.cup_mem` is not used; it follows from `CycleClassMultiplicative` and
`η_mem` anyway (`algebraicTimesDivisor_of_cycleClassMultiplicative`). The case `g = 2` is
classical, so this is no distance to the abelian-variety milestone; its value is that the transfer
is exercised end to end.

Source: a restatement of the Blocks theorem `HodgeBlocks.hodgeConjecture_g2`
(`HodgeLean/Blocks/Milestone/HardLefschetz.lean`) through the transfer
`hdg_le_span_of_hodgeConjectureFor` (F-1689); the published inputs are the hypotheses in the
table, each with its own `Source:` line.

Checks: F-1690 -/
@[hodge_milestone] theorem hdg_le_span_abelian_g2 (hF : FiniteBetti X) (hB : BettiDeRhamIso X)
    (hD : HodgeDecomposition X) (hT : TorusCohomology μ) (hM : CycleClassMultiplicative μ)
    (hH : CycleClassIsHodge X) {η : HQ X 2} (hA : AlgebraicTimesDivisor X μ η)
    (hL : HardLefschetz X μ η) (h11 : LefschetzOneOneHyp) (hg : dim X.left = 2) :
    ∀ p : ℕ, Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p := by
  let := hT.finite
  exact hdg_le_span_of_hodgeConjectureFor hF hB hD hT
    (HodgeBlocks.hodgeConjecture_g2 _ _ hg (cycleClassPredicateOf hF hB hD hT hM hH hA.η_mem)
      (lefschetzOneOne_abelianVarietyCohomologyOf hF hB hD hT h11)
      (polarizationTopPowerNonzero_abelianVarietyCohomologyOf hF hB hD hT hL))

/-- **The Hodge conjecture for an abelian threefold, against upstream's `Hdg^p`.** Under the
hypotheses in the table below, for an abelian variety `X` of dimension three, `Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p` for every `p`: the
transfer applied to `HodgeBlocks.hodgeConjecture_g3`, with `HardLefschetzFromDegreeTwo` built by
`hardLefschetzFromDegreeTwoOf`.

| hypothesis | role |
| --- | --- |
| `FiniteBetti`, `BettiDeRhamIso`, `HodgeDecomposition` (C1, C2, C4) | the Hodge structures of the package; C2 and C4 also give reflection |
| `TorusCohomology` (C7) | `H^m ≅ ⋀^m H¹`, so the package is the cohomology of `X` |
| `CycleClassMultiplicative` (C9) | `IsCycleClassPredicate.wedge_mem` |
| `CycleClassIsHodge` (C8) | `IsCycleClassPredicate.isHodge`, and `η ∈ Hdg^1` |
| `AlgebraicTimesDivisor` (O6) | `η` is a divisor class; `L` preserves algebraic classes (`Lpow_isAlgebraic`) |
| `HardLefschetz` (O3) | `k = 0`: `PolarizationTopPowerNonzero`; `k = 2`: `Lpow : H² ≅ H⁴` |
| `CupFiltered` (O5) | `Lpow_isHodge`, both directions |
| `LefschetzOneOneHyp` | Blocks `LefschetzOneOne` |
| `dim X.left = 3` | the case |

The case `g = 3` is classical, so this is no distance to the abelian-variety milestone; its value
is that the transfer is exercised end to end.

Source: a restatement of the Blocks theorem `HodgeBlocks.hodgeConjecture_g3`
(`HodgeLean/Blocks/Milestone/HardLefschetz.lean`) through the transfer
`hdg_le_span_of_hodgeConjectureFor` (F-1689); the published inputs are the hypotheses in the
table, each with its own `Source:` line.

Checks: F-1690 -/
@[hodge_milestone] theorem hdg_le_span_abelian_g3 (hF : FiniteBetti X) (hB : BettiDeRhamIso X)
    (hD : HodgeDecomposition X) (hT : TorusCohomology μ) (hM : CycleClassMultiplicative μ)
    (hH : CycleClassIsHodge X) {η : HQ X 2} (hA : AlgebraicTimesDivisor X μ η)
    (hL : HardLefschetz X μ η) (hC : CupFiltered X μ) (h11 : LefschetzOneOneHyp)
    (hg : dim X.left = 3) :
    ∀ p : ℕ, Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p := by
  let := hT.finite
  exact hdg_le_span_of_hodgeConjectureFor hF hB hD hT
    (HodgeBlocks.hodgeConjecture_g3 _ _ hg (cycleClassPredicateOf hF hB hD hT hM hH hA.η_mem)
      (lefschetzOneOne_abelianVarietyCohomologyOf hF hB hD hT h11)
      (hardLefschetzFromDegreeTwoOf hF hB hD hT hH hA hL hC hg)
      (polarizationTopPowerNonzero_abelianVarietyCohomologyOf hF hB hD hT hL))

end Restatements

end HodgeLean.RealDefs
