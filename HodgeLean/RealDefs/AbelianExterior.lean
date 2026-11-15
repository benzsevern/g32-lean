import HodgeLean.RealDefs.AbelianVariety
import HodgeLean.Blocks.Weil.WeilTheoremHodge

/-! # The abelian-variety package is the exterior power of its weight-one part

Roadmap `docs/roadmap/layer3.md` §3 C1, C6, C7 and O7.

* `finiteBetti_of_torusCohomology` (C1) and `vanishingAboveTop_of_torusCohomology` (O7): for an
  abelian `X`, finite Betti numbers and vanishing above degree `2 · dim X` follow from the torus
  theorem (C7) alone.
* `hodgeConjectureFor_of_hdg_le_span`: the converse of the transfer
  `hdg_le_span_of_hodgeConjectureFor`, and `hodgeConjectureFor_iff_hdg_le_span`.
-/

open CategoryTheory AlgebraicGeometry ComplexPoint TopologicalSpace
open scoped TensorProduct

namespace HodgeLean.RealDefs

variable {X : Over (Spec ↧ℂ)} [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
variable {μ : CupProduct X} [GrpObj X]

section Torus

/-- **Finite Betti numbers (C1) for an abelian `X`**, from the torus theorem (C7): `H¹` is
finite-dimensional, so is `⋀^m H¹`, and `cupWedgeEquiv m` identifies it with `H^m`.

Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, Lemma 1.3.1 (through `TorusCohomology`).

| hypothesis | roadmap |
| --- | --- |
| `hT : TorusCohomology μ` | C7 |

Relation to the goal: HC no distance; AV milestone no distance (a premise of the package, derived
rather than assumed). -/
theorem finiteBetti_of_torusCohomology (hT : TorusCohomology μ) : FiniteBetti X := by
  refine ⟨fun n => ?_⟩
  let := hT.finite
  exact Module.Finite.equiv (hT.cupWedgeEquiv n)

/-- **Vanishing above the top degree (O7) for an abelian `X`**, from the torus theorem (C7): for
`m > 2 · dim X.left = finrank H¹`, `⋀^m H¹ = 0`, and `cupWedgeEquiv m` identifies it with `H^m`.

Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, Lemma 1.3.1 (through `TorusCohomology`).

| hypothesis | roadmap |
| --- | --- |
| `hT : TorusCohomology μ` | C7 |

Relation to the goal: HC no distance; AV milestone no distance. -/
theorem vanishingAboveTop_of_torusCohomology (hT : TorusCohomology μ) : VanishingAboveTop X := by
  refine ⟨fun m hm => ?_⟩
  let := hT.finite
  have : Subsingleton (⋀[ℚ]^m (HQ X 1)) := by
    apply exteriorPower.subsingleton_of_span_eq_top_of_card_lt
      (ι := Fin (Module.finrank ℚ (HQ X 1))) (Module.finBasis ℚ (HQ X 1))
    · exact (Module.finBasis ℚ (HQ X 1)).span_eq
    · simpa [hT.finrank_eq] using hm
  exact (hT.cupWedgeEquiv m).symm.toEquiv.subsingleton

end Torus

section Transfer

/-- **The converse of the transfer (C10).** Under C1, C2, C4 and C7, upstream's Hodge conjecture
for `X` (`Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p` for every `p`) gives the Blocks statement
`HodgeConjectureFor` for the package `abelianVarietyCohomologyOf` and the predicate
`isAlgebraicOf μ`. With `hdg_le_span_of_hodgeConjectureFor` this makes the transfer an
equivalence (`hodgeConjectureFor_iff_hdg_le_span`), so the Blocks statement for the package is
neither weaker nor stronger than upstream's for `X`.

Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, Lemma 1.3.1 (through `TorusCohomology`); the converse itself is proved here, with no further input.

| hypothesis | roadmap |
| --- | --- |
| `hF : FiniteBetti X` | C1 |
| `hB : BettiDeRhamIso X` | C2 |
| `hD : HodgeDecomposition X` | C4 |
| `hT : TorusCohomology μ` | C7 |
| `h : ∀ p, Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p` | the premise: upstream's statement for `X` |

Relation to the goal: HC no distance; AV milestone no distance (it certifies that the transfer
loses nothing). -/
theorem hodgeConjectureFor_of_hdg_le_span (hF : FiniteBetti X) (hB : BettiDeRhamIso X)
    (hD : HodgeDecomposition X) (hT : TorusCohomology μ)
    (h : ∀ p : ℕ, Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p) :
    letI := hT.finite
    HodgeBlocks.HodgeConjectureFor (abelianVarietyCohomologyOf hF hB hD hT)
      (fun {m} => isAlgebraicOf μ (m := m)) := by
  intro p v hv
  exact (isAlgebraicOf_iff p v).mpr
    (h p ((isHodgeClass_abelianVarietyCohomologyOf_iff hF hB hD hT p v).mp hv))

/-- **The transfer is an equivalence (C10).** Under C1, C2, C4 and C7, the Blocks statement
`HodgeConjectureFor` for the package `abelianVarietyCohomologyOf` and `isAlgebraicOf μ` holds
exactly when upstream's `Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p` holds for every `p`.

Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, Lemma 1.3.1 (through `TorusCohomology`).

| hypothesis | roadmap |
| --- | --- |
| `hF : FiniteBetti X` | C1 |
| `hB : BettiDeRhamIso X` | C2 |
| `hD : HodgeDecomposition X` | C4 |
| `hT : TorusCohomology μ` | C7 |

Relation to the goal: HC no distance; AV milestone no distance. -/
theorem hodgeConjectureFor_iff_hdg_le_span (hF : FiniteBetti X) (hB : BettiDeRhamIso X)
    (hD : HodgeDecomposition X) (hT : TorusCohomology μ) :
    letI := hT.finite
    HodgeBlocks.HodgeConjectureFor (abelianVarietyCohomologyOf hF hB hD hT)
        (fun {m} => isAlgebraicOf μ (m := m)) ↔
      ∀ p : ℕ, Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p :=
  ⟨hdg_le_span_of_hodgeConjectureFor hF hB hD hT, hodgeConjectureFor_of_hdg_le_span hF hB hD hT⟩

end Transfer

section ExteriorOfWeightOne

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]

/-- **`IsExteriorOfWeightOne`** (roadmap `docs/roadmap/layer3.md` §3 C6): the Hodge structure
`S.cohomology m` of a Blocks package is, in every degree `m`, the `m`-th exterior power of its
weight-one part `S.weight1`: the two have the same `(p, q)` piece for every `(p, q)`.

`S.weight1.exteriorPower m` has weight `m * 1` and `S.cohomology m` has weight `m`; the statement
compares them along `weightCast` for `(m : ℤ) * 1 = m`, which changes no piece (`weightCast_H`).
The examples below unfold the weight at `m = 0` and `m = 2`.

This is the compatibility that the referee disclosure of `HodgeBlocks.AbelianVarietyCohomology`
says no field enforces: that `cohomology m` is the Hodge structure induced on `⋀^m` of `weight1`.
For the package `abelianVarietyCohomologyOf` of a real abelian `X`,
`isExteriorOfWeightOne_of_cupFiltered` proves it **under C1, C2, C4, C7 and O5 (`CupFiltered`),
which remain hypotheses**. So the compatibility half of the disclosure (left open in
`abelianVarietyCohomologyOf`'s docstring) is retired for that package only, and only
conditionally. The disclosure still applies to every other `AbelianVarietyCohomology`. -/
def AbelianVarietyCohomology.IsExteriorOfWeightOne
    (S : HodgeBlocks.AbelianVarietyCohomology V) : Prop :=
  ∀ (m : ℕ) (pq : ℤ × ℤ), (S.cohomology m).H pq =
    (HodgeBlocks.WeilAction.weightCast (V := ⋀[ℚ]^m V) (by ring)
      (S.weight1.exteriorPower (V := V) m)).H pq

/-- At `m = 0` the exterior power has weight `0 * 1 = 0`, the weight of `cohomology 0`. -/
noncomputable example (S : HodgeBlocks.AbelianVarietyCohomology V) :
    HodgeBlocks.QHodgeStructure 0 (⋀[ℚ]^0 V) :=
  S.weight1.exteriorPower (V := V) 0

/-- At `m = 2` the exterior power has weight `2 * 1 = 2`, the weight of `cohomology 2`: its
`(3, 0)` and `(1, 0)` pieces vanish, and `IsExteriorOfWeightOne` matches `(1, 1)` pieces with no
shift. -/
noncomputable example (S : HodgeBlocks.AbelianVarietyCohomology V) :
    HodgeBlocks.QHodgeStructure 2 (⋀[ℚ]^2 V) :=
  S.weight1.exteriorPower (V := V) 2

example (S : HodgeBlocks.AbelianVarietyCohomology V) :
    (S.weight1.exteriorPower (V := V) 2).H (3, 0) = ⊥ ∧
      (S.weight1.exteriorPower (V := V) 2).H (1, 0) = ⊥ :=
  ⟨(S.weight1.exteriorPower (V := V) 2).supported (3, 0) (by norm_num),
    (S.weight1.exteriorPower (V := V) 2).supported (1, 0) (by norm_num)⟩

example (S : HodgeBlocks.AbelianVarietyCohomology V)
    (h : AbelianVarietyCohomology.IsExteriorOfWeightOne S) :
    (S.cohomology 2).H (1, 1) = (S.weight1.exteriorPower (V := V) 2).H (1, 1) := by
  rw [h 2 (1, 1), HodgeBlocks.WeilAction.weightCast_H]

/-- At `m = 0`, `IsExteriorOfWeightOne` matches the `(0, 0)` pieces with no shift. -/
example (S : HodgeBlocks.AbelianVarietyCohomology V)
    (h : AbelianVarietyCohomology.IsExteriorOfWeightOne S) :
    (S.cohomology 0).H (0, 0) = (S.weight1.exteriorPower (V := V) 0).H (0, 0) := by
  rw [h 0 (0, 0), HodgeBlocks.WeilAction.weightCast_H]

/-- At `m = 2`, `IsExteriorOfWeightOne` matches the `(2, 0)` pieces with no shift. -/
example (S : HodgeBlocks.AbelianVarietyCohomology V)
    (h : AbelianVarietyCohomology.IsExteriorOfWeightOne S) :
    (S.cohomology 2).H (2, 0) = (S.weight1.exteriorPower (V := V) 2).H (2, 0) := by
  rw [h 2 (2, 0), HodgeBlocks.WeilAction.weightCast_H]

end ExteriorOfWeightOne

section CupMultiC

namespace CupProduct

omit [GrpObj X]

/-- One step of the complexified cup of `m` degree-one classes: `a ↦ cupC a ∘ f`, `ℂ`-linear in
`a`. -/
noncomputable def cupLeftMultiC (μ : CupProduct X) (m : ℕ)
    (f : MultilinearMap ℂ (fun _ : Fin m => ℂ ⊗[ℚ] HQ X 1) (ℂ ⊗[ℚ] HQ X m)) :
    ℂ ⊗[ℚ] HQ X 1 →ₗ[ℂ]
      MultilinearMap ℂ (fun _ : Fin m => ℂ ⊗[ℚ] HQ X 1) (ℂ ⊗[ℚ] HQ X (m + 1)) where
  toFun a := (μ.cupC (Nat.add_comm 1 m) a).compMultilinearMap f
  map_add' a b := by ext; simp
  map_smul' c a := by ext; simp

/-- The base change of `cupMulti` to `ℂ`: the `ℂ`-multilinear map
`(x₁, …, x_m) ↦ x₁ ∪ (x₂ ∪ ⋯ ∪ (x_m ∪ 1))` on `ℂ ⊗[ℚ] H¹`, built from `cupC`. -/
noncomputable def cupMultiC (μ : CupProduct X) :
    ∀ m : ℕ, MultilinearMap ℂ (fun _ : Fin m => ℂ ⊗[ℚ] HQ X 1) (ℂ ⊗[ℚ] HQ X m)
  | 0 => MultilinearMap.constOfIsEmpty ℂ _ ((1 : ℂ) ⊗ₜ[ℚ] (unitClass X : HQ X 0))
  | m + 1 => (μ.cupLeftMultiC m (cupMultiC μ m)).uncurryLeft

theorem cupMultiC_zero (μ : CupProduct X) (v : Fin 0 → ℂ ⊗[ℚ] HQ X 1) :
    μ.cupMultiC 0 v = (1 : ℂ) ⊗ₜ[ℚ] (unitClass X : HQ X 0) :=
  rfl

/-- The base-changed form of the recursion `cupMulti_succ`: one more factor is one more `cupC`. -/
theorem cupMultiC_succ (μ : CupProduct X) (m : ℕ) (v : Fin (m + 1) → ℂ ⊗[ℚ] HQ X 1) :
    μ.cupMultiC (m + 1) v = μ.cupC (Nat.add_comm 1 m) (v 0) (μ.cupMultiC m (Fin.tail v)) :=
  rfl

/-- On rational vectors, `cupMultiC` is the base change of `cupMulti`. -/
theorem cupMultiC_tmul (μ : CupProduct X) :
    ∀ (m : ℕ) (a : Fin m → HQ X 1),
      μ.cupMultiC m (fun i => (1 : ℂ) ⊗ₜ[ℚ] a i) = (1 : ℂ) ⊗ₜ[ℚ] μ.cupMulti m a
  | 0, _ => rfl
  | m + 1, a => by
    rw [cupMultiC_succ]
    have ih := cupMultiC_tmul μ m (Fin.tail a)
    change μ.cupC _ ((1 : ℂ) ⊗ₜ[ℚ] a 0)
      (μ.cupMultiC m (fun i => (1 : ℂ) ⊗ₜ[ℚ] Fin.tail a i)) = _
    rw [ih, cupC_tmul, one_mul]
    rfl

end CupProduct

omit [GrpObj X] in
/-- **Step 1 of the compatibility.** With the cup product respecting the Hodge filtration (O5),
the complexified cup product of `m` degree-one classes, the `i`-th of de Rham type `d i`, has de
Rham type the total bidegree `∑ d i`. Induction on `m` through `cupMultiC_succ`, with
`CupFiltered.mem_hodgePiece` (which carries the conjugate side, `CupFiltered.mem_conj`) for each
cup; the empty product is the unit, of type `(0, 0)`. -/
theorem CupFiltered.bettiDeRhamHQ_cupMultiC_mem (hC : CupFiltered X μ) :
    ∀ (m : ℕ) (d : Fin m → ℤ × ℤ) (v : Fin m → ℂ ⊗[ℚ] HQ X 1),
      (∀ i, bettiDeRhamHQ X 1 (v i) ∈ hodgePiece X (d i).1 (d i).2 1) →
      bettiDeRhamHQ X m (μ.cupMultiC m v) ∈
        hodgePiece X (HodgeBlocks.totalBidegree m d).1 (HodgeBlocks.totalBidegree m d).2 m
  | 0, d, v, _ => by
    simp only [HodgeBlocks.totalBidegree, Finset.univ_eq_empty, Finset.sum_empty]
    refine ⟨?_, ?_⟩
    · rw [hodgeFiltration_eq_top_of_nonpos X le_rfl]
      exact Submodule.mem_top
    · refine (mem_conjHodgeFiltrationComplexSubmodule X _).mpr ?_
      rw [hodgeFiltration_eq_top_of_nonpos X le_rfl]
      exact Submodule.mem_top
  | m + 1, d, v, hv => by
    rw [CupProduct.cupMultiC_succ]
    have := hC.mem_hodgePiece (Nat.add_comm 1 m) (v 0) _ (hv 0)
      (bettiDeRhamHQ_cupMultiC_mem hC m (Fin.tail d) (Fin.tail v) (fun i => hv i.succ))
    convert this using 2 <;> simp [HodgeBlocks.totalBidegree, Fin.sum_univ_succ, Fin.tail]

/-- The complexified torus isomorphism, read on `⋀^m (ℂ ⊗ H¹)` through
`exteriorPowerBaseChangeEquiv`, sends `x₁ ∧ ⋯ ∧ x_m` to `cupMultiC m x`. Both sides are
`ℂ`-multilinear in `x`, and they agree on the basis `1 ⊗ eᵢ` by `cupMultiC_tmul`. -/
theorem TorusCohomology.complexificationCongr_symm_ιMulti (hT : TorusCohomology μ) (m : ℕ)
    (v : Fin m → ℂ ⊗[ℚ] HQ X 1) :
    letI := hT.finite
    letI := (finiteBetti_of_torusCohomology hT).finite m
    HodgeBlocks.QHodgeStructure.complexificationCongr (V := ⋀[ℚ]^m (HQ X 1)) (W := HQ X m)
      (hT.cupWedgeEquiv m) ((HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv m).symm
        (exteriorPower.ιMulti ℂ m v)) = μ.cupMultiC m v := by
  let := hT.finite
  let := (finiteBetti_of_torusCohomology hT).finite m
  let e := Module.finBasis ℚ (HQ X 1)
  have key : (((HodgeBlocks.QHodgeStructure.complexificationCongr (V := ⋀[ℚ]^m (HQ X 1))
      (W := HQ X m) (hT.cupWedgeEquiv m)).toLinearMap ∘ₗ
      (HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv (V := HQ X 1) m).symm.toLinearMap
      ).compAlternatingMap (exteriorPower.ιMulti ℂ m)).toMultilinearMap = μ.cupMultiC m := by
    refine Module.Basis.ext_multilinear (fun _ => e.baseChange ℂ) fun σ => ?_
    simp only [Module.Basis.baseChange_apply, AlternatingMap.coe_multilinearMap,
      LinearMap.compAlternatingMap_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [CupProduct.cupMultiC_tmul μ m (fun i => e (σ i)),
      ← HodgeBlocks.complexifyWedge_ιMulti (V := HQ X 1) m (fun i => e (σ i)),
      ← HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv_tmul, LinearEquiv.symm_apply_apply,
      HodgeBlocks.QHodgeStructure.complexificationCongr_tmul, TorusCohomology.cupWedgeEquiv_apply,
      CupProduct.cupWedgeMap_ιMulti]
  exact DFunLike.congr_fun key v

end CupMultiC

section WedgePiece

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]

/-- The span, in `ℂ ⊗[ℚ] ⋀^m V`, of the wedges `x₁ ∧ ⋯ ∧ x_m` (moved by
`exteriorPowerBaseChangeEquiv`) with each `xᵢ` in a piece `M.H (d i)` and total bidegree `pq`. -/
noncomputable def wedgePiece (M : HodgeBlocks.QHodgeStructure 1 V) (m : ℕ) (pq : ℤ × ℤ) :
    Submodule ℂ (ℂ ⊗[ℚ] ⋀[ℚ]^m V) :=
  Submodule.span ℂ {x | ∃ (d : Fin m → ℤ × ℤ) (v : Fin m → ℂ ⊗[ℚ] V),
    HodgeBlocks.totalBidegree m d = pq ∧ (∀ i, v i ∈ M.H (d i)) ∧
      (HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv m).symm
        (exteriorPower.ιMulti ℂ m v) = x}

/-- Each wedge span lies in its exterior-power piece (`exteriorPower_ιMulti_mem_exteriorPowerH_map`). -/
theorem wedgePiece_le (M : HodgeBlocks.QHodgeStructure 1 V) (m : ℕ) (pq : ℤ × ℤ) :
    wedgePiece M m pq ≤ M.exteriorPowerH (V := V) m pq := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨d, v, hd, hv, rfl⟩
  exact (Submodule.mem_map_equiv _).mp
    (HodgeBlocks.WeilAction.exteriorPower_ιMulti_mem_exteriorPowerH_map M m pq d v hd hv)

/-- The wedge spans cover `ℂ ⊗[ℚ] ⋀^m V`: `ℂ ⊗ V` is the sum of the pieces `M.H d`, and `ιMulti`
is multilinear and spans. -/
theorem iSup_wedgePiece (M : HodgeBlocks.QHodgeStructure 1 V) (m : ℕ) :
    ⨆ pq, wedgePiece M m pq = ⊤ := by
  classical
  let ebc := HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv (V := V) m
  have main : ∀ v : Fin m → ℂ ⊗[ℚ] V,
      ebc.symm (exteriorPower.ιMulti ℂ m v) ∈ ⨆ pq, wedgePiece M m pq := by
    intro v
    have hv : ∀ i, ∃ f : ℤ × ℤ →₀ ℂ ⊗[ℚ] V, (∀ j, f j ∈ M.H j) ∧
        (f.sum fun _ x => x) = v i := fun i =>
      (Submodule.mem_iSup_iff_exists_finsupp _ _).mp
        (M.isInternal.submodule_iSup_eq_top ▸ Submodule.mem_top)
    choose f hf hsum using hv
    have hv' : v = fun i => ∑ j ∈ (f i).support, f i j := funext fun i => (hsum i).symm
    rw [hv', ← AlternatingMap.coe_multilinearMap, MultilinearMap.map_sum_finset, map_sum]
    refine Submodule.sum_mem _ fun r _ => ?_
    refine Submodule.mem_iSup_of_mem (HodgeBlocks.totalBidegree m r) (Submodule.subset_span ?_)
    exact ⟨r, fun i => f i (r i), rfl, fun i => hf i (r i), rfl⟩
  refine eq_top_iff.mpr fun x _ => ?_
  have hy : ebc x ∈ Submodule.span ℂ (Set.range (exteriorPower.ιMulti ℂ m)) := by
    rw [exteriorPower.ιMulti_span]
    exact Submodule.mem_top
  have : ∀ y ∈ Submodule.span ℂ (Set.range (exteriorPower.ιMulti ℂ (M := ℂ ⊗[ℚ] V) m)),
      ebc.symm y ∈ ⨆ pq, wedgePiece M m pq := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨v, rfl⟩ := hy
      exact main v
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
    | smul c y _ hy => rw [map_smul]; exact Submodule.smul_mem _ c hy
  simpa using this _ hy

/-- **Step 2 of the compatibility.** Each exterior-power piece is the span of its wedges: the wedge
spans lie in the pieces and cover the space, and the pieces are independent
(`exteriorPowerH_isInternal`). -/
theorem exteriorPowerH_eq_wedgePiece (M : HodgeBlocks.QHodgeStructure 1 V) (m : ℕ)
    (pq : ℤ × ℤ) : M.exteriorPowerH (V := V) m pq = wedgePiece M m pq := by
  refine le_antisymm (fun x hx => ?_) (wedgePiece_le M m pq)
  exact mem_of_map_mem_of_iSupIndep_of_map_le (iSup_wedgePiece M m)
    (M.exteriorPowerH_isInternal (V := V) m).submodule_iSupIndep (g := id)
    Function.injective_id (f := LinearMap.id) Function.injective_id
    (fun i => by rw [Submodule.map_id]; exact wedgePiece_le M m i) hx

end WedgePiece

section Compatibility

/-- **Step 3 of the compatibility, on generators.** Under O5, the complexified torus isomorphism
sends each wedge span of the weight-one structure of `H¹` into the matching candidate piece of
`ℂ ⊗ H^m`. A generator goes to `cupMultiC m v` (`complexificationCongr_symm_ιMulti`), which is of
the total type by step 1 when every `v i` sits on the line `p + q = 1`; otherwise some `v i` lies
in a `⊥` piece, so `v i = 0` and the generator is `0`. -/
theorem map_wedgePiece_le_cohomologyHodgePiece (hF : FiniteBetti X) (hB : BettiDeRhamIso X)
    (hD : HodgeDecomposition X) (hT : TorusCohomology μ) (hC : CupFiltered X μ) (m : ℕ)
    (pq : ℤ × ℤ) :
    letI := hT.finite
    letI := (finiteBetti_of_torusCohomology hT).finite m
    (wedgePiece (cohomologyHodgeStructure hF hB hD 1) m pq).map
      (HodgeBlocks.QHodgeStructure.complexificationCongr (V := ⋀[ℚ]^m (HQ X 1)) (W := HQ X m)
        (hT.cupWedgeEquiv m)).toLinearMap ≤ cohomologyHodgePiece X m pq := by
  let := hT.finite
  let := (finiteBetti_of_torusCohomology hT).finite m
  rw [Submodule.map_le_iff_le_comap, wedgePiece, Submodule.span_le]
  rintro _ ⟨d, v, rfl, hv, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_comap, LinearEquiv.coe_coe,
    hT.complexificationCongr_symm_ιMulti]
  have hv' : ∀ i, v i ∈ cohomologyHodgePiece X 1 (d i) := hv
  by_cases hall : ∀ i, (d i).1 + (d i).2 = ((1 : ℕ) : ℤ)
  · have hpq : (HodgeBlocks.totalBidegree m d).1 + (HodgeBlocks.totalBidegree m d).2 =
        (m : ℤ) := by
      simp only [HodgeBlocks.totalBidegree]
      rw [← Finset.sum_add_distrib]
      simp [hall]
    simp only [cohomologyHodgePiece, hpq, ↓reduceIte, Submodule.mem_comap]
    refine hC.bettiDeRhamHQ_cupMultiC_mem m d v fun i => ?_
    have := hv' i
    simp only [cohomologyHodgePiece, hall i, ↓reduceIte, Submodule.mem_comap] at this
    exact this
  · obtain ⟨i, hi⟩ := not_forall.mp hall
    have := hv' i
    simp only [cohomologyHodgePiece, hi, ↓reduceIte] at this
    rw [(μ.cupMultiC m).map_coord_zero i ((Submodule.mem_bot ℂ).mp this)]
    exact Submodule.zero_mem _

/-- **Step 3 of the compatibility.** Under O5, each piece of the exterior power of the weight-one
structure of `H¹` lies in the pullback of the matching candidate piece of `ℂ ⊗ H^m` along the
complexified torus isomorphism. -/
theorem exteriorPowerH_le_comap_cohomologyHodgePiece (hF : FiniteBetti X)
    (hB : BettiDeRhamIso X) (hD : HodgeDecomposition X) (hT : TorusCohomology μ)
    (hC : CupFiltered X μ) (m : ℕ) (pq : ℤ × ℤ) :
    letI := hT.finite
    letI := (finiteBetti_of_torusCohomology hT).finite m
    (cohomologyHodgeStructure hF hB hD 1).exteriorPowerH (V := HQ X 1) m pq ≤
      (cohomologyHodgePiece X m pq).comap
        (HodgeBlocks.QHodgeStructure.complexificationCongr (V := ⋀[ℚ]^m (HQ X 1))
          (W := HQ X m) (hT.cupWedgeEquiv m)).toLinearMap := by
  let := hT.finite
  let := (finiteBetti_of_torusCohomology hT).finite m
  rw [exteriorPowerH_eq_wedgePiece, ← Submodule.map_le_iff_le_comap]
  exact map_wedgePiece_le_cohomologyHodgePiece hF hB hD hT hC m pq

/-- **Step 4 of the compatibility.** Under O5, each piece of the exterior power of the weight-one
structure of `H¹` is exactly the pullback of the matching candidate piece of `ℂ ⊗ H^m` along the
complexified torus isomorphism: step 3 gives `≤`, and `mem_of_map_mem_of_iSupIndep_of_map_le` (the pieces
of `⋀^m` cover, the pieces of `H^m` are independent by C4, the map is injective by C7) gives
`≥`. Off the line `p + q = m` both sides are `⊥`; no separate case is needed. -/
theorem comap_cohomologyHodgePiece_eq_exteriorPowerH (hF : FiniteBetti X)
    (hB : BettiDeRhamIso X) (hD : HodgeDecomposition X) (hT : TorusCohomology μ)
    (hC : CupFiltered X μ) (m : ℕ) (pq : ℤ × ℤ) :
    letI := hT.finite
    letI := (finiteBetti_of_torusCohomology hT).finite m
    (cohomologyHodgePiece X m pq).comap
        (HodgeBlocks.QHodgeStructure.complexificationCongr (V := ⋀[ℚ]^m (HQ X 1))
          (W := HQ X m) (hT.cupWedgeEquiv m)).toLinearMap =
      (cohomologyHodgeStructure hF hB hD 1).exteriorPowerH (V := HQ X 1) m pq := by
  let := hT.finite
  let := (finiteBetti_of_torusCohomology hT).finite m
  refine le_antisymm (fun x hx => ?_)
    (exteriorPowerH_le_comap_cohomologyHodgePiece hF hB hD hT hC m pq)
  exact mem_of_map_mem_of_iSupIndep_of_map_le
    ((cohomologyHodgeStructure hF hB hD 1).exteriorPowerH_isInternal (V := HQ X 1)
      m).submodule_iSup_eq_top
    (cohomologyHodgeStructure hF hB hD m).isInternal.submodule_iSupIndep (g := id)
    Function.injective_id (LinearEquiv.injective _)
    (fun i => Submodule.map_le_iff_le_comap.mpr
      (exteriorPowerH_le_comap_cohomologyHodgePiece hF hB hD hT hC m i)) hx

/-- **The abelian-variety package is the exterior power of its weight-one part
(`IsExteriorOfWeightOne`, roadmap C6).** For an abelian `X`, under finite Betti numbers (C1), the
Betti–de Rham comparison (C2), the Hodge decomposition (C4), the torus theorem (C7) and the cup
product respecting the Hodge filtration (O5), the Hodge structure of `H^m(X(ℂ); ℚ)`, carried to
`⋀^m H¹` by `abelianVarietyCohomologyOf`, is the `m`-th exterior power of the weight-one
structure of `H¹(X(ℂ); ℚ)`, piece by piece. This retires the compatibility half of the referee
disclosure of `HodgeBlocks.AbelianVarietyCohomology` for this package only, and only
conditionally: C1, C2, C4, C7 and O5 remain hypotheses, and the disclosure still applies to every
other `AbelianVarietyCohomology`.

Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, Lemma 1.3.1 (through `TorusCohomology`), with Voisin, *Hodge Theory and Complex Algebraic Geometry I*, Cambridge Stud. Adv. Math. 76, §7.1 (through `CupFiltered`); the compatibility itself is proved here, with no further input.

Proof in four steps: the complexified cup of classes of types `d i` has type `∑ d i`
(`CupFiltered.bettiDeRhamHQ_cupMultiC_mem`); each exterior-power piece is the span of its wedges
(`exteriorPowerH_eq_wedgePiece`); so it maps into the matching piece of `H^m`
(`exteriorPowerH_le_comap_cohomologyHodgePiece`); and bijectivity with independence gives
equality (`comap_cohomologyHodgePiece_eq_exteriorPowerH`).

| hypothesis | roadmap |
| --- | --- |
| `hF : FiniteBetti X` | C1 |
| `hB : BettiDeRhamIso X` | C2 |
| `hD : HodgeDecomposition X` | C4 |
| `hT : TorusCohomology μ` | C7 |
| `hC : CupFiltered X μ` | O5 |

`hF` is kept so that the package is literally `abelianVarietyCohomologyOf hF hB hD hT`, the one
the transfer `hdg_le_span_of_hodgeConjectureFor` uses. It is redundant given `hT`
(`finiteBetti_of_torusCohomology`): a caller with only `hT` passes
`finiteBetti_of_torusCohomology hT`, and since `FiniteBetti X` is a proposition every choice gives
the same package.

Relation to the goal: HC no distance; AV milestone no distance (it retires the package's open
compatibility, not a case of HC). -/
@[hodge_milestone] theorem isExteriorOfWeightOne_of_cupFiltered (hF : FiniteBetti X)
    (hB : BettiDeRhamIso X) (hD : HodgeDecomposition X) (hT : TorusCohomology μ)
    (hC : CupFiltered X μ) :
    letI := hT.finite
    AbelianVarietyCohomology.IsExteriorOfWeightOne (abelianVarietyCohomologyOf hF hB hD hT) := by
  let := hT.finite
  intro m pq
  let := (finiteBetti_of_torusCohomology hT).finite m
  rw [HodgeBlocks.WeilAction.weightCast_H]
  let Φ := HodgeBlocks.QHodgeStructure.complexificationCongr (V := ⋀[ℚ]^m (HQ X 1))
    (W := HQ X m) (hT.cupWedgeEquiv m)
  let Ψ := HodgeBlocks.QHodgeStructure.complexificationCongr (V := HQ X m)
    (W := ⋀[ℚ]^m (HQ X 1)) (hT.cupWedgeEquiv m).symm
  change (cohomologyHodgePiece X m pq).map Ψ.toLinearMap =
    (cohomologyHodgeStructure hF hB hD 1).exteriorPowerH (V := HQ X 1) m pq
  have hΨ : ∀ x, Ψ x = Φ.symm x := fun x => by
    apply Φ.injective
    rw [LinearEquiv.apply_symm_apply]
    induction x using TensorProduct.inductionOn with
    | tmul c w => simp [Ψ, Φ]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  rw [← comap_cohomologyHodgePiece_eq_exteriorPowerH hF hB hD hT hC m pq]
  ext x
  rw [Submodule.mem_map_equiv, Submodule.mem_comap]
  have : Ψ.symm x = Φ x := by
    rw [LinearEquiv.symm_apply_eq, hΨ, LinearEquiv.symm_apply_apply]
  rw [this]
  rfl

/-- **Hodge classes of the exterior power.** Under C1, C2, C4, C7 and O5, `v ∈ ⋀^(2p) H¹` is a
Hodge class of the exterior power of the weight-one structure of `H¹(X(ℂ); ℚ)` exactly when its
cup product `cupWedgeMap (2p) v` lies in upstream's `Hdg^p(X; ℚ)`. From
`isExteriorOfWeightOne_of_cupFiltered` and `isHodgeClass_abelianVarietyCohomologyOf_iff`.

The weight cast `((2p : ℕ) : ℤ) * 1 = 2 * p` is a `weightCast`, the same operation Blocks'
`isHodgeClass_of_mem_weilClasses` applies (any two proofs of the equation agree);
`isHodgeClass_exteriorPower_add_iff` states the degree as `k + k`, as that theorem does.

Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, Lemma 1.3.1 (through `TorusCohomology`), with Voisin, *Hodge Theory and Complex Algebraic Geometry I*, Cambridge Stud. Adv. Math. 76, §7.1 (through `CupFiltered`).

| hypothesis | roadmap |
| --- | --- |
| `hF : FiniteBetti X` | C1 |
| `hB : BettiDeRhamIso X` | C2 |
| `hD : HodgeDecomposition X` | C4 |
| `hT : TorusCohomology μ` | C7 |
| `hC : CupFiltered X μ` | O5 |

Relation to the goal: HC no distance; AV milestone no distance. -/
theorem isHodgeClass_exteriorPower_iff (hF : FiniteBetti X) (hB : BettiDeRhamIso X)
    (hD : HodgeDecomposition X) (hT : TorusCohomology μ) (hC : CupFiltered X μ) (p : ℕ)
    (v : ⋀[ℚ]^(2 * p) (HQ X 1)) :
    letI := hT.finite
    HodgeBlocks.IsHodgeClass (p := (p : ℤ))
      (HodgeBlocks.WeilAction.weightCast (V := ⋀[ℚ]^(2 * p) (HQ X 1)) (by push_cast; ring)
        ((abelianVarietyCohomologyOf hF hB hD hT).weight1.exteriorPower (V := HQ X 1)
          (2 * p))) v ↔
      (μ.cupWedgeMap (2 * p) v : H^(2 * p)(X; ℚ)) ∈ Hdg^p(X; ℚ) := by
  let := hT.finite
  rw [← isHodgeClass_abelianVarietyCohomologyOf_iff hF hB hD hT p v, HodgeBlocks.IsHodgeClass,
    HodgeBlocks.IsHodgeClass, isExteriorOfWeightOne_of_cupFiltered hF hB hD hT hC (2 * p) (p, p),
    HodgeBlocks.WeilAction.weightCast_H]

/-- `isHodgeClass_exteriorPower_iff` with the degree written `k + k`, the form in which Blocks'
`isHodgeClass_of_mem_weilClasses` concludes (`IsHodgeClass (p := k)` of
`weightCast _ (M.exteriorPower (k + k))`); the cup product is read in `H^(2k)` along
`k + k = 2k`.

Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, Lemma 1.3.1 (through `TorusCohomology`), with Voisin, *Hodge Theory and Complex Algebraic Geometry I*, Cambridge Stud. Adv. Math. 76, §7.1 (through `CupFiltered`).

| hypothesis | roadmap |
| --- | --- |
| `hF : FiniteBetti X` | C1 |
| `hB : BettiDeRhamIso X` | C2 |
| `hD : HodgeDecomposition X` | C4 |
| `hT : TorusCohomology μ` | C7 |
| `hC : CupFiltered X μ` | O5 |

Relation to the goal: HC no distance; AV milestone no distance. -/
theorem isHodgeClass_exteriorPower_add_iff (hF : FiniteBetti X) (hB : BettiDeRhamIso X)
    (hD : HodgeDecomposition X) (hT : TorusCohomology μ) (hC : CupFiltered X μ) (k : ℕ)
    (v : ⋀[ℚ]^(k + k) (HQ X 1)) :
    letI := hT.finite
    HodgeBlocks.IsHodgeClass (p := (k : ℤ))
      (HodgeBlocks.WeilAction.weightCast (V := ⋀[ℚ]^(k + k) (HQ X 1)) (by omega)
        ((abelianVarietyCohomologyOf hF hB hD hT).weight1.exteriorPower (V := HQ X 1)
          (k + k))) v ↔
      (HQ.castEquiv X (two_mul k).symm (μ.cupWedgeMap (k + k) v) : H^(2 * k)(X; ℚ)) ∈
        Hdg^k(X; ℚ) := by
  let := hT.finite
  have gen : ∀ (m : ℕ) (h : m = 2 * k) (w : ⋀[ℚ]^m (HQ X 1)),
      HodgeBlocks.complexify _ w ∈
        ((abelianVarietyCohomologyOf hF hB hD hT).weight1.exteriorPower (V := HQ X 1) m).H
          ((k : ℤ), (k : ℤ)) ↔
      (HQ.castEquiv X h (μ.cupWedgeMap m w) : H^(2 * k)(X; ℚ)) ∈ Hdg^k(X; ℚ) := by
    intro m h w
    subst h
    have := isHodgeClass_exteriorPower_iff hF hB hD hT hC k w
    rw [HodgeBlocks.IsHodgeClass, HodgeBlocks.WeilAction.weightCast_H] at this
    rw [HQ.castEquiv_apply_self]
    exact this
  rw [HodgeBlocks.IsHodgeClass, HodgeBlocks.WeilAction.weightCast_H]
  exact gen (k + k) (two_mul k).symm v

end Compatibility

end HodgeLean.RealDefs
