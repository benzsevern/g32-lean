import HodgeLean.Foundations.MultiBlockInvariantsDefs

/-! # Proofs for the multi-block invariants spec (stage A3b)

The agent's working file. Fill every proof hole. **Do not change the statement of any `_aux`
theorem**: `MultiBlockInvariants.lean` (frozen) restates each one and must still typecheck.
Helper lemmas may be added freely, in this file or in new files; prefix them `a3b_`.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] HodgeLean.Foundations.SchurWeyl.dualAddCommGroup
open scoped TensorProduct DirectSum
namespace HodgeLean.Foundations
open InvariantsExterior SchurWeyl Module

variable {K : Type*} [Field K] [CharZero K]

section Blocks

variable {e : ℕ} {W U U' : Fin (e + 1) → Type*}
  [∀ v, AddCommGroup (W v)] [∀ v, Module K (W v)] [∀ v, FiniteDimensional K (W v)]
  [∀ v, AddCommGroup (U v)] [∀ v, Module K (U v)]
  [∀ v, AddCommGroup (U' v)] [∀ v, Module K (U' v)]

omit [CharZero K] in
/-- Block-diagonal maps commute with `Fin.consLinearEquiv`: `piMap φ` on `Π_v S_v` is
`φ 0 × piMap (φ ∘ succ)` on `S_0 × Π_j S_{j.succ}`. -/
theorem a3b_piMap_comp_consLinearEquiv {n : ℕ} {S : Fin (n + 1) → Type*}
    [∀ v, AddCommGroup (S v)] [∀ v, Module K (S v)] (φ : (v : Fin (n + 1)) → Module.End K (S v)) :
    LinearMap.piMap φ ∘ₗ (Fin.consLinearEquiv K S).toLinearMap =
      (Fin.consLinearEquiv K S).toLinearMap ∘ₗ
        (φ 0).prodMap (LinearMap.piMap fun j => φ j.succ) := by
  refine LinearMap.ext fun x => funext fun v => ?_
  refine Fin.cases ?_ (fun j => ?_) v <;> simp [Fin.consLinearEquiv, Fin.consEquiv]

/-- The Lie subalgebra of block-diagonal endomorphisms `piMap (ρ ∘ g)` of `Π_i M_i`, for Lie maps
`ρ_i : 𝔤_i → End M_i`. It stands in for the image of `Π_i 𝔤_i`, which carries no Lie structure in
Mathlib.
Source: Bourbaki, *Groupes et algèbres de Lie*, ch. I, §1, no. 1 (product of Lie algebras). -/
def a3bPiLieSubalgebra {ι : Type*} {𝔤 M : ι → Type*} [∀ i, LieRing (𝔤 i)]
    [∀ i, LieAlgebra K (𝔤 i)] [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)]
    (ρ : ∀ i, 𝔤 i →ₗ⁅K⁆ Module.End K (M i)) : LieSubalgebra K (Module.End K ((i : ι) → M i)) where
  carrier := Set.range fun g : (i : ι) → 𝔤 i => LinearMap.piMap fun i => ρ i (g i)
  zero_mem' := ⟨0, by ext; simp⟩
  add_mem' := by
    rintro _ _ ⟨g, rfl⟩ ⟨g', rfl⟩
    exact ⟨g + g', by ext; simp⟩
  smul_mem' := by
    rintro c _ ⟨g, rfl⟩
    exact ⟨c • g, by ext; simp⟩
  lie_mem' := by
    rintro _ _ ⟨g, rfl⟩ ⟨g', rfl⟩
    refine ⟨fun i => ⁅g i, g' i⁆, ?_⟩
    ext x i
    simp [Ring.lie_def, LieHom.map_lie]

example {ι : Type*} {𝔤 M : ι → Type*} [∀ i, LieRing (𝔤 i)]
    [∀ i, LieAlgebra K (𝔤 i)] [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)]
    (ρ : ∀ i, 𝔤 i →ₗ⁅K⁆ Module.End K (M i)) (g : (i : ι) → 𝔤 i) :
    LinearMap.piMap (fun i => ρ i (g i)) ∈ a3bPiLieSubalgebra ρ :=
  ⟨g, rfl⟩

/-- A3a's S8 transported along `Fin.consLinearEquiv : S 0 × Π_j S_{j.succ} ≃ Π_v S_v`, with the
two families of invariants given as functions of the degree. -/
theorem a3b_exterior_invariants_cons {n : ℕ} {S : Fin (n + 1) → Type*}
    [∀ v, AddCommGroup (S v)] [∀ v, Module K (S v)] [∀ v, FiniteDimensional K (S v)]
    {𝔤₁ 𝔤₂ : Type*} [LieRing 𝔤₁] [LieAlgebra K 𝔤₁] [LieRing 𝔤₂] [LieAlgebra K 𝔤₂]
    (ρ₁ : 𝔤₁ →ₗ⁅K⁆ Module.End K (S 0)) (ρ₂ : 𝔤₂ →ₗ⁅K⁆ Module.End K ((j : Fin n) → S j.succ))
    (k : ℕ) (P : Submodule K (⋀[K]^k ((v : Fin (n + 1)) → S v)))
    (N₁ : (i : ℕ) → Submodule K (⋀[K]^i (S 0)))
    (N₂ : (j : ℕ) → Submodule K (⋀[K]^j ((j : Fin n) → S j.succ)))
    (hP : P = Submodule.map (exteriorPower.map k (Fin.consLinearEquiv K S).toLinearMap)
      (⨅ x : 𝔤₁ × 𝔤₂, LinearMap.ker (exteriorDer k ((ρ₁ x.1).prodMap (ρ₂ x.2)))))
    (h₁ : ∀ i, N₁ i = ⨅ x, LinearMap.ker (exteriorDer i (ρ₁ x)))
    (h₂ : ∀ j, N₂ j = ⨅ y, LinearMap.ker (exteriorDer j (ρ₂ y))) :
    P = ⨆ p : {p : ℕ × ℕ // p.1 + p.2 = k},
      LinearMap.range
        (exteriorPower.map k (Fin.consLinearEquiv K S).toLinearMap ∘ₗ
          exteriorProdDegree k ∘ₗ
          DirectSum.lof K _ (fun p : {p : ℕ × ℕ // p.1 + p.2 = k} =>
            ⋀[K]^p.1.1 (S 0) ⊗[K] ⋀[K]^p.1.2 ((j : Fin n) → S j.succ)) p ∘ₗ
          TensorProduct.map (N₁ p.1.1).subtype (N₂ p.1.2).subtype) := by
  obtain rfl : N₁ = _ := funext h₁
  obtain rfl : N₂ = _ := funext h₂
  rw [hP, spec_a3a_exterior_invariants ρ₁ ρ₂ k, Submodule.map_iSup]
  refine iSup_congr fun p => ?_
  simp only [LinearMap.range_comp]

/-- The inductive step in generic form: for Lie maps `ρ_v : 𝔤_v → End S_v`, the joint kernel of
the block-diagonal operators `piMap (ρ ∘ f)` on `⋀^k (Π_v S_v)` is the image of the tensor products
of the block-`0` invariants and the tail invariants. -/
theorem a3b_invariants_cons_generic {n : ℕ} {S : Fin (n + 1) → Type*}
    [∀ v, AddCommGroup (S v)] [∀ v, Module K (S v)] [∀ v, FiniteDimensional K (S v)]
    {𝔤 : Fin (n + 1) → Type*} [∀ v, LieRing (𝔤 v)] [∀ v, LieAlgebra K (𝔤 v)]
    (ρ : ∀ v, 𝔤 v →ₗ⁅K⁆ Module.End K (S v)) (k : ℕ) :
    (⨅ f : (v : Fin (n + 1)) → 𝔤 v,
        LinearMap.ker (exteriorDer k (LinearMap.piMap fun v => ρ v (f v)))) =
      ⨆ p : {p : ℕ × ℕ // p.1 + p.2 = k},
        LinearMap.range
          (exteriorPower.map k (Fin.consLinearEquiv K S).toLinearMap ∘ₗ
            exteriorProdDegree k ∘ₗ
            DirectSum.lof K _ (fun p : {p : ℕ × ℕ // p.1 + p.2 = k} =>
              ⋀[K]^p.1.1 (S 0) ⊗[K] ⋀[K]^p.1.2 ((j : Fin n) → S j.succ)) p ∘ₗ
            TensorProduct.map
              (⨅ x : 𝔤 0, LinearMap.ker (exteriorDer p.1.1 (ρ 0 x))).subtype
              (⨅ g : (j : Fin n) → 𝔤 j.succ,
                LinearMap.ker (exteriorDer p.1.2 (LinearMap.piMap fun j => ρ j.succ (g j)))).subtype) := by
  let E := Fin.consLinearEquiv K S
  let L := a3bPiLieSubalgebra (K := K) fun j : Fin n => ρ j.succ
  -- the joint kernel over `L` is the joint kernel over the family
  have hL : ∀ m, (⨅ y : L, LinearMap.ker (exteriorDer m (L.incl y))) =
      ⨅ g : (j : Fin n) → 𝔤 j.succ,
        LinearMap.ker (exteriorDer m (LinearMap.piMap fun j => ρ j.succ (g j))) := by
    intro m
    apply le_antisymm
    · exact le_iInf fun g => iInf_le_of_le ⟨_, g, rfl⟩ le_rfl
    · refine le_iInf fun y => ?_
      obtain ⟨_, g, hg⟩ := y
      subst hg
      exact iInf_le_of_le g le_rfl
  -- intertwining along `E`
  have hint : ∀ (f : (v : Fin (n + 1)) → 𝔤 v) (y : ⋀[K]^k (S 0 × ((j : Fin n) → S j.succ))),
      exteriorDer k (LinearMap.piMap fun v => ρ v (f v)) (exteriorPower.map k E.toLinearMap y) =
        exteriorPower.map k E.toLinearMap (exteriorDer k
          ((ρ 0 (f 0)).prodMap (LinearMap.piMap fun j => ρ j.succ (f j.succ))) y) :=
    fun f y => exteriorDer_map k _ _ _ (a3b_piMap_comp_consLinearEquiv fun v => ρ v (f v)) y
  have hEE : ∀ y : ⋀[K]^k (S 0 × ((j : Fin n) → S j.succ)),
      exteriorPower.map k E.symm.toLinearMap (exteriorPower.map k E.toLinearMap y) = y := by
    intro y
    rw [← LinearMap.comp_apply, ← exteriorPower.map_comp]
    simp
  have hEE' : ∀ x : ⋀[K]^k ((v : Fin (n + 1)) → S v),
      exteriorPower.map k E.toLinearMap (exteriorPower.map k E.symm.toLinearMap x) = x := by
    intro x
    rw [← LinearMap.comp_apply, ← exteriorPower.map_comp]
    simp
  refine a3b_exterior_invariants_cons (ρ 0) L.incl k _
    (fun i => ⨅ x : 𝔤 0, LinearMap.ker (exteriorDer i (ρ 0 x)))
    (fun j => ⨅ g : (j : Fin n) → 𝔤 j.succ,
      LinearMap.ker (exteriorDer j (LinearMap.piMap fun j => ρ j.succ (g j)))) ?_ (fun _ => rfl)
    fun m => (hL m).symm
  ext x
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, Submodule.mem_map]
  constructor
  · intro hx
    refine ⟨exteriorPower.map k E.symm.toLinearMap x, ?_, hEE' x⟩
    rintro ⟨a, ⟨_, g, rfl⟩⟩
    have h := hint (Fin.cons a g) (exteriorPower.map k E.symm.toLinearMap x)
    rw [hEE', hx] at h
    have h' := congrArg (exteriorPower.map k E.symm.toLinearMap) h
    rw [hEE, map_zero] at h'
    simpa [a3bPiLieSubalgebra] using h'.symm
  · rintro ⟨y, hy, rfl⟩ f
    rw [hint]
    have := hy (f 0, ⟨_, fun j => f j.succ, rfl⟩)
    simp only [LieSubalgebra.coe_incl] at this
    rw [this, map_zero]

theorem spec_a3b_invariants_cons_aux [∀ v, FiniteDimensional K (U v)]
    [∀ v, FiniteDimensional K (U' v)] (k : ℕ) :
    (⨅ f : (v : Fin (e + 1)) → slEnd K (W v),
        LinearMap.ker (exteriorDer k
          (LinearMap.piMap fun v => multiplicityLie K (W v) (U v) (U' v) (f v)))) =
      ⨆ p : {p : ℕ × ℕ // p.1 + p.2 = k},
        LinearMap.range
          (exteriorPower.map k
              (Fin.consLinearEquiv K fun v => Space K (W v) (U v) (U' v)).toLinearMap ∘ₗ
            exteriorProdDegree k ∘ₗ
            DirectSum.lof K _ (fun p : {p : ℕ × ℕ // p.1 + p.2 = k} =>
              ⋀[K]^p.1.1 (Space K (W 0) (U 0) (U' 0)) ⊗[K]
                ⋀[K]^p.1.2 (MultiSpace K (fun j : Fin e => W j.succ)
                  (fun j => U j.succ) (fun j => U' j.succ))) p ∘ₗ
            TensorProduct.map
              (⨅ f : slEnd K (W 0),
                LinearMap.ker (exteriorDer p.1.1 (multiplicityLie K (W 0) (U 0) (U' 0) f))).subtype
              (⨅ g : (j : Fin e) → slEnd K (W j.succ),
                LinearMap.ker (exteriorDer p.1.2 (LinearMap.piMap fun j =>
                  multiplicityLie K (W j.succ) (U j.succ) (U' j.succ) (g j)))).subtype) := by
  exact a3b_invariants_cons_generic
    (fun v => (multiplicityLie K (W v) (U v) (U' v)).comp (slEnd K (W v)).incl) k

section Helpers

omit [CharZero K]

variable {M N : Type*} [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]

theorem a3b_coe_wedge {k l : ℕ} (x : ⋀[K]^k M) (y : ⋀[K]^l M) :
    ((exteriorPower.wedge K M k l x y : ⋀[K]^(k + l) M) : ExteriorAlgebra K M) =
      (x : ExteriorAlgebra K M) * y :=
  rfl

theorem a3b_map_wedge (f : M →ₗ[K] N) {k l : ℕ} (x : ⋀[K]^k M) (y : ⋀[K]^l M) :
    exteriorPower.map (k + l) f (exteriorPower.wedge K M k l x y) =
      exteriorPower.wedge K N k l (exteriorPower.map k f x) (exteriorPower.map l f y) := by
  apply Subtype.ext
  simp only [exteriorPower.coe_map, a3b_coe_wedge, map_mul]

theorem a3b_coe_unit :
    ((exteriorPower.ιMulti K 0 (Fin.elim0 : Fin 0 → M) : ⋀[K]^0 M) : ExteriorAlgebra K M) = 1 := by
  simp [exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply]

theorem a3b_map_unit (f : M →ₗ[K] N) :
    exteriorPower.map 0 f (exteriorPower.ιMulti K 0 (Fin.elim0 : Fin 0 → M)) =
      exteriorPower.ιMulti K 0 Fin.elim0 := by
  rw [exteriorPower.map_apply_ιMulti]
  congr 1
  funext i
  exact Fin.elim0 i

section Factors

variable {P Q : Type*} [AddCommGroup P] [Module K P] [AddCommGroup Q] [Module K Q]

theorem a3b_unit_eq_mul (f : M →ₗ[K] N) (g : P →ₗ[K] N) :
    ((exteriorPower.ιMulti K 0 (Fin.elim0 : Fin 0 → N) : ⋀[K]^0 N) : ExteriorAlgebra K N) =
      ExteriorAlgebra.map f
          ((exteriorPower.ιMulti K 0 (Fin.elim0 : Fin 0 → M) : ⋀[K]^0 M) : ExteriorAlgebra K M) *
        ExteriorAlgebra.map g
          ((exteriorPower.ιMulti K 0 (Fin.elim0 : Fin 0 → P) : ⋀[K]^0 P) : ExteriorAlgebra K P) := by
  rw [a3b_coe_unit, a3b_coe_unit, a3b_coe_unit, map_one, map_one, mul_one]

theorem a3b_map_eq_mul_unit (f : M →ₗ[K] N) (g : P →ₗ[K] N) {k : ℕ} (x : ⋀[K]^k M) :
    ((exteriorPower.map k f x : ⋀[K]^k N) : ExteriorAlgebra K N) =
      ExteriorAlgebra.map f (x : ExteriorAlgebra K M) *
        ExteriorAlgebra.map g
          ((exteriorPower.ιMulti K 0 (Fin.elim0 : Fin 0 → P) : ⋀[K]^0 P) : ExteriorAlgebra K P) := by
  rw [a3b_coe_unit, map_one, mul_one, exteriorPower.coe_map]

theorem a3b_map_comp_eq_unit_mul (f : M →ₗ[K] N) (g : P →ₗ[K] N) (h : Q →ₗ[K] P) {k : ℕ}
    (x : ⋀[K]^k Q) :
    ((exteriorPower.map k (g ∘ₗ h) x : ⋀[K]^k N) : ExteriorAlgebra K N) =
      ExteriorAlgebra.map f
          ((exteriorPower.ιMulti K 0 (Fin.elim0 : Fin 0 → M) : ⋀[K]^0 M) : ExteriorAlgebra K M) *
        ExteriorAlgebra.map g ((exteriorPower.map k h x : ⋀[K]^k P) : ExteriorAlgebra K P) := by
  rw [a3b_coe_unit, map_one, one_mul, exteriorPower.coe_map, exteriorPower.coe_map,
    ← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map]

theorem a3b_coe_wedge_map (f : M →ₗ[K] N) (g : P →ₗ[K] N) {i j : ℕ} (a : ⋀[K]^i M)
    (b : ⋀[K]^j P) :
    ((exteriorPower.wedge K N i j (exteriorPower.map i f a) (exteriorPower.map j g b) :
        ⋀[K]^(i + j) N) : ExteriorAlgebra K N) =
      ExteriorAlgebra.map f (a : ExteriorAlgebra K M) * ExteriorAlgebra.map g (b : ExteriorAlgebra K P) := by
  rw [a3b_coe_wedge, exteriorPower.coe_map, exteriorPower.coe_map]

end Factors

variable {ι : Type*} [DecidableEq ι] {X Y Z : ι → Type*}
  [∀ v, AddCommGroup (X v)] [∀ v, Module K (X v)] [∀ v, FiniteDimensional K (X v)]
  [∀ v, AddCommGroup (Y v)] [∀ v, Module K (Y v)]
  [∀ v, AddCommGroup (Z v)] [∀ v, Module K (Z v)]

theorem a3b_multiGeneratedDegree_zero :
    multiGeneratedDegree (K := K) (W := X) (U := Y) (U' := Z) 0 = ⊤ := by
  apply top_unique
  rw [← exteriorPower.ιMulti_span K 0 (MultiSpace K X Y Z), Submodule.span_le]
  rintro _ ⟨v, rfl⟩
  have hv : v = Fin.elim0 := funext (fun i => Fin.elim0 i)
  rw [hv]
  exact Submodule.subset_span MultiGeneratorProduct.unit

theorem a3b_wedge_mem {k l : ℕ} {x : ⋀[K]^k (MultiSpace K X Y Z)} {y : ⋀[K]^l (MultiSpace K X Y Z)}
    (hx : x ∈ multiGeneratedDegree k) (hy : y ∈ multiGeneratedDegree l) :
    exteriorPower.wedge K _ k l x y ∈ multiGeneratedDegree (k + l) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    induction hy using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span (MultiGeneratorProduct.wedge hx hy)
    | zero => simp only [map_zero, Submodule.zero_mem]
    | add y z _ _ hy hz => simpa only [map_add] using Submodule.add_mem _ hy hz
    | smul a y _ hy => simpa only [map_smul] using Submodule.smul_mem _ a hy
  | zero => simp only [map_zero, LinearMap.zero_apply, Submodule.zero_mem]
  | add x z _ _ hx hz =>
    simpa only [map_add, LinearMap.add_apply] using Submodule.add_mem _ hx hz
  | smul a x _ hx =>
    simpa only [map_smul, LinearMap.smul_apply] using Submodule.smul_mem _ a hx

theorem a3b_map_single_mem (v : ι) {k : ℕ} {g : ⋀[K]^k (Space K (X v) (Y v) (Z v))}
    (hg : g ∈ generatedDegree k) :
    exteriorPower.map k (LinearMap.single K (fun v => Space K (X v) (Y v) (Z v)) v) g ∈
      multiGeneratedDegree (K := K) (W := X) (U := Y) (U' := Z) k := by
  induction hg using Submodule.span_induction with
  | mem g hg => exact Submodule.subset_span (MultiGeneratorProduct.block v hg)
  | zero => simp only [map_zero, Submodule.zero_mem]
  | add x z _ _ hx hz => simpa only [map_add] using Submodule.add_mem _ hx hz
  | smul a x _ hx => simpa only [map_smul] using Submodule.smul_mem _ a hx

theorem a3b_mem_of_coe_eq {k l : ℕ} (h : k = l) {x : ⋀[K]^k (MultiSpace K X Y Z)}
    {y : ⋀[K]^l (MultiSpace K X Y Z)}
    (hxy : (x : ExteriorAlgebra K (MultiSpace K X Y Z)) = (y : ExteriorAlgebra K (MultiSpace K X Y Z)))
    (hy : y ∈ multiGeneratedDegree l) : x ∈ multiGeneratedDegree k := by
  subst h
  rwa [Subtype.ext hxy]

end Helpers

section BlockHelpers

omit [CharZero K]

/-- The tail inclusion `x ↦ Fin.cons 0 x` of `Π_j Space_{j.succ}` in `Π_v Space_v`.
Source: constructed here; Mathlib's `Fin.consLinearEquiv` composed with `LinearMap.inr`. -/
abbrev a3b_consInr : MultiSpace K (fun j : Fin e => W j.succ) (fun j => U j.succ)
    (fun j => U' j.succ) →ₗ[K] MultiSpace K W U U' :=
  (Fin.consLinearEquiv K fun v => Space K (W v) (U v) (U' v)).toLinearMap ∘ₗ
    LinearMap.inr K (Space K (W 0) (U 0) (U' 0))
      (MultiSpace K (fun j : Fin e => W j.succ) (fun j => U j.succ) (fun j => U' j.succ))

omit [∀ v, FiniteDimensional K (W v)] in
example (x : MultiSpace K (fun j : Fin e => W j.succ) (fun j => U j.succ) (fun j => U' j.succ)) :
    a3b_consInr (K := K) x = Fin.cons 0 x :=
  rfl

omit [∀ v, FiniteDimensional K (W v)] in
theorem a3b_consInr_single (j : Fin e) :
    a3b_consInr (K := K) (W := W) (U := U) (U' := U') ∘ₗ
        LinearMap.single K (fun j : Fin e => Space K (W j.succ) (U j.succ) (U' j.succ)) j =
      LinearMap.single K (fun v => Space K (W v) (U v) (U' v)) j.succ := by
  refine LinearMap.ext fun x => funext fun v => ?_
  refine Fin.cases ?_ (fun i => ?_) v
  · simp [Fin.succ_ne_zero]
  · by_cases h : i = j
    · subst h; simp
    · simp [h, Fin.succ_inj]

omit [∀ v, FiniteDimensional K (W v)] in
theorem a3b_consInl :
    (Fin.consLinearEquiv K fun v => Space K (W v) (U v) (U' v)).toLinearMap ∘ₗ
        LinearMap.inl K (Space K (W 0) (U 0) (U' 0))
          (MultiSpace K (fun j : Fin e => W j.succ) (fun j => U j.succ) (fun j => U' j.succ)) =
      LinearMap.single K (fun v => Space K (W v) (U v) (U' v)) 0 := by
  refine LinearMap.ext fun x => funext fun v => ?_
  refine Fin.cases ?_ (fun i => ?_) v
  · simp
  · simp [Fin.succ_ne_zero]

theorem a3b_consInr_mgp {k : ℕ}
    {t : ⋀[K]^k (MultiSpace K (fun j : Fin e => W j.succ) (fun j => U j.succ) (fun j => U' j.succ))}
    (ht : MultiGeneratorProduct k t) :
    MultiGeneratorProduct (W := W) (U := U) (U' := U') k
      (exteriorPower.map k (a3b_consInr (K := K)) t) := by
  induction ht with
  | unit => rw [a3b_map_unit]; exact MultiGeneratorProduct.unit
  | block j hg =>
    rw [← LinearMap.comp_apply, ← exteriorPower.map_comp, a3b_consInr_single]
    exact MultiGeneratorProduct.block j.succ hg
  | wedge _ _ hx hy => rw [a3b_map_wedge]; exact MultiGeneratorProduct.wedge hx hy

theorem a3b_consInr_mem {k : ℕ}
    {t : ⋀[K]^k (MultiSpace K (fun j : Fin e => W j.succ) (fun j => U j.succ) (fun j => U' j.succ))}
    (ht : t ∈ multiGeneratedDegree k) :
    exteriorPower.map k (a3b_consInr (K := K)) t ∈
      multiGeneratedDegree (K := K) (W := W) (U := U) (U' := U') k := by
  induction ht using Submodule.span_induction with
  | mem g hg => exact Submodule.subset_span (a3b_consInr_mgp hg)
  | zero => simp only [map_zero, Submodule.zero_mem]
  | add x z _ _ hx hz => simpa only [map_add] using Submodule.add_mem _ hx hz
  | smul a x _ hx => simpa only [map_smul] using Submodule.smul_mem _ a hx

omit [CharZero K] in
theorem a3b_coe_exteriorProdMul {S₁ S₂ : Type*} [AddCommGroup S₁] [Module K S₁] [AddCommGroup S₂]
    [Module K S₂] (i j : ℕ) (a : ⋀[K]^i S₁) (b : ⋀[K]^j S₂) :
    ((exteriorProdMul i j (a ⊗ₜ[K] b) : ⋀[K]^(i + j) (S₁ × S₂)) : ExteriorAlgebra K (S₁ × S₂)) =
      ExteriorAlgebra.map (LinearMap.inl K S₁ S₂) (a : ExteriorAlgebra K S₁) *
        ExteriorAlgebra.map (LinearMap.inr K S₁ S₂) (b : ExteriorAlgebra K S₂) := by
  simp only [exteriorProdMul, TensorProduct.lift.tmul, LinearMap.comp_apply,
    LinearMap.compl₂_apply, a3b_coe_wedge, exteriorPower.coe_map]

/-- The map of S3 for one bidegree `p`: `g ⊗ t ↦ ⋀(ι_0) g ∧ ⋀(cons ∘ inr) t`, for `g` generated
in block `0` and `t` generated in the tail.
Source: constructed here; A3a's `exteriorProdDegree` along `Fin.consLinearEquiv`. -/
def a3b_consMap (k : ℕ) (p : {p : ℕ × ℕ // p.1 + p.2 = k}) :
    (generatedDegree (K := K) (W := W 0) (U := U 0) (U' := U' 0) p.1.1) ⊗[K]
        (multiGeneratedDegree (K := K) (W := fun j : Fin e => W j.succ)
          (U := fun j => U j.succ) (U' := fun j => U' j.succ) p.1.2) →ₗ[K]
      ⋀[K]^k (MultiSpace K W U U') :=
  exteriorPower.map k
      (Fin.consLinearEquiv K fun v => Space K (W v) (U v) (U' v)).toLinearMap ∘ₗ
    exteriorProdDegree k ∘ₗ
    DirectSum.lof K _ (fun p : {p : ℕ × ℕ // p.1 + p.2 = k} =>
      ⋀[K]^p.1.1 (Space K (W 0) (U 0) (U' 0)) ⊗[K]
        ⋀[K]^p.1.2 (MultiSpace K (fun j : Fin e => W j.succ)
          (fun j => U j.succ) (fun j => U' j.succ))) p ∘ₗ
    TensorProduct.map
      (generatedDegree (K := K) (W := W 0) (U := U 0) (U' := U' 0) p.1.1).subtype
      (multiGeneratedDegree (K := K) (W := fun j : Fin e => W j.succ)
        (U := fun j => U j.succ) (U' := fun j => U' j.succ) p.1.2).subtype

theorem a3b_coe_consMap (k : ℕ) (p : {p : ℕ × ℕ // p.1 + p.2 = k})
    (g : generatedDegree (K := K) (W := W 0) (U := U 0) (U' := U' 0) p.1.1)
    (t : multiGeneratedDegree (K := K) (W := fun j : Fin e => W j.succ)
          (U := fun j => U j.succ) (U' := fun j => U' j.succ) p.1.2) :
    ((a3b_consMap (K := K) (W := W) (U := U) (U' := U') k p (g ⊗ₜ[K] t) : ⋀[K]^k (MultiSpace K W U U')) :
        ExteriorAlgebra K (MultiSpace K W U U')) =
      ExteriorAlgebra.map (LinearMap.single K (fun v => Space K (W v) (U v) (U' v)) 0)
          (g.1 : ExteriorAlgebra K _) *
        ExteriorAlgebra.map (a3b_consInr (K := K)) (t.1 : ExteriorAlgebra K _) := by
  simp only [a3b_consMap, LinearMap.comp_apply, TensorProduct.map_tmul, Submodule.subtype_apply,
    exteriorPower.coe_map]
  simp only [exteriorProdDegree, DirectSum.toModule_lof, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.coe_ofEq_apply, a3b_coe_exteriorProdMul, map_mul]
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map,
    ExteriorAlgebra.map_comp_map, a3b_consInl]

example (k : ℕ) (p : {p : ℕ × ℕ // p.1 + p.2 = k})
    (g : generatedDegree (K := K) (W := W 0) (U := U 0) (U' := U' 0) p.1.1)
    (t : multiGeneratedDegree (K := K) (W := fun j : Fin e => W j.succ)
          (U := fun j => U j.succ) (U' := fun j => U' j.succ) p.1.2) :
    a3b_consMap (K := K) (W := W) (U := U) (U' := U') k p (g ⊗ₜ[K] t) ∈ LinearMap.range (a3b_consMap (K := K) (W := W) (U := U) (U' := U') k p) :=
  ⟨_, rfl⟩

theorem a3b_mem_consRHS {k i j : ℕ} (h : i + j = k) {g : ⋀[K]^i (Space K (W 0) (U 0) (U' 0))}
    (hg : g ∈ generatedDegree i)
    {t : ⋀[K]^j (MultiSpace K (fun j : Fin e => W j.succ) (fun j => U j.succ) (fun j => U' j.succ))}
    (ht : t ∈ multiGeneratedDegree j) {x : ⋀[K]^k (MultiSpace K W U U')}
    (hx : (x : ExteriorAlgebra K (MultiSpace K W U U')) =
      ExteriorAlgebra.map (LinearMap.single K (fun v => Space K (W v) (U v) (U' v)) 0)
          (g : ExteriorAlgebra K _) *
        ExteriorAlgebra.map (a3b_consInr (K := K)) (t : ExteriorAlgebra K _)) :
    x ∈ ⨆ p, LinearMap.range (a3b_consMap (K := K) (W := W) (U := U) (U' := U') k p) := by
  refine Submodule.mem_iSup_of_mem ⟨(i, j), h⟩ ⟨⟨g, hg⟩ ⊗ₜ[K] ⟨t, ht⟩, ?_⟩
  apply Subtype.ext
  rw [a3b_coe_consMap, hx]

omit [CharZero K] [∀ v, FiniteDimensional K (W v)] in
theorem a3b_map_cons_inl (z : ExteriorAlgebra K (Space K (W 0) (U 0) (U' 0))) :
    ExteriorAlgebra.map (Fin.consLinearEquiv K fun v => Space K (W v) (U v) (U' v)).toLinearMap
        (ExteriorAlgebra.map (LinearMap.inl K (Space K (W 0) (U 0) (U' 0))
          (MultiSpace K (fun j : Fin e => W j.succ) (fun j => U j.succ) (fun j => U' j.succ))) z) =
      ExteriorAlgebra.map (LinearMap.single K (fun v => Space K (W v) (U v) (U' v)) 0) z := by
  rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map, a3b_consInl]

omit [CharZero K] [∀ v, FiniteDimensional K (W v)] in
theorem a3b_map_cons_inr
    (z : ExteriorAlgebra K
      (MultiSpace K (fun j : Fin e => W j.succ) (fun j => U j.succ) (fun j => U' j.succ))) :
    ExteriorAlgebra.map (Fin.consLinearEquiv K fun v => Space K (W v) (U v) (U' v)).toLinearMap
        (ExteriorAlgebra.map (LinearMap.inr K (Space K (W 0) (U 0) (U' 0))
          (MultiSpace K (fun j : Fin e => W j.succ) (fun j => U j.succ) (fun j => U' j.succ))) z) =
      ExteriorAlgebra.map (a3b_consInr (K := K)) z := by
  rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map]

omit [CharZero K] [∀ v, FiniteDimensional K (W v)] in
theorem a3b_cons_sign {i j i' j' : ℕ} (a : ⋀[K]^i (Space K (W 0) (U 0) (U' 0)))
    (b : ⋀[K]^j (MultiSpace K (fun j : Fin e => W j.succ) (fun j => U j.succ) (fun j => U' j.succ)))
    (a' : ⋀[K]^i' (Space K (W 0) (U 0) (U' 0)))
    (b' : ⋀[K]^j' (MultiSpace K (fun j : Fin e => W j.succ) (fun j => U j.succ)
      (fun j => U' j.succ))) :
    ExteriorAlgebra.map (LinearMap.single K (fun v => Space K (W v) (U v) (U' v)) 0)
          (a : ExteriorAlgebra K _) *
        ExteriorAlgebra.map (a3b_consInr (K := K)) (b : ExteriorAlgebra K _) *
      (ExteriorAlgebra.map (LinearMap.single K (fun v => Space K (W v) (U v) (U' v)) 0)
          (a' : ExteriorAlgebra K _) *
        ExteriorAlgebra.map (a3b_consInr (K := K)) (b' : ExteriorAlgebra K _)) =
      ExteriorAlgebra.map (LinearMap.single K (fun v => Space K (W v) (U v) (U' v)) 0)
          ((-1 : K) ^ (j * i') • (a.1 * a'.1)) *
        ExteriorAlgebra.map (a3b_consInr (K := K)) (b.1 * b'.1) := by
  have h := congrArg
    (ExteriorAlgebra.map (Fin.consLinearEquiv K fun v => Space K (W v) (U v) (U' v)).toLinearMap)
    (spec_a3a_exteriorProdMul_mul i j i' j' a b a' b')
  simp only [a3b_coe_exteriorProdMul, a3b_coe_wedge, map_mul, map_smul, a3b_map_cons_inl,
    a3b_map_cons_inr] at h
  rw [map_smul, smul_mul_assoc, map_mul, map_mul]
  exact h

end BlockHelpers

theorem a3b_wedge_mem_consRHS {k l : ℕ} {x : ⋀[K]^k (MultiSpace K W U U')}
    {y : ⋀[K]^l (MultiSpace K W U U')}
    (hx : x ∈ ⨆ p, LinearMap.range (a3b_consMap (K := K) (W := W) (U := U) (U' := U') k p))
    (hy : y ∈ ⨆ p, LinearMap.range (a3b_consMap (K := K) (W := W) (U := U) (U' := U') l p)) :
    exteriorPower.wedge K _ k l x y ∈
      ⨆ p, LinearMap.range (a3b_consMap (K := K) (W := W) (U := U) (U' := U') (k + l) p) := by
  refine Submodule.iSup_induction _ (motive := fun x => exteriorPower.wedge K _ k l x y ∈ _) hx
    ?_ ?_ ?_
  · rintro p _ ⟨z, rfl⟩
    refine Submodule.iSup_induction _
      (motive := fun y => exteriorPower.wedge K _ k l
        (a3b_consMap (K := K) (W := W) (U := U) (U' := U') k p z) y ∈ _) hy ?_ ?_ ?_
    · rintro p' _ ⟨z', rfl⟩
      induction z using TensorProduct.inductionOn with
      | add z₁ z₂ h₁ h₂ =>
        simpa only [map_add, LinearMap.add_apply] using Submodule.add_mem _ h₁ h₂
      | tmul g t =>
        induction z' using TensorProduct.inductionOn with
        | add z₁ z₂ h₁ h₂ => simpa only [map_add] using Submodule.add_mem _ h₁ h₂
        | tmul g' t' =>
          have e1 := a3b_coe_consMap (K := K) (W := W) (U := U) (U' := U') k p g t
          have e2 := a3b_coe_consMap (K := K) (W := W) (U := U) (U' := U') l p' g' t'
          have h := a3b_cons_sign (K := K) (W := W) (U := U) (U' := U') g.1 t.1 g'.1 t'.1
          have hk : p.1.1 + p'.1.1 + (p.1.2 + p'.1.2) = k + l := by
            have := p.2; have := p'.2; omega
          refine a3b_mem_consRHS hk
            (Submodule.smul_mem _ ((-1 : K) ^ (p.1.2 * p'.1.1))
              (wedge_mem_generatedDegree g.2 g'.2)) (a3b_wedge_mem t.2 t'.2) ?_
          exact (congrArg₂ (· * ·) e1 e2).trans h
    · simp only [map_zero, Submodule.zero_mem]
    · intro y₁ y₂ h₁ h₂
      simpa only [map_add] using Submodule.add_mem _ h₁ h₂
  · simp only [map_zero, LinearMap.zero_apply, Submodule.zero_mem]
  · intro x₁ x₂ h₁ h₂
    simpa only [map_add, LinearMap.add_apply] using Submodule.add_mem _ h₁ h₂

theorem spec_a3b_multiGeneratedDegree_cons_aux (k : ℕ) :
    multiGeneratedDegree (K := K) (W := W) (U := U) (U' := U') k =
      ⨆ p : {p : ℕ × ℕ // p.1 + p.2 = k},
        LinearMap.range
          (exteriorPower.map k
              (Fin.consLinearEquiv K fun v => Space K (W v) (U v) (U' v)).toLinearMap ∘ₗ
            exteriorProdDegree k ∘ₗ
            DirectSum.lof K _ (fun p : {p : ℕ × ℕ // p.1 + p.2 = k} =>
              ⋀[K]^p.1.1 (Space K (W 0) (U 0) (U' 0)) ⊗[K]
                ⋀[K]^p.1.2 (MultiSpace K (fun j : Fin e => W j.succ)
                  (fun j => U j.succ) (fun j => U' j.succ))) p ∘ₗ
            TensorProduct.map
              (generatedDegree (K := K) (W := W 0) (U := U 0) (U' := U' 0) p.1.1).subtype
              (multiGeneratedDegree (K := K) (W := fun j : Fin e => W j.succ)
                (U := fun j => U j.succ) (U' := fun j => U' j.succ) p.1.2).subtype) := by
  show _ = ⨆ p, LinearMap.range (a3b_consMap (K := K) (W := W) (U := U) (U' := U') k p)
  apply le_antisymm
  · refine Submodule.span_le.mpr fun x hx => ?_
    change MultiGeneratorProduct k x at hx
    induction hx with
    | unit =>
      have hg := Submodule.subset_span (R := K)
        (GeneratorProduct.unit (K := K) (W := W 0) (U := U 0) (U' := U' 0))
      have ht := Submodule.subset_span (R := K)
        (MultiGeneratorProduct.unit (K := K) (W := fun j : Fin e => W j.succ)
          (U := fun j => U j.succ) (U' := fun j => U' j.succ))
      exact a3b_mem_consRHS (i := 0) (j := 0) rfl hg ht (a3b_unit_eq_mul _ _)
    | @block v k g hg =>
      induction v using Fin.cases with
      | zero =>
        have ht := Submodule.subset_span (R := K)
          (MultiGeneratorProduct.unit (K := K) (W := fun j : Fin e => W j.succ)
            (U := fun j => U j.succ) (U' := fun j => U' j.succ))
        exact a3b_mem_consRHS (add_zero k) (Submodule.subset_span hg) ht
          (a3b_map_eq_mul_unit _ _ g)
      | succ j =>
        have hg0 := Submodule.subset_span (R := K)
          (GeneratorProduct.unit (K := K) (W := W 0) (U := U 0) (U' := U' 0))
        refine a3b_mem_consRHS (zero_add k) hg0
          (Submodule.subset_span (MultiGeneratorProduct.block j hg)) ?_
        rw [← a3b_consInr_single]
        exact a3b_map_comp_eq_unit_mul _ _ _ g
    | wedge _ _ hx hy => exact a3b_wedge_mem_consRHS hx hy
  · refine iSup_le fun p => ?_
    intro x hx
    obtain ⟨z, rfl⟩ := LinearMap.mem_range.mp hx
    clear hx
    induction z using TensorProduct.inductionOn with
    | add z₁ z₂ h₁ h₂ => rw [map_add]; exact Submodule.add_mem _ h₁ h₂
    | tmul g t =>
      exact a3b_mem_of_coe_eq p.2.symm
        ((a3b_coe_consMap k p g t).trans (a3b_coe_wedge_map _ _ g.1 t.1).symm)
        (a3b_wedge_mem (a3b_map_single_mem 0 g.2) (a3b_consInr_mem t.2))

omit [CharZero K] in
theorem a3b_subsingleton_space {W U U' : Type*} [AddCommGroup W] [Module K W] [AddCommGroup U]
    [Module K U] [AddCommGroup U'] [Module K U'] [Subsingleton W] :
    Subsingleton (Space K W U U') := by
  have : Subsingleton (Module.Dual K W) := inferInstance
  infer_instance

omit [CharZero K] in
theorem a3b_mem_map_consInr_zero (x : ⋀[K]^0 (MultiSpace K W U U')) :
    x ∈ Submodule.map (exteriorPower.map 0 (a3b_consInr (K := K)))
      (multiGeneratedDegree (K := K) (W := fun j : Fin e => W j.succ)
        (U := fun j => U j.succ) (U' := fun j => U' j.succ) 0) := by
  have hx : x ∈ (⊤ : Submodule K (⋀[K]^0 (MultiSpace K W U U'))) := trivial
  rw [← exteriorPower.ιMulti_span K 0 (MultiSpace K W U U')] at hx
  refine Submodule.span_le.mpr ?_ hx
  rintro _ ⟨v, rfl⟩
  have hv : v = Fin.elim0 := funext (fun i => Fin.elim0 i)
  rw [hv]
  exact ⟨_, Submodule.subset_span MultiGeneratorProduct.unit, a3b_map_unit _⟩

set_option linter.unusedSectionVars false in
theorem spec_a3b_multiGeneratedDegree_of_subsingleton_aux [Subsingleton (W 0)] (k : ℕ) :
    multiGeneratedDegree (K := K) (W := W) (U := U) (U' := U') k =
      Submodule.map
        (exteriorPower.map k
          ((Fin.consLinearEquiv K fun v => Space K (W v) (U v) (U' v)).toLinearMap ∘ₗ
            LinearMap.inr K (Space K (W 0) (U 0) (U' 0))
              (MultiSpace K (fun j : Fin e => W j.succ) (fun j => U j.succ)
                (fun j => U' j.succ))))
        (multiGeneratedDegree (K := K) (W := fun j : Fin e => W j.succ)
          (U := fun j => U j.succ) (U' := fun j => U' j.succ) k) := by
  apply le_antisymm
  · rw [multiGeneratedDegree, Submodule.span_le]
    intro x (hx : MultiGeneratorProduct k x)
    induction hx with
    | unit =>
      exact ⟨_, by rw [a3b_multiGeneratedDegree_zero]; trivial, a3b_map_unit _⟩
    | @block v k g hg =>
      induction v using Fin.cases with
      | zero =>
        rcases Nat.eq_zero_or_pos k with rfl | hk
        · exact a3b_mem_map_consInr_zero _
        · have := a3b_subsingleton_space (K := K) (W := W 0) (U := U 0) (U' := U' 0)
          have := a3a_subsingleton_exteriorPower (K := K)
            (S₂ := Space K (W 0) (U 0) (U' 0)) hk.ne'
          rw [Subsingleton.elim g 0, map_zero]
          exact Submodule.zero_mem _
      | succ j =>
        refine ⟨_, Submodule.subset_span (MultiGeneratorProduct.block j hg), ?_⟩
        rw [← LinearMap.comp_apply, ← exteriorPower.map_comp, a3b_consInr_single]
    | wedge _ _ hx hy =>
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      exact ⟨_, a3b_wedge_mem ha hb, a3b_map_wedge _ _ _⟩
  · rw [Submodule.map_le_iff_le_comap]
    intro t ht
    exact a3b_consInr_mem ht

end Blocks

section Main

/-- The joint kernel of the `𝔰𝔩(W)` derivations on `⋀^k Space` is the single-block
`generatedDegree k` (F-1575 (1) in joint-kernel form). -/
theorem a3b_iInf_ker_eq_generatedDegree {W U U' : Type*}
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    [AddCommGroup U'] [Module K U'] [FiniteDimensional K U'] (k : ℕ) :
    (⨅ f : slEnd K W, LinearMap.ker (exteriorDer k (multiplicityLie K W U U' f))) =
      generatedDegree (K := K) (W := W) (U := U) (U' := U') k := by
  rw [← invariants_eq_generatedDegree k]
  ext x
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LieSubmodule.mem_toSubmodule,
    LieModule.mem_maxTrivSubmodule, LieSubalgebra.coe_bracket_of_module, lie_eq_exteriorDer]

/-- The derivation of the zero endomorphism is zero. -/
theorem a3b_exteriorDer_zero {M : Type*} [AddCommGroup M] [Module K M] (k : ℕ) :
    exteriorDer k (0 : Module.End K M) = 0 := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  simp only [LinearMap.compAlternatingMap_apply, exteriorDer_ιMulti, LinearMap.zero_apply,
    AlternatingMap.map_update_zero, Finset.sum_const_zero]

omit [CharZero K] in
/-- Congruence in the two factors of one summand of the splitting of `⋀^k` over `Fin (e + 1)`
(the submodules occur in the type of the tensor product, so `rw` cannot do this). -/
theorem a3b_cons_range_congr {e : ℕ} {W U U' : Fin (e + 1) → Type*}
    [∀ v, AddCommGroup (W v)] [∀ v, Module K (W v)]
    [∀ v, AddCommGroup (U v)] [∀ v, Module K (U v)]
    [∀ v, AddCommGroup (U' v)] [∀ v, Module K (U' v)]
    (k : ℕ) (p : {p : ℕ × ℕ // p.1 + p.2 = k})
    {S S' : Submodule K (⋀[K]^p.1.1 (Space K (W 0) (U 0) (U' 0)))}
    {T T' : Submodule K (⋀[K]^p.1.2 (MultiSpace K (fun j : Fin e => W j.succ)
      (fun j => U j.succ) (fun j => U' j.succ)))} (hS : S = S') (hT : T = T') :
    LinearMap.range
        (exteriorPower.map k
            (Fin.consLinearEquiv K fun v => Space K (W v) (U v) (U' v)).toLinearMap ∘ₗ
          exteriorProdDegree k ∘ₗ
          DirectSum.lof K _ (fun p : {p : ℕ × ℕ // p.1 + p.2 = k} =>
            ⋀[K]^p.1.1 (Space K (W 0) (U 0) (U' 0)) ⊗[K]
              ⋀[K]^p.1.2 (MultiSpace K (fun j : Fin e => W j.succ)
                (fun j => U j.succ) (fun j => U' j.succ))) p ∘ₗ
          TensorProduct.map S.subtype T.subtype) =
      LinearMap.range
        (exteriorPower.map k
            (Fin.consLinearEquiv K fun v => Space K (W v) (U v) (U' v)).toLinearMap ∘ₗ
          exteriorProdDegree k ∘ₗ
          DirectSum.lof K _ (fun p : {p : ℕ × ℕ // p.1 + p.2 = k} =>
            ⋀[K]^p.1.1 (Space K (W 0) (U 0) (U' 0)) ⊗[K]
              ⋀[K]^p.1.2 (MultiSpace K (fun j : Fin e => W j.succ)
                (fun j => U j.succ) (fun j => U' j.succ))) p ∘ₗ
          TensorProduct.map S'.subtype T'.subtype) := by
  subst hS hT; rfl

omit [CharZero K] in
/-- With no blocks, `multiGeneratedDegree k` is everything. -/
theorem a3b_multiGeneratedDegree_fin_zero {W U U' : Fin 0 → Type*}
    [∀ v, AddCommGroup (W v)] [∀ v, Module K (W v)] [∀ v, FiniteDimensional K (W v)]
    [∀ v, AddCommGroup (U v)] [∀ v, Module K (U v)]
    [∀ v, AddCommGroup (U' v)] [∀ v, Module K (U' v)] (k : ℕ) :
    multiGeneratedDegree (K := K) (W := W) (U := U) (U' := U') k = ⊤ := by
  rw [eq_top_iff, ← exteriorPower.ιMulti_span, multiGeneratedDegree]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨v, rfl⟩
  cases k with
  | zero =>
    rw [show v = Fin.elim0 from Subsingleton.elim _ _]
    exact Submodule.subset_span MultiGeneratorProduct.unit
  | succ k =>
    have hv : Function.update v 0 0 = v := by
      rw [show (0 : MultiSpace K W U U') = v 0 from Subsingleton.elim _ _,
        Function.update_eq_self]
    rw [← hv, AlternatingMap.map_update_zero]
    exact Submodule.zero_mem _

theorem a3b_invariants_eq_multiGeneratedDegree : ∀ (e : ℕ) {W U U' : Fin e → Type*}
    [∀ v, AddCommGroup (W v)] [∀ v, Module K (W v)] [∀ v, FiniteDimensional K (W v)]
    [∀ v, AddCommGroup (U v)] [∀ v, Module K (U v)] [∀ v, FiniteDimensional K (U v)]
    [∀ v, AddCommGroup (U' v)] [∀ v, Module K (U' v)] [∀ v, FiniteDimensional K (U' v)]
    (k : ℕ),
    (⨅ f : (v : Fin e) → slEnd K (W v),
        LinearMap.ker (exteriorDer k
          (LinearMap.piMap fun v => multiplicityLie K (W v) (U v) (U' v) (f v)))) =
      multiGeneratedDegree (K := K) (W := W) (U := U) (U' := U') k
  | 0, W, U, U', _, _, _, _, _, _, _, _, _, k => by
    rw [a3b_multiGeneratedDegree_fin_zero k, eq_top_iff]
    intro x _
    simp only [Submodule.mem_iInf, LinearMap.mem_ker]
    intro f
    have h0 : (LinearMap.piMap fun v => multiplicityLie K (W v) (U v) (U' v) (f v)) = 0 := by
      apply LinearMap.ext; intro y; funext v; exact v.elim0
    rw [h0, a3b_exteriorDer_zero, LinearMap.zero_apply]
  | e + 1, W, U, U', _, _, _, _, _, _, _, _, _, k => by
    refine (spec_a3b_invariants_cons_aux (K := K) (W := W) (U := U) (U' := U') k).trans ?_
    refine Eq.trans ?_
      (spec_a3b_multiGeneratedDegree_cons_aux (K := K) (W := W) (U := U) (U' := U') k).symm
    refine iSup_congr fun p => ?_
    have h1 := a3b_iInf_ker_eq_generatedDegree (K := K) (W := W 0) (U := U 0) (U' := U' 0) p.1.1
    have h2 := a3b_invariants_eq_multiGeneratedDegree e (W := fun j : Fin e => W j.succ)
        (U := fun j => U j.succ) (U' := fun j => U' j.succ) p.1.2
    exact a3b_cons_range_congr k p h1 h2


variable {e : ℕ} {W U U' : Fin e → Type*}
  [∀ v, AddCommGroup (W v)] [∀ v, Module K (W v)] [∀ v, FiniteDimensional K (W v)]
  [∀ v, AddCommGroup (U v)] [∀ v, Module K (U v)]
  [∀ v, AddCommGroup (U' v)] [∀ v, Module K (U' v)]

theorem spec_a3b_invariants_eq_multiGeneratedDegree_aux [∀ v, FiniteDimensional K (U v)]
    [∀ v, FiniteDimensional K (U' v)] (k : ℕ) :
    (⨅ f : (v : Fin e) → slEnd K (W v),
        LinearMap.ker (exteriorDer k
          (LinearMap.piMap fun v => multiplicityLie K (W v) (U v) (U' v) (f v)))) =
      multiGeneratedDegree (K := K) (W := W) (U := U) (U' := U') k :=
  a3b_invariants_eq_multiGeneratedDegree e k

omit [CharZero K] in
/-- Graded commutativity of homogeneous elements of the exterior algebra. -/
theorem a3b_mul_anticomm {M : Type*} [AddCommGroup M] [Module K M] {i j : ℕ}
    {x y : ExteriorAlgebra K M} (hx : x ∈ ⋀[K]^i M) (hy : y ∈ ⋀[K]^j M) :
    x * y = ((-1 : ℤˣ) ^ (j * i)) • (y * x) := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hx hy
  refine Submodule.span_induction₂ (p := fun x y _ _ =>
    x * y = ((-1 : ℤˣ) ^ (j * i)) • (y * x)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨u, rfl⟩ ⟨v, rfl⟩
    exact ExteriorAlgebra.ιMulti_mul_ιMulti_anticomm K u v
  all_goals simp +contextual [add_mul, mul_add]
  all_goals intro r _ _ _ _ _; exact smul_comm _ _ _

omit [CharZero K] in
/-- Submodules of homogeneous elements commute, as submodules of the exterior algebra. -/
theorem a3b_submodule_commute {M : Type*} [AddCommGroup M] [Module K M] {i j : ℕ}
    {S T : Submodule K (ExteriorAlgebra K M)} (hS : S ≤ ⋀[K]^i M) (hT : T ≤ ⋀[K]^j M) :
    Commute S T := by
  have key : ∀ {i j : ℕ} {S T : Submodule K (ExteriorAlgebra K M)},
      S ≤ ⋀[K]^i M → T ≤ ⋀[K]^j M → S * T ≤ T * S := by
    intro i j S T hS hT
    rw [Submodule.mul_le]
    intro x hx y hy
    rw [a3b_mul_anticomm (hS hx) (hT hy), Units.smul_def]
    exact zsmul_mem (Submodule.mul_mem_mul hy hx) _
  exact le_antisymm (key hS hT) (key hT hS)

omit [CharZero K] in
/-- The image of `⋀^n N` under `⋀ f` lies in `⋀^n M`. -/
theorem a3b_map_le_exteriorPower {M N : Type*} [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] (f : N →ₗ[K] M) (n : ℕ) (S : Submodule K (⋀[K]^n N)) :
    Submodule.map ((ExteriorAlgebra.map f).toLinearMap ∘ₗ (⋀[K]^n N).subtype) S ≤
      ⋀[K]^n M := by
  rintro _ ⟨x, _, rfl⟩
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
    AlgHom.toLinearMap_apply]
  rw [← exteriorPower.coe_map]
  exact (exteriorPower.map n f x).2

omit [CharZero K] in
theorem a3b_prod_ofFn_mono {A : Type*} [Ring A] [Algebra K A] :
    ∀ (n : ℕ) (f g : Fin n → Submodule K A), (∀ i, f i ≤ g i) →
      (List.ofFn f).prod ≤ (List.ofFn g).prod
  | 0, _, _, _ => le_rfl
  | n + 1, f, g, h => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons]
    exact mul_le_mul' (h 0) (a3b_prod_ofFn_mono n _ _ fun i => h i.succ)

omit [CharZero K] in
theorem a3b_one_le_prod_ofFn {A : Type*} [Ring A] [Algebra K A] :
    ∀ (n : ℕ) (f : Fin n → Submodule K A), (∀ i, 1 ≤ f i) → 1 ≤ (List.ofFn f).prod
  | 0, _, _ => le_rfl
  | n + 1, f, h => by
    rw [List.ofFn_succ, List.prod_cons, ← one_mul (1 : Submodule K A)]
    exact mul_le_mul' (h 0) (a3b_one_le_prod_ofFn n _ fun i => h i.succ)

omit [CharZero K] in
theorem a3b_mem_prod_ofFn_of_mem {A : Type*} [Ring A] [Algebra K A] :
    ∀ (n : ℕ) (f : Fin n → Submodule K A) (v : Fin n) {x : A}, (∀ w, w ≠ v → 1 ≤ f w) →
      x ∈ f v → x ∈ (List.ofFn f).prod
  | 0, _, v, _, _, _ => v.elim0
  | n + 1, f, v, x, h, hx => by
    rw [List.ofFn_succ, List.prod_cons]
    cases v using Fin.cases with
    | zero =>
      rw [← mul_one x]
      exact Submodule.mul_mem_mul hx (Submodule.one_le.mp
        (a3b_one_le_prod_ofFn n _ fun i => h i.succ (Fin.succ_ne_zero i)))
    | succ v =>
      rw [← one_mul x]
      exact Submodule.mul_mem_mul (Submodule.one_le.mp (h 0 (Fin.succ_ne_zero v).symm))
        (a3b_mem_prod_ofFn_of_mem n _ v (fun w hw => h w.succ (fun h' => hw (Fin.succ_injective _ h')))
          hx)

omit [CharZero K] in
theorem a3b_prod_ofFn_mul {A : Type*} [Ring A] [Algebra K A] :
    ∀ (n : ℕ) (f g : Fin n → Submodule K A), (∀ i j, Commute (f i) (g j)) →
      (List.ofFn f).prod * (List.ofFn g).prod = (List.ofFn fun i => f i * g i).prod
  | 0, _, _, _ => by simp
  | n + 1, f, g, h => by
    rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons,
      List.prod_cons, ← a3b_prod_ofFn_mul n (fun i => f i.succ) (fun i => g i.succ)
        fun i j => h _ _]
    have hc : Commute (List.ofFn fun i => f i.succ).prod (g 0) := by
      refine Commute.list_prod_left _ _ fun x hx => ?_
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
      exact h _ _
    rw [mul_assoc, ← mul_assoc _ (g 0), hc.eq, mul_assoc, mul_assoc]

omit [CharZero K] in
theorem a3b_wedge_mem_multiGeneratedDegree {a b : ℕ}
    {x : ⋀[K]^a (MultiSpace K W U U')} {y : ⋀[K]^b (MultiSpace K W U U')}
    (hx : x ∈ multiGeneratedDegree (K := K) (W := W) (U := U) (U' := U') a)
    (hy : y ∈ multiGeneratedDegree (K := K) (W := W) (U := U) (U' := U') b) :
    exteriorPower.wedge K _ a b x y ∈
      multiGeneratedDegree (K := K) (W := W) (U := U) (U' := U') (a + b) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    induction hy using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span (MultiGeneratorProduct.wedge hx hy)
    | zero => simp only [map_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => simpa only [map_add] using Submodule.add_mem _ hy hz
    | smul c y _ hy => simpa only [map_smul] using Submodule.smul_mem _ c hy
  | zero => simp only [map_zero, LinearMap.zero_apply]; exact Submodule.zero_mem _
  | add x z _ _ hx hz =>
    simpa only [map_add, LinearMap.add_apply] using Submodule.add_mem _ hx hz
  | smul c x _ hx =>
    simpa only [map_smul, LinearMap.smul_apply] using Submodule.smul_mem _ c hx

omit [CharZero K] in
theorem a3b_coe_wedge_c {M : Type*} [AddCommGroup M] [Module K M] {m n : ℕ}
    (x : ⋀[K]^m M) (y : ⋀[K]^n M) :
    (exteriorPower.wedge K M m n x y : ExteriorAlgebra K M) = x * y := by
  simp [DirectSum.gMulLHom_apply_apply, SetLike.coe_gMul]

omit [CharZero K] in
/-- Every `MultiGeneratorProduct` lies in any graded family of submodules of the exterior algebra
that contains `1` in degree `0`, the block images of the generator products, and is closed under
multiplication. -/
theorem a3b_mem_of_multiGeneratorProduct
    (R : ℕ → Submodule K (ExteriorAlgebra K (MultiSpace K W U U')))
    (h1 : (1 : ExteriorAlgebra K (MultiSpace K W U U')) ∈ R 0)
    (hblock : ∀ (v : Fin e) (n : ℕ) (g : ⋀[K]^n (Space K (W v) (U v) (U' v))),
      GeneratorProduct n g →
        ExteriorAlgebra.map (LinearMap.single K (fun v => Space K (W v) (U v) (U' v)) v)
          (g : ExteriorAlgebra K (Space K (W v) (U v) (U' v))) ∈ R n)
    (hmul : ∀ a b, R a * R b ≤ R (a + b)) {k : ℕ} {x : ⋀[K]^k (MultiSpace K W U U')}
    (hx : MultiGeneratorProduct k x) : (x : ExteriorAlgebra K (MultiSpace K W U U')) ∈ R k := by
  induction hx with
  | unit =>
    rw [exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_zero_apply]
    exact h1
  | block v hg =>
    rw [exteriorPower.coe_map]
    exact hblock v _ _ hg
  | wedge _ _ ihx ihy =>
    rw [a3b_coe_wedge_c]
    exact hmul _ _ (Submodule.mul_mem_mul ihx ihy)

omit [CharZero K] in
/-- An ordered product of submodules, each inside a graded piece of a multiplicatively closed
graded family, lies in the piece of the total degree. -/
theorem a3b_prod_ofFn_le {A : Type*} [Ring A] [Algebra K A] (P : ℕ → Submodule K A)
    (h1 : 1 ≤ P 0) (hmul : ∀ a b, P a * P b ≤ P (a + b)) :
    ∀ (n : ℕ) (d : Fin n → ℕ) (S : Fin n → Submodule K A), (∀ i, S i ≤ P (d i)) →
      (List.ofFn S).prod ≤ P (∑ i, d i)
  | 0, _, _, _ => by simpa using h1
  | n + 1, d, S, h => by
    rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ]
    exact (mul_le_mul' (h 0)
      (a3b_prod_ofFn_le P h1 hmul n (fun i => d i.succ) (fun i => S i.succ) fun i => h i.succ)).trans
      (hmul _ _)

/-- The image of `generatedDegree` of one block, in the exterior algebra of all blocks, is
closed under products. -/
theorem a3b_block_mul_le (v : Fin e) (a b : ℕ) :
    Submodule.map
        ((ExteriorAlgebra.map
            (LinearMap.single K (fun v => Space K (W v) (U v) (U' v)) v)).toLinearMap ∘ₗ
          (⋀[K]^a (Space K (W v) (U v) (U' v))).subtype)
        (generatedDegree (K := K) (W := W v) (U := U v) (U' := U' v) a) *
      Submodule.map
        ((ExteriorAlgebra.map
            (LinearMap.single K (fun v => Space K (W v) (U v) (U' v)) v)).toLinearMap ∘ₗ
          (⋀[K]^b (Space K (W v) (U v) (U' v))).subtype)
        (generatedDegree (K := K) (W := W v) (U := U v) (U' := U' v) b) ≤
    Submodule.map
        ((ExteriorAlgebra.map
            (LinearMap.single K (fun v => Space K (W v) (U v) (U' v)) v)).toLinearMap ∘ₗ
          (⋀[K]^(a + b) (Space K (W v) (U v) (U' v))).subtype)
        (generatedDegree (K := K) (W := W v) (U := U v) (U' := U' v) (a + b)) := by
  rw [Submodule.mul_le]
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  refine ⟨exteriorPower.wedge K _ a b x y, wedge_mem_generatedDegree hx hy, ?_⟩
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
    AlgHom.toLinearMap_apply, a3b_coe_wedge_c, map_mul]

omit [CharZero K] in
theorem a3b_one_mem_block (v : Fin e) :
    (1 : ExteriorAlgebra K (MultiSpace K W U U')) ∈ Submodule.map
        ((ExteriorAlgebra.map
            (LinearMap.single K (fun v => Space K (W v) (U v) (U' v)) v)).toLinearMap ∘ₗ
          (⋀[K]^0 (Space K (W v) (U v) (U' v))).subtype)
        (generatedDegree (K := K) (W := W v) (U := U v) (U' := U' v) 0) := by
  refine ⟨_, Submodule.subset_span GeneratorProduct.unit, ?_⟩
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
    AlgHom.toLinearMap_apply, exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_zero_apply,
    map_one]

theorem spec_a3b_multiGeneratedDegree_eq_iSup_prod_aux (k : ℕ) :
    Submodule.map (⋀[K]^k (MultiSpace K W U U')).subtype
        (multiGeneratedDegree (K := K) (W := W) (U := U) (U' := U') k) =
      ⨆ d : {d : Fin e → ℕ // ∑ v, d v = k},
        (List.ofFn fun v => Submodule.map
          ((ExteriorAlgebra.map
              (LinearMap.single K (fun v => Space K (W v) (U v) (U' v)) v)).toLinearMap ∘ₗ
            (⋀[K]^(d.1 v) (Space K (W v) (U v) (U' v))).subtype)
          (generatedDegree (K := K) (W := W v) (U := U v) (U' := U' v) (d.1 v))).prod := by
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap, multiGeneratedDegree, Submodule.span_le]
    intro x hx
    rw [SetLike.mem_coe, Submodule.mem_comap, Submodule.coe_subtype]
    refine a3b_mem_of_multiGeneratorProduct (fun k => ⨆ d : {d : Fin e → ℕ // ∑ v, d v = k},
      (List.ofFn fun v => Submodule.map
        ((ExteriorAlgebra.map
            (LinearMap.single K (fun v => Space K (W v) (U v) (U' v)) v)).toLinearMap ∘ₗ
          (⋀[K]^(d.1 v) (Space K (W v) (U v) (U' v))).subtype)
        (generatedDegree (K := K) (W := W v) (U := U v) (U' := U' v) (d.1 v))).prod)
      ?_ ?_ ?_ hx
    · refine Submodule.mem_iSup_of_mem ⟨0, by simp⟩ ?_
      exact Submodule.one_le.mp
        (a3b_one_le_prod_ofFn _ _ fun v => Submodule.one_le.mpr (a3b_one_mem_block v))
    · intro v n g hg
      refine Submodule.mem_iSup_of_mem ⟨Pi.single v n, by simp⟩ ?_
      refine a3b_mem_prod_ofFn_of_mem _ _ v ?_ ?_
      · intro w hw
        have key : ∀ m : ℕ, m = 0 → (1 : ExteriorAlgebra K (MultiSpace K W U U')) ∈
            Submodule.map
              ((ExteriorAlgebra.map
                  (LinearMap.single K (fun v => Space K (W v) (U v) (U' v)) w)).toLinearMap ∘ₗ
                (⋀[K]^m (Space K (W w) (U w) (U' w))).subtype)
              (generatedDegree (K := K) (W := W w) (U := U w) (U' := U' w) m) := by
          rintro m rfl
          exact a3b_one_mem_block w
        exact Submodule.one_le.mpr (key _ (by simp [hw]))
      · have key : ∀ m : ℕ, n = m →
            ExteriorAlgebra.map (LinearMap.single K (fun v => Space K (W v) (U v) (U' v)) v)
              (g : ExteriorAlgebra K (Space K (W v) (U v) (U' v))) ∈
            Submodule.map
              ((ExteriorAlgebra.map
                  (LinearMap.single K (fun v => Space K (W v) (U v) (U' v)) v)).toLinearMap ∘ₗ
                (⋀[K]^m (Space K (W v) (U v) (U' v))).subtype)
              (generatedDegree (K := K) (W := W v) (U := U v) (U' := U' v) m) := by
          rintro m rfl
          exact ⟨g, Submodule.subset_span hg, rfl⟩
        exact key _ (by simp)
    · intro a b
      rw [Submodule.iSup_mul]
      refine iSup_le fun d => ?_
      rw [Submodule.mul_iSup]
      refine iSup_le fun d' => ?_
      rw [a3b_prod_ofFn_mul _ _ _ fun i j => a3b_submodule_commute
        (a3b_map_le_exteriorPower _ _ _) (a3b_map_le_exteriorPower _ _ _)]
      refine le_trans ?_ (le_iSup _ ⟨d.1 + d'.1, by simp [Finset.sum_add_distrib, d.2, d'.2]⟩)
      exact a3b_prod_ofFn_mono _ _ _ fun v => a3b_block_mul_le v _ _
  · refine iSup_le fun d => ?_
    obtain ⟨d, rfl⟩ := d
    refine a3b_prod_ofFn_le (fun n => Submodule.map (⋀[K]^n (MultiSpace K W U U')).subtype
      (multiGeneratedDegree (K := K) (W := W) (U := U) (U' := U') n)) ?_ ?_ e d _ ?_
    · rw [Submodule.one_le]
      refine ⟨_, Submodule.subset_span MultiGeneratorProduct.unit, ?_⟩
      simp only [Submodule.coe_subtype, exteriorPower.ιMulti_apply_coe,
        ExteriorAlgebra.ιMulti_zero_apply]
    · intro a b
      rw [Submodule.mul_le]
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      exact ⟨_, a3b_wedge_mem_multiGeneratedDegree hx hy, a3b_coe_wedge_c x y⟩
    · intro v
      rintro _ ⟨g, hg, rfl⟩
      refine ⟨exteriorPower.map _ (LinearMap.single K (fun v => Space K (W v) (U v) (U' v)) v) g,
        ?_, ?_⟩
      · refine (Submodule.span_le (p := Submodule.comap (exteriorPower.map _
          (LinearMap.single K (fun v => Space K (W v) (U v) (U' v)) v))
          (multiGeneratedDegree (K := K) (W := W) (U := U) (U' := U') _))).mpr ?_ hg
        intro g hg
        exact Submodule.subset_span (MultiGeneratorProduct.block v hg)
      · simp only [Submodule.coe_subtype, exteriorPower.coe_map, LinearMap.coe_comp,
          Function.comp_apply, AlgHom.toLinearMap_apply]

set_option linter.unusedSectionVars false in
theorem spec_a3b_multiGeneratedDegree_zero_aux :
    multiGeneratedDegree (K := K) (W := W) (U := U) (U' := U') 0 = ⊤ :=
  a3b_multiGeneratedDegree_zero

end Main

section Degenerate

set_option linter.unusedSectionVars false in
theorem spec_a3b_multiGeneratedDegree_fin_zero_aux {W U U' : Fin 0 → Type*}
    [∀ v, AddCommGroup (W v)] [∀ v, Module K (W v)] [∀ v, FiniteDimensional K (W v)]
    [∀ v, AddCommGroup (U v)] [∀ v, Module K (U v)]
    [∀ v, AddCommGroup (U' v)] [∀ v, Module K (U' v)] (k : ℕ) :
    multiGeneratedDegree (K := K) (W := W) (U := U) (U' := U') k = ⊤ := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact a3b_multiGeneratedDegree_zero
  · have := a3a_subsingleton_exteriorPower (K := K) (S₂ := MultiSpace K W U U') hk.ne'
    exact eq_top_iff.mpr fun x _ => Subsingleton.elim x 0 ▸ Submodule.zero_mem _

theorem spec_a3b_multiGeneratedDegree_fin_one_aux {W U U' : Fin 1 → Type*}
    [∀ v, AddCommGroup (W v)] [∀ v, Module K (W v)] [∀ v, FiniteDimensional K (W v)]
    [∀ v, AddCommGroup (U v)] [∀ v, Module K (U v)]
    [∀ v, AddCommGroup (U' v)] [∀ v, Module K (U' v)] (k : ℕ) :
    multiGeneratedDegree (K := K) (W := W) (U := U) (U' := U') k =
      Submodule.map
        (exteriorPower.map k (LinearMap.single K (fun v => Space K (W v) (U v) (U' v)) 0))
        (generatedDegree (K := K) (W := W 0) (U := U 0) (U' := U' 0) k) := by
  apply le_antisymm
  · rw [multiGeneratedDegree, Submodule.span_le]
    intro x (hx : MultiGeneratorProduct k x)
    induction hx with
    | unit => exact ⟨_, Submodule.subset_span GeneratorProduct.unit, a3b_map_unit _⟩
    | @block v k g hg =>
      obtain rfl : v = 0 := Subsingleton.elim _ _
      exact ⟨_, Submodule.subset_span hg, rfl⟩
    | wedge _ _ hx hy =>
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      exact ⟨_, wedge_mem_generatedDegree ha hb, a3b_map_wedge _ _ _⟩
  · rw [Submodule.map_le_iff_le_comap]
    intro g hg
    exact a3b_map_single_mem 0 hg

set_option linter.unusedSectionVars false in
theorem spec_a3b_detW_blocks_anticomm_aux :
    let x : ExteriorAlgebra K (MultiSpace K (fun _ : Fin 2 => K) (fun _ => K) (fun _ => K)) :=
      (exteriorPower.map _ (LinearMap.single K (fun _ : Fin 2 => Space K K K K) 0)
        (detW (K := K) (W := K) (U' := K) (1 : K)) :)
    let y : ExteriorAlgebra K (MultiSpace K (fun _ : Fin 2 => K) (fun _ => K) (fun _ => K)) :=
      (exteriorPower.map _ (LinearMap.single K (fun _ : Fin 2 => Space K K K K) 1)
        (detW (K := K) (W := K) (U' := K) (1 : K)) :)
    x * y = -(y * x) ∧ x * y ≠ 0 := by
  intro x y
  have key : ∀ (n : ℕ) (hn : n = 1) (f : Fin n → Space K K K K) (v : Fin 2),
      ((exteriorPower.map n (LinearMap.single K (fun _ : Fin 2 => Space K K K K) v)
        (exteriorPower.ιMulti K n f) : ⋀[K]^n _) : ExteriorAlgebra K _) =
        ExteriorAlgebra.ι K (Pi.single (M := fun _ : Fin 2 => Space K K K K) v (f ⟨0, by omega⟩)) := by
    rintro n rfl f v
    rw [exteriorPower.map_apply_ιMulti, exteriorPower.ιMulti_apply_coe,
      ExteriorAlgebra.ιMulti_apply]
    simp
  set b := Module.finBasis K K ⟨0, by rw [Module.finrank_self]; omega⟩ with hb
  have hx : x = ExteriorAlgebra.ι K (Pi.single (M := fun _ : Fin 2 => Space K K K K) 0 ((b ⊗ₜ[K] (1 : K), 0) : Space K K K K)) := by
    simp only [x]
    rw [detW_eq]
    exact key _ (Module.finrank_self K) _ _
  have hy : y = ExteriorAlgebra.ι K (Pi.single (M := fun _ : Fin 2 => Space K K K K) 1 ((b ⊗ₜ[K] (1 : K), 0) : Space K K K K)) := by
    simp only [y]
    rw [detW_eq]
    exact key _ (Module.finrank_self K) _ _
  rw [hx, hy]
  refine ⟨eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _), ?_⟩
  intro h0
  set u : MultiSpace K (fun _ : Fin 2 => K) (fun _ => K) (fun _ => K) :=
    Pi.single 0 ((b ⊗ₜ[K] (1 : K), 0) : Space K K K K)
  set w : MultiSpace K (fun _ : Fin 2 => K) (fun _ => K) (fun _ => K) :=
    Pi.single 1 ((b ⊗ₜ[K] (1 : K), 0) : Space K K K K)
  have hι : exteriorPower.ιMulti K 2 ![u, w] = 0 := by
    apply Subtype.ext
    rw [exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply]
    simpa [List.ofFn_succ] using h0
  let c : Space K K K K →ₗ[K] K := (TensorProduct.lid K K).toLinearMap ∘ₗ LinearMap.fst K _ _
  let φ : MultiSpace K (fun _ : Fin 2 => K) (fun _ => K) (fun _ => K) →ₗ[K] (Fin 2 → K) :=
    LinearMap.pi fun i => c ∘ₗ LinearMap.proj i
  have hD := congrArg (exteriorPower.alternatingMapLinearEquiv
    ((Pi.basisFun K (Fin 2)).det.compLinearMap φ)) hι
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, map_zero] at hD
  have hb0 : b ≠ 0 := Basis.ne_zero _ _
  rw [AlternatingMap.compLinearMap_apply, Basis.det_apply, Matrix.det_fin_two] at hD
  simp [φ, c, u, w, Basis.toMatrix_apply] at hD
  exact hb0 hD

end Degenerate

end HodgeLean.Foundations
