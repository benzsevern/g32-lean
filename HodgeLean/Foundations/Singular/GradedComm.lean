import HodgeLean.Foundations.Singular.CupOne

/-!
# Graded commutativity of the singular cup product

Steenrod's positive-degree cup-one operation is constructed over every
commutative ring. Its full differential identity is proved by partitioning
the alternating face sums, cancelling adjacent seams, and identifying the
two surviving endpoints with the two Alexander–Whitney cup orders.

Descent to upstream singular cohomology gives `cup_comm_graded` with sign
`(-1)^(p*q)` and both target-degree equalities explicit. Degree zero is handled
by an endpoint argument. Rational odd-degree squares vanish. The separate
bidegree `(1,1)` proof records an independent check of the minus sign.

HC no distance; AV milestone no distance. This supplies S6, O1's last missing
field; it retires nothing alone.
-/

noncomputable section
open CategoryTheory Limits AlgebraicTopology.Simplicial
open scoped Simplicial
open Finset
namespace HodgeLean.Foundations.Singular
attribute [local implicit_reducible] ShortComplex.moduleCatMk ShortComplex.moduleCatLeftHomologyData
variable {R : Type} [CommRing R] (Y : TopCat.{0})

private theorem extCochain {X : SSet.{0}} {n : ℕ} (φ ψ : Cochain R X n)
    (h : ∀ σ : X _⦋n⦌, φ (chainOfSimplex R σ) = ψ (chainOfSimplex R σ)) : φ = ψ := by
  have hc : ModuleCat.ofHom φ = ModuleCat.ofHom ψ := by
    apply SSet.chainComplex_hom_ext
    intro σ
    refine ModuleCat.hom_ext (LinearMap.ext fun a => ?_)
    have hi : (X.ιChainComplex (R := ModuleCat.of R R) σ).hom a =
        a • chainOfSimplex R σ := by
      rw [chainOfSimplex, ← map_smul]
      simp
    change φ ((X.ιChainComplex (R := ModuleCat.of R R) σ).hom a) =
      ψ ((X.ιChainComplex (R := ModuleCat.of R R) σ).hom a)
    rw [hi, map_smul, map_smul, h]
  exact congrArg ModuleCat.Hom.hom hc

private theorem sign_period (a b : ℕ) :
    (-1 : R) ^ (a + 2 * b) = (-1 : R) ^ a := by
  rw [pow_add, pow_mul]
  simp

private theorem cupClass (p q : ℕ)
    (φ : Cocycle R (TopCat.toSSet.obj Y) p)
    (ψ : Cocycle R (TopCat.toSSet.obj Y) q)
    (χ : Cocycle R (TopCat.toSSet.obj Y) (p + q))
    (hχ : χ.1 = cupCochain Y p q φ.1 ψ.1) :
    cup Y rfl (cohomologyClass Y p φ) (cohomologyClass Y q ψ) =
      cohomologyClass Y (p + q) χ := by
  dsimp only [cup, cohomologyClass]
  simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  have hc : coboundary R (p + q) (cupCochain Y p q φ.1 ψ.1) = 0 := by
    rw [coboundary_cupCochain, show coboundary R p φ.1 = 0 from φ.2,
      show coboundary R q ψ.1 = 0 from ψ.2]
    simp
  change cohomologyClass Y (p + q) ⟨cupCochain Y p q φ.1 ψ.1, hc⟩ =
    cohomologyClass Y (p + q) χ
  exact congrArg (cohomologyClass Y (p + q)) (Subtype.ext hχ.symm)

private theorem boundaryClass (n : ℕ) (φ : Cochain R (TopCat.toSSet.obj Y) n) :
    cohomologyClass Y (n + 1) ⟨coboundary R n φ, coboundary_coboundary R n φ⟩ = 0 := by
  let K := (TopCat.toSSet.obj Y).chainComplex (ModuleCat.of R R)
  let T := (K.sc (n + 1)).linearDual
  let hn : (ComplexShape.down ℕ).next (n + 1) = n := ChainComplex.next_nat_succ n
  let η : T.X₁ := φ.comp (K.XIsoOfEq hn).hom.hom
  have hη : (η : Module.Dual R (K.X ((ComplexShape.down ℕ).next (n + 1)))).comp
      (K.XIsoOfEq hn).inv.hom = φ := by
    ext c
    exact congrArg φ (ConcreteCategory.congr_hom (K.XIsoOfEq hn).inv_hom_id c)
  have he := cohomologyCycleToCocycle_moduleCatToCycles_succ R n η
  dsimp only at he
  rw [hη] at he
  unfold cohomologyClass
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  apply (map_eq_zero_iff _ (LinearEquiv.injective _)).mpr
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  refine ⟨η, ?_⟩
  apply Subtype.ext
  exact congrArg (fun x : Cocycle R (TopCat.toSSet.obj Y) (n + 1) => x.1) he

/-- Degree-one singular cohomology classes anticommute over any commutative ring.
Source: Hatcher, *Algebraic Topology*, Theorem 3.11, bidegree `(1,1)`.
-/
theorem cup_comm_one_one (a b : AlgebraicTopology.Singular.Cohomology R Y 1) :
    cup Y rfl b a = -cup Y rfl a b := by
  obtain ⟨φ, rfl⟩ := cohomologyClass_surjective Y 1 a
  obtain ⟨ψ, rfl⟩ := cohomologyClass_surjective Y 1 b
  let φψ : Cocycle R (TopCat.toSSet.obj Y) 2 := ⟨cupCochain Y 1 1 φ.1 ψ.1, by
    change coboundary R 2 _ = 0
    rw [coboundary_cupCochain Y 1 1, show coboundary R 1 φ.1 = 0 from φ.2,
      show coboundary R 1 ψ.1 = 0 from ψ.2]
    simp⟩
  let ψφ : Cocycle R (TopCat.toSSet.obj Y) 2 := ⟨cupCochain Y 1 1 ψ.1 φ.1, by
    change coboundary R 2 _ = 0
    rw [coboundary_cupCochain Y 1 1, show coboundary R 1 φ.1 = 0 from φ.2,
      show coboundary R 1 ψ.1 = 0 from ψ.2]
    simp⟩
  rw [cupClass Y 1 1 ψ φ ψφ rfl, cupClass Y 1 1 φ ψ φψ rfl]
  have hh : -(φψ + ψφ) =
      (⟨coboundary R 1 (cupOneCochain Y 0 0 φ.1 ψ.1),
        coboundary_coboundary R 1 _⟩ : Cocycle R (TopCat.toSSet.obj Y) 2) :=
    Subtype.ext (coboundary_cupOneCochain_one_one_of_closed Y φ.1 ψ.1 φ.2 ψ.2).symm
  have hc := boundaryClass Y 1 (cupOneCochain Y 0 0 φ.1 ψ.1)
  rw [← hh, map_neg, map_add, neg_eq_zero] at hc
  exact eq_neg_of_add_eq_zero_right hc

private def longEdge (n : ℕ) : SimplexCategory.mk 1 ⟶ SimplexCategory.mk n :=
  SimplexCategory.mkHom
    { toFun := fun i => ⟨i.val * n, by have := i.isLt; interval_cases i.val <;> omega⟩
      monotone' := fun _ _ h => Nat.mul_le_mul_right n h }

/-- A closed zero-cochain commutes with every cochain, with the target degree transported.
Source: Hatcher, *Algebraic Topology*, §3.2, cup formula and Theorem 3.11 in degree zero.
-/
theorem cupCochain_comm_zero (q : ℕ) (φ : Cochain R (TopCat.toSSet.obj Y) 0)
    (ψ : Cochain R (TopCat.toSSet.obj Y) q) (hφ : coboundary R 0 φ = 0) :
    cupCochain Y q 0 ψ φ =
      (cupCochain Y 0 q φ ψ).comp
        (((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of R R)).XIsoOfEq
          (Nat.zero_add q).symm).hom.hom := by
  apply extCochain
  intro σ
  let X := TopCat.toSSet.obj Y
  let e : SimplexCategory.mk (0 + q) ⟶ SimplexCategory.mk q :=
    eqToHom (congrArg SimplexCategory.mk (Nat.zero_add q))
  have hf : frontInclusion q 0 = 𝟙 _ := by ext i; rfl
  have hb : backInclusion 0 q ≫ e = 𝟙 _ := by
    ext i
    simp [backInclusion, e, SimplexCategory.eqToHom_toOrderHom]
  have he0 : SimplexCategory.δ (0 : Fin 2) ≫ longEdge q = backInclusion q 0 := by
    ext i
    fin_cases i
    simp [longEdge, backInclusion, SimplexCategory.δ]
    change 1 * q = q
    omega
  have he1 : SimplexCategory.δ (1 : Fin 2) ≫ longEdge q = frontInclusion 0 q ≫ e := by
    ext i
    fin_cases i
    simp [longEdge, frontInclusion, SimplexCategory.δ, e,
      SimplexCategory.eqToHom_toOrderHom]
    apply Fin.ext
    change 0 * q = 0
    omega
  have hz := LinearMap.congr_fun hφ (chainOfSimplex R (X.map (longEdge q).op σ))
  simp only [coboundary_chainOfSimplex, Fin.sum_univ_succ] at hz
  simp only [Fin.val_zero, Fin.val_succ, pow_zero, one_smul,
    Fin.sum_univ_zero, add_zero, LinearMap.zero_apply] at hz
  simp only [Nat.zero_add, pow_one, neg_one_smul, Fin.succ_zero_eq_one] at hz
  have hv : φ (chainOfSimplex R (X.map (backInclusion q 0).op σ)) =
      φ (chainOfSimplex R (X.map (frontInclusion 0 q ≫ e).op σ)) := by
    change φ (chainOfSimplex R (X.map (SimplexCategory.δ (0 : Fin 2)).op
      (X.map (longEdge q).op σ))) +
      -φ (chainOfSimplex R (X.map (SimplexCategory.δ (1 : Fin 2)).op
        (X.map (longEdge q).op σ))) = 0 at hz
    simp only [← Functor.map_comp_apply, ← op_comp, he0, he1] at hz
    exact sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using hz)
  simp only [LinearMap.comp_apply, XIsoOfEq_chainOfSimplex, cupCochain_apply_simplex,
    frontFace, backFace, hf]
  change ψ (chainOfSimplex R (X.map (𝟙 _).op σ)) *
    φ (chainOfSimplex R (X.map (backInclusion q 0).op σ)) =
      φ (chainOfSimplex R (X.map (frontInclusion 0 q).op (X.map e.op σ))) *
      ψ (chainOfSimplex R (X.map (backInclusion 0 q).op (X.map e.op σ)))
  simp only [← Functor.map_comp_apply, ← op_comp, hb, hv]
  exact mul_comm _ _

private theorem cupClass_cast {p q k : ℕ} (h : p + q = k)
    (φ : Cocycle R (TopCat.toSSet.obj Y) p)
    (ψ : Cocycle R (TopCat.toSSet.obj Y) q)
    (χ : Cocycle R (TopCat.toSSet.obj Y) k)
    (hχ : χ.1 = (cupCochain Y p q φ.1 ψ.1).comp
      (((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of R R)).XIsoOfEq h.symm).hom.hom) :
    cup Y h (cohomologyClass Y p φ) (cohomologyClass Y q ψ) =
      cohomologyClass Y k χ := by
  subst k
  exact cupClass Y p q φ ψ χ (by simpa using hχ)

/-- Degree-zero singular cohomology classes commute with classes in every degree.
Source: Hatcher, *Algebraic Topology*, Theorem 3.11, bidegree `(0,q)`.
-/
theorem cup_comm_zero (q : ℕ)
    (a : AlgebraicTopology.Singular.Cohomology R Y 0)
    (b : AlgebraicTopology.Singular.Cohomology R Y q) :
    cup Y (Nat.add_zero q) b a = cup Y (Nat.zero_add q) a b := by
  obtain ⟨φ, rfl⟩ := cohomologyClass_surjective Y 0 a
  obtain ⟨ψ, rfl⟩ := cohomologyClass_surjective Y q b
  let χ : Cocycle R (TopCat.toSSet.obj Y) q := ⟨cupCochain Y q 0 ψ.1 φ.1, by
    change coboundary R q _ = 0
    have hc := coboundary_cupCochain Y q 0 ψ.1 φ.1
    rw [show coboundary R q ψ.1 = 0 from ψ.2,
      show coboundary R 0 φ.1 = 0 from φ.2] at hc
    simpa using hc⟩
  exact (cupClass Y q 0 ψ φ χ rfl).trans
    (cupClass_cast Y (Nat.zero_add q) φ ψ χ
      (cupCochain_comm_zero Y q φ.1 ψ.1 φ.2)).symm

/-- A rational degree-one singular cohomology class has square zero.
Source: Hatcher, *Algebraic Topology*, Theorem 3.11 and its odd-degree square consequence,
specialized here to degree one.
-/
theorem cup_self_one_eq_zero (a : AlgebraicTopology.Singular.Cohomology ℚ Y 1) :
    cup Y rfl a a = 0 := by
  have hh := cup_comm_one_one Y a a
  have hz : (2 : ℚ) • cup Y rfl a a = 0 := by
    rw [two_smul]
    exact eq_neg_iff_add_eq_zero.mp hh
  exact (smul_eq_zero.mp hz).resolve_left (by norm_num)

/-- The degree-`(1,1)` graded sign in the degree-equality interface of a cup product.
Source: Hatcher, *Algebraic Topology*, Theorem 3.11, bidegree `(1,1)`.
-/
theorem cup_comm_graded_one_one {k : ℕ} (h : 1 + 1 = k) (h' : 1 + 1 = k)
    (a b : AlgebraicTopology.Singular.Cohomology R Y 1) :
    cup Y h' b a = ((-1 : R) ^ (1 * 1)) • cup Y h a b := by
  subst k
  simpa using cup_comm_one_one Y a b

/-- The degree-zero graded sign, with both target-degree equalities explicit.
Source: Hatcher, *Algebraic Topology*, Theorem 3.11, bidegree `(0,q)`.
-/
theorem cup_comm_graded_zero {q k : ℕ} (h : 0 + q = k) (h' : q + 0 = k)
    (a : AlgebraicTopology.Singular.Cohomology R Y 0)
    (b : AlgebraicTopology.Singular.Cohomology R Y q) :
    cup Y h' b a = ((-1 : R) ^ (0 * q)) • cup Y h a b := by
  cases h'
  simpa using cup_comm_zero Y q a b

example (φ ψ : Cochain R (TopCat.toSSet.obj Y) 1)
    (hφ : coboundary R 1 φ = 0) (hψ : coboundary R 1 ψ = 0) :
    coboundary R 1 (cupOneCochain Y 0 0 φ ψ) =
      -(cupCochain Y 1 1 φ ψ + cupCochain Y 1 1 ψ φ) :=
  coboundary_cupOneCochain_one_one_of_closed Y φ ψ hφ hψ

example (a b : AlgebraicTopology.Singular.Cohomology R Y 1) :
    cup Y rfl b a = ((-1 : R) ^ (1 * 1)) • cup Y rfl a b :=
  cup_comm_graded_one_one Y rfl rfl a b

example (a : AlgebraicTopology.Singular.Cohomology ℚ Y 1) : cup Y rfl a a = 0 :=
  cup_self_one_eq_zero Y a

example (q : ℕ) (a : AlgebraicTopology.Singular.Cohomology R Y 0)
    (b : AlgebraicTopology.Singular.Cohomology R Y q) :
    cup Y (Nat.add_zero q) b a = cup Y (Nat.zero_add q) a b :=
  cup_comm_zero Y q a b


private theorem cupOne_zero_left (p q : ℕ)
    (ψ : Cochain R (TopCat.toSSet.obj Y) (q + 1)) :
    cupOneCochain Y p q (0 : Cochain R (TopCat.toSSet.obj Y) (p + 1)) ψ = 0 := by
  apply extCochain
  intro σ
  simp [cupOneCochain_apply_simplex]

private theorem cupOne_zero_right (p q : ℕ)
    (φ : Cochain R (TopCat.toSSet.obj Y) (p + 1)) :
    cupOneCochain Y p q φ (0 : Cochain R (TopCat.toSSet.obj Y) (q + 1)) = 0 := by
  apply extCochain
  intro σ
  simp [cupOneCochain_apply_simplex]

private def transportedCycle {m n : ℕ} (h : m = n)
    (φ : Cocycle R (TopCat.toSSet.obj Y) m) :
    Cocycle R (TopCat.toSSet.obj Y) n := h ▸ φ

private theorem transportedCycle_val {m n : ℕ} (h : m = n)
    (φ : Cocycle R (TopCat.toSSet.obj Y) m) :
    (transportedCycle Y h φ).1 = φ.1.comp
      (((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of R R)).XIsoOfEq h.symm).hom.hom := by
  subst n
  simp [transportedCycle]

private def productCycle (p q : ℕ)
    (φ : Cocycle R (TopCat.toSSet.obj Y) p)
    (ψ : Cocycle R (TopCat.toSSet.obj Y) q) :
    Cocycle R (TopCat.toSSet.obj Y) (p + q) :=
  ⟨cupCochain Y p q φ.1 ψ.1, by
    change coboundary R (p + q) _ = 0
    rw [coboundary_cupCochain Y p q,
      show coboundary R p φ.1 = 0 from φ.2,
      show coboundary R q ψ.1 = 0 from ψ.2]
    simp⟩

private theorem sign_square (n : ℕ) : ((-1 : R) ^ n) * ((-1 : R) ^ n) = 1 := by
  rw [← pow_add, show n + n = 2 * n by omega, pow_mul]
  simp

private theorem sign_product (p q : ℕ) :
    (-1 : R) ^ ((p + 1) * (q + 1) + (p + 1) + (q + 1)) *
      (-1 : R) ^ (p + q + 1) = -(-1 : R) ^ ((p + 1) * (q + 1)) := by
  rw [← pow_add,
    show ((p + 1) * (q + 1) + (p + 1) + (q + 1)) + (p + q + 1) =
      (((p + 1) * (q + 1)) + 1) + 2 * (p + q + 1) by omega,
    sign_period, pow_succ, mul_neg_one]

private theorem cup_comm_positive (p q : ℕ)
    (a : AlgebraicTopology.Singular.Cohomology R Y (p + 1))
    (b : AlgebraicTopology.Singular.Cohomology R Y (q + 1)) :
    cup Y (by omega : q + 1 + (p + 1) = p + q + 2) b a =
      ((-1 : R) ^ ((p + 1) * (q + 1))) •
        cup Y (by omega : p + 1 + (q + 1) = p + q + 2) a b := by
  obtain ⟨φ, rfl⟩ := cohomologyClass_surjective Y (p + 1) a
  obtain ⟨ψ, rfl⟩ := cohomologyClass_surjective Y (q + 1) b
  let A := transportedCycle Y (by omega : p + 1 + (q + 1) = p + q + 2)
    (productCycle Y (p + 1) (q + 1) φ ψ)
  let B := transportedCycle Y (by omega : q + 1 + (p + 1) = p + q + 2)
    (productCycle Y (q + 1) (p + 1) ψ φ)
  have hA : A.1 = (cupCochain Y (p + 1) (q + 1) φ.1 ψ.1).comp
      (reassocChain R p (q + 1)) := transportedCycle_val Y _ _
  have hB : B.1 = (cupCochain Y (q + 1) (p + 1) ψ.1 φ.1).comp
      (((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of R R)).XIsoOfEq
        (by omega : p + q + 2 = q + 1 + (p + 1))).hom.hom :=
    transportedCycle_val Y _ _
  rw [cupClass_cast Y _ ψ φ B hB, cupClass_cast Y _ φ ψ A hA]
  have hd := coboundary_cupOneCochain Y p q φ.1 ψ.1
  rw [show coboundary R (p + 1) φ.1 = 0 from φ.2,
    show coboundary R (q + 1) ψ.1 = 0 from ψ.2,
    cupOne_zero_left, cupOne_zero_right] at hd
  simp only [LinearMap.zero_comp, smul_zero, add_zero] at hd
  have hh : (-1 : R) ^ (p + q + 1) • A +
      (-1 : R) ^ ((p + 1) * (q + 1) + (p + 1) + (q + 1)) • B =
      (⟨coboundary R (p + q + 1) (cupOneCochain Y p q φ.1 ψ.1),
        coboundary_coboundary R (p + q + 1) _⟩ :
        Cocycle R (TopCat.toSSet.obj Y) (p + q + 2)) := by
    apply Subtype.ext
    change (-1 : R) ^ (p + q + 1) • A.1 +
      (-1 : R) ^ ((p + 1) * (q + 1) + (p + 1) + (q + 1)) • B.1 = _
    rw [hA, hB]
    exact hd.symm
  have hc := boundaryClass Y (p + q + 1) (cupOneCochain Y p q φ.1 ψ.1)
  rw [← hh, map_add, map_smul, map_smul] at hc
  have hs := congrArg (fun x =>
    (-1 : R) ^ ((p + 1) * (q + 1) + (p + 1) + (q + 1)) • x) hc
  simp only [smul_add, smul_smul, smul_zero, sign_square, sign_product,
    one_smul, neg_smul] at hs
  exact (neg_add_eq_zero.mp hs).symm

/-- Graded commutativity of the singular cup product over any commutative ring,
with both target-degree equalities explicit.
Source: Hatcher, *Algebraic Topology*, Theorem 3.11.
HC no distance; AV milestone no distance. This supplies S6, O1's last missing field;
it retires nothing alone.
-/
theorem cup_comm_graded {p q k : ℕ} (h : p + q = k) (h' : q + p = k)
    (a : AlgebraicTopology.Singular.Cohomology R Y p)
    (b : AlgebraicTopology.Singular.Cohomology R Y q) :
    cup Y h' b a = ((-1 : R) ^ (p * q)) • cup Y h a b := by
  cases p with
  | zero => exact cup_comm_graded_zero Y h h' a b
  | succ p =>
    cases q with
    | zero =>
      have hz := cup_comm_graded_zero Y h' h b a
      simpa using hz.symm
    | succ q =>
      have hk : k = p + q + 2 := by omega
      revert h h'
      rw [hk]
      intro h h'
      exact cup_comm_positive Y p q a b

example {p q k : ℕ} (h : p + q = k) (h' : q + p = k)
    (a : AlgebraicTopology.Singular.Cohomology R Y p)
    (b : AlgebraicTopology.Singular.Cohomology R Y q) :
    cup Y h' b a = ((-1 : R) ^ (p * q)) • cup Y h a b :=
  cup_comm_graded Y h h' a b

/-- The square of every odd-degree rational singular cohomology class vanishes.
Source: Hatcher, *Algebraic Topology*, Theorem 3.11, odd-degree square consequence.
-/
theorem cup_self_eq_zero_of_odd {p : ℕ} (hp : Odd p)
    (a : AlgebraicTopology.Singular.Cohomology ℚ Y p) : cup Y rfl a a = 0 := by
  have hh := cup_comm_graded Y rfl rfl a a
  rw [(hp.mul hp).neg_one_pow] at hh
  have hz : (2 : ℚ) • cup Y rfl a a = 0 := by
    rw [two_smul]
    simpa using eq_neg_iff_add_eq_zero.mp (by simpa using hh)
  exact (smul_eq_zero.mp hz).resolve_left (by norm_num)

example (a : AlgebraicTopology.Singular.Cohomology ℚ Y 3) : cup Y rfl a a = 0 :=
  cup_self_eq_zero_of_odd Y (by decide) a

#print axioms cup_comm_graded
#print axioms cup_self_eq_zero_of_odd
#print axioms cup_comm_one_one
#print axioms cupCochain_comm_zero
#print axioms cup_comm_zero
#print axioms cup_self_one_eq_zero
#print axioms cup_comm_graded_one_one
#print axioms cup_comm_graded_zero

end HodgeLean.Foundations.Singular
