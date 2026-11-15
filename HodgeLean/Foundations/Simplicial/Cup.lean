import HodgeLean.Foundations.Port.AlgebraicTopology.Singular.Cap.Simplicial

/-!
# The simplicial Alexander–Whitney cochain product

The front/back formula, Leibniz rule, associativity, unit laws and naturality hold
for every simplicial set. Singular cochains and cover-small singular cochains are
specializations. This supports C7 on the torus track and retires nothing yet.
HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory Limits
open AlgebraicTopology.Simplicial
open scoped Simplicial

namespace HodgeLean.Foundations.Simplicial

attribute [local implicit_reducible] ShortComplex.moduleCatMk ShortComplex.moduleCatLeftHomologyData

variable {R : Type} [CommRing R] (Y : SSet.{0})

private theorem cochain_ext {X : SSet.{0}} {n : ℕ} (φ ψ : Cochain R X n)
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

/-- The Alexander–Whitney product of simplicial cochains, evaluated on front and back faces.
Source: Hatcher, *Algebraic Topology*, §3.2, definition of the cup product.
-/
def cupCochain (p q : ℕ) :
    Cochain R Y p →ₗ[R]
      Cochain R Y q →ₗ[R]
        Cochain R Y (p + q) where
  toFun φ := (cap R p q φ).dualMap
  map_add' φ ψ := by
    ext η c
    change η (capLinear R p q (φ + ψ) c) =
      η (capLinear R p q φ c) + η (capLinear R p q ψ c)
    simp only [map_add, LinearMap.add_apply]
  map_smul' a φ := by
    ext η c
    change η (capLinear R p q (a • φ) c) = a • η (capLinear R p q φ c)
    simp

/-- Evaluation on a simplex is the product of the evaluations on its two faces.
Source: Hatcher, *Algebraic Topology*, §3.2, definition of the cup product.
-/
theorem cupCochain_apply_simplex (p q : ℕ)
    (φ : Cochain R Y p)
    (ψ : Cochain R Y q)
    (σ : Y _⦋p + q⦌) :
    cupCochain Y p q φ ψ (chainOfSimplex R σ) =
      φ (chainOfSimplex R (frontFace Y σ)) *
        ψ (chainOfSimplex R (backFace Y σ)) := by
  change ψ (cap R p q φ (chainOfSimplex R σ)) = _
  rw [cap_chainOfSimplex, map_smul, smul_eq_mul]

example (φ ψ : Cochain R Y 0)
    (σ : Y _⦋0 + 0⦌) :
    cupCochain Y 0 0 φ ψ (chainOfSimplex R σ) =
      φ (chainOfSimplex R (frontFace Y σ)) *
        ψ (chainOfSimplex R (backFace Y σ)) :=
  cupCochain_apply_simplex Y 0 0 φ ψ σ

/-- The Leibniz rule, with the canonical reassociation of the first summand's degree.
Source: Hatcher, *Algebraic Topology*, §3.2, Lemma 3.6.
-/
theorem coboundary_cupCochain (p q : ℕ)
    (φ : Cochain R Y p)
    (ψ : Cochain R Y q) :
    coboundary R (p + q) (cupCochain Y p q φ ψ) =
      (cupCochain Y (p + 1) q (coboundary R p φ) ψ).comp (reassocChain R p q) +
        (-1 : R) ^ p • cupCochain Y p (q + 1) φ (coboundary R q ψ) := by
  ext c
  have h := congrArg ψ (LinearMap.congr_fun (cap_coboundary_eq R p q φ) c)
  change ψ (cap R (p + 1) q (coboundary R p φ) (reassocChain R p q c)) =
    ψ (cap R p q φ (boundary R (p + q) c) -
      (-1 : R) ^ p • boundary R q (cap R p (q + 1) φ c)) at h
  rw [map_sub, map_smul] at h
  exact (eq_sub_iff_add_eq.mp h).symm

/-- Pullback along a map of simplicial sets preserves the cochain cup product.
Source: Hatcher, *Algebraic Topology*, §3.2, naturality of the cup product.
-/
theorem cupCochain_naturality {Z : SSet.{0}} (f : Z ⟶ Y) (p q : ℕ)
    (φ : Cochain R Y p)
    (ψ : Cochain R Y q) :
    cochainMap R f (p + q) (cupCochain Y p q φ ψ) =
      cupCochain Z p q (cochainMap R f p φ)
        (cochainMap R f q ψ) := by
  ext c
  exact congrArg ψ (cap_naturality R f p q φ c).symm

/-- Associativity of the Alexander–Whitney product, with its canonical degree transport.
Source: Hatcher, *Algebraic Topology*, §3.2, associativity of the cup product.
-/
theorem cupCochain_assoc (p q r : ℕ)
    (φ : Cochain R Y p)
    (ψ : Cochain R Y q)
    (χ : Cochain R Y r) :
    cupCochain Y (p + q) r (cupCochain Y p q φ ψ) χ =
      (cupCochain Y p (q + r) φ (cupCochain Y q r ψ χ)).comp
        ((Y.chainComplex (ModuleCat.of R R)).XIsoOfEq
          (Nat.add_assoc p q r)).hom.hom := by
  apply cochain_ext
  intro σ
  let X := Y
  let e : SimplexCategory.mk (p + (q + r)) ⟶ SimplexCategory.mk (p + q + r) :=
    eqToHom (congrArg SimplexCategory.mk (Nat.add_assoc p q r).symm)
  have hf : frontInclusion p q ≫ frontInclusion (p + q) r =
      frontInclusion p (q + r) ≫ e := by
    ext i
    simp [frontInclusion, e, SimplexCategory.eqToHom_toOrderHom]
    rfl
  have hm : backInclusion p q ≫ frontInclusion (p + q) r =
      frontInclusion q r ≫ backInclusion p (q + r) ≫ e := by
    ext i
    simp [frontInclusion, backInclusion, e, SimplexCategory.eqToHom_toOrderHom]
    rfl
  have hb : backInclusion (p + q) r =
      backInclusion q r ≫ backInclusion p (q + r) ≫ e := by
    ext i
    simp [backInclusion, e, SimplexCategory.eqToHom_toOrderHom, Nat.add_assoc]
    rfl
  have hfront : frontFace (p := p) (q := q) X (frontFace (p := p + q) (q := r) X σ) =
      frontFace (p := p) (q := q + r) X (X.map e.op σ) := by
    simp only [frontFace, ← Functor.map_comp_apply, ← op_comp, hf]
  have hmiddle : backFace (p := p) (q := q) X (frontFace (p := p + q) (q := r) X σ) =
      frontFace (p := q) (q := r) X (backFace (p := p) (q := q + r) X (X.map e.op σ)) := by
    simp only [frontFace, backFace, ← Functor.map_comp_apply, ← op_comp, hm]
  have hback : backFace (p := p + q) (q := r) X σ =
      backFace (p := q) (q := r) X (backFace (p := p) (q := q + r) X (X.map e.op σ)) := by
    simp only [backFace, ← Functor.map_comp_apply, ← op_comp, hb]
  simp only [LinearMap.comp_apply, XIsoOfEq_chainOfSimplex, cupCochain_apply_simplex]
  rw [hfront, hmiddle, hback, mul_assoc]

/-- The constant simplicial zero-cochain with value one on every vertex.
Source: Hatcher, *Algebraic Topology*, §3.2, unit for the cup product.
-/
def unitCochain : Cochain R Y 0 :=
  (Y.isColimitChainComplexXCofan (ModuleCat.of R R) 0).desc
    (Cofan.mk _ fun _ ↦ 𝟙 (ModuleCat.of R R)) |>.hom

/-- The unit cochain evaluates to one on each vertex.
Source: Hatcher, *Algebraic Topology*, §3.2, unit for the cup product.
-/
@[simp] theorem unitCochain_apply_simplex (σ : Y _⦋0⦌) :
    unitCochain (R := R) Y (chainOfSimplex R σ) = 1 := by
  have h := Y.isColimitChainComplexXCofan
    (ModuleCat.of R R) 0 |>.fac (Cofan.mk _ fun _ ↦ 𝟙 (ModuleCat.of R R)) ⟨σ⟩
  exact ConcreteCategory.congr_hom h (1 : R)

example (σ : Y _⦋0⦌) :
    unitCochain (R := R) Y (chainOfSimplex R σ) = 1 :=
  unitCochain_apply_simplex Y σ

/-- The constant unit cochain is closed.
Source: Hatcher, *Algebraic Topology*, §3.2, unit for the cup product.
-/
@[simp] theorem coboundary_unitCochain :
    coboundary R 0 (unitCochain (R := R) Y) = 0 := by
  apply cochain_ext
  intro σ
  simp [Fin.sum_univ_succ]

/-- The right unit law on simplicial cochains.
Source: Hatcher, *Algebraic Topology*, §3.2, unit for the cup product.
-/
theorem cupCochain_one (p : ℕ) (φ : Cochain R Y p) :
    cupCochain Y p 0 φ (unitCochain Y) = φ := by
  apply cochain_ext
  intro σ
  rw [cupCochain_apply_simplex, unitCochain_apply_simplex, mul_one]
  have h : frontInclusion p 0 = 𝟙 (SimplexCategory.mk p) := by
    ext i
    rfl
  simp [frontFace, h]

/-- The left unit law on simplicial cochains, with the degree equality explicit.
Source: Hatcher, *Algebraic Topology*, §3.2, unit for the cup product.
-/
theorem one_cupCochain (q : ℕ) (ψ : Cochain R Y q) :
    cupCochain Y 0 q (unitCochain Y) ψ =
      ψ.comp ((Y.chainComplex (ModuleCat.of R R)).XIsoOfEq
        (Nat.zero_add q)).hom.hom := by
  apply cochain_ext
  intro σ
  rw [cupCochain_apply_simplex, unitCochain_apply_simplex, one_mul]
  simp only [LinearMap.comp_apply, XIsoOfEq_chainOfSimplex]
  have h : backInclusion 0 q = eqToHom (congrArg SimplexCategory.mk (Nat.zero_add q).symm) := by
    ext i
    simp [backInclusion, SimplexCategory.eqToHom_toOrderHom]

  rw [backFace, h]


/-- Constant zero-cochains multiply their scalar values.
Source: Hatcher, *Algebraic Topology*, §3.2, definition of the cup product.
-/
theorem cupCochain_constants (a b : R) :
    cupCochain Y 0 0 (a • unitCochain (R := R) Y) (b • unitCochain (R := R) Y) =
      (a * b) • unitCochain (R := R) Y := by
  simp [map_smul, LinearMap.smul_apply, cupCochain_one, smul_smul, mul_comm]

example : cupCochain (TopCat.toSSet.obj (TopCat.of PUnit)) 0 0
    ((2 : ℚ) • unitCochain (R := ℚ) _) ((3 : ℚ) • unitCochain (R := ℚ) _) =
      (6 : ℚ) • unitCochain (R := ℚ) _ := by
  convert cupCochain_constants (TopCat.toSSet.obj (TopCat.of PUnit)) (2 : ℚ) 3 using 1
  norm_num


/-- Pullback of simplicial cochains preserves the constant unit.
Source: Hatcher, *Algebraic Topology*, §3.2, naturality and unit of the cup product.
-/
theorem cochainMap_unitCochain {Z : SSet.{0}} (f : Z ⟶ Y) :
    cochainMap R f 0 (unitCochain (R := R) Y) = unitCochain Z := by
  apply cochain_ext
  intro σ
  rw [cochainMap_apply, chainOfSimplex_map, unitCochain_apply_simplex, unitCochain_apply_simplex]

/-- Pullback of simplicial cochains commutes with the coboundary.
Source: Hatcher, *Algebraic Topology*, §3.1, induced maps on cochains.
-/
theorem coboundary_cochainMap {Z : SSet.{0}} (f : Z ⟶ Y) (n : ℕ) (φ : Cochain R Y n) :
    coboundary R n (cochainMap R f n φ) = cochainMap R f (n + 1) (coboundary R n φ) := by
  ext c
  exact congrArg φ (ConcreteCategory.congr_hom
    ((SSet.chainComplexMap f (ModuleCat.of R R)).comm (n + 1) n) c).symm


/-! ## Axiom audit -/

#print axioms cupCochain
#print axioms cupCochain_apply_simplex
#print axioms coboundary_cupCochain
#print axioms cupCochain_naturality
#print axioms cupCochain_assoc
#print axioms unitCochain
#print axioms unitCochain_apply_simplex
#print axioms coboundary_unitCochain
#print axioms cupCochain_one
#print axioms one_cupCochain
#print axioms cupCochain_constants
#print axioms cochainMap_unitCochain
#print axioms coboundary_cochainMap

end HodgeLean.Foundations.Simplicial
