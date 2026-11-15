import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

variable {A R : Type*} [CommRing A] [CommRing R] [Algebra A R]

/-- Restriction of a derivation to an ideal, followed by reduction modulo that ideal. -/
def s2v_l1b_idealDerivation (I : Ideal R) (d : Derivation A R R) : I →ₗ[R] R ⧸ I where
  toFun x := Ideal.Quotient.mk I (d x)
  map_add' x y := by simp only [Submodule.coe_add, map_add]
  map_smul' a x := by
    change Ideal.Quotient.mk I (d (a * (x : R))) = a • Ideal.Quotient.mk I (d x)
    rw [d.leibniz, map_add, smul_eq_mul, smul_eq_mul, map_mul, map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr x.2,
      zero_mul, add_zero]
    rfl

/-- Products of two ideal elements vanish under the reduced derivation. -/
theorem s2v_l1b_idealDerivation_square (I : Ideal R) (d : Derivation A R R) :
    I • (⊤ : Submodule R I) ≤ LinearMap.ker (s2v_l1b_idealDerivation I d) := by
  intro x hx
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro a ha b hb
    change s2v_l1b_idealDerivation I d (a • b) = 0
    rw [map_smul]
    rw [Algebra.smul_def]
    change Ideal.Quotient.mk I a * _ = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_mul]
  · intro x y hx hy
    exact (LinearMap.ker _).add_mem hx hy

/-- The reduced derivation factors through the conormal module. -/
def s2v_l1b_conormalDerivation (I : Ideal R) (d : Derivation A R R) :
    I.Cotangent →ₗ[R] R ⧸ I :=
  (I • (⊤ : Submodule R I)).liftQ (s2v_l1b_idealDerivation I d)
    (s2v_l1b_idealDerivation_square I d)

@[simp] theorem s2v_l1b_conormalDerivation_toCotangent
    (I : Ideal R) (d : Derivation A R R) (x : I) :
    s2v_l1b_conormalDerivation I d (I.toCotangent x) = Ideal.Quotient.mk I (d x) := rfl

/-- The conormal functional is linear over the quotient ring. -/
def s2v_l1b_conormalFunctional (I : Ideal R) (d : Derivation A R R) :
    I.Cotangent →ₗ[R ⧸ I] R ⧸ I where
  __ := (s2v_l1b_conormalDerivation I d).toAddHom
  map_smul' q x := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    change s2v_l1b_conormalDerivation I d ((algebraMap R (R ⧸ I)) a • x) =
      (algebraMap R (R ⧸ I)) a • s2v_l1b_conormalDerivation I d x
    simpa only [IsScalarTower.algebraMap_smul] using
      (s2v_l1b_conormalDerivation I d).map_smul a x

@[simp] theorem s2v_l1b_conormalFunctional_toCotangent
    (I : Ideal R) (d : Derivation A R R) (x : I) :
    s2v_l1b_conormalFunctional I d (I.toCotangent x) = Ideal.Quotient.mk I (d x) := rfl

/-- Ideal generators generate the conormal module over the quotient ring. -/
theorem s2v_l1b_conormal_span {ι : Type*} (I : Ideal R) (z : ι → R)
    (hz : I = Ideal.span (Set.range z)) (hm : ∀ j, z j ∈ I) :
    Submodule.span (R ⧸ I) (Set.range fun j => I.toCotangent ⟨z j, hm j⟩) = ⊤ := by
  apply top_unique
  intro x hx
  obtain ⟨x, rfl⟩ := I.toCotangent_surjective x
  have hx' : (x : R) ∈ Ideal.span (Set.range z) := hz ▸ x.2
  have H : ∀ (a : R), a ∈ Ideal.span (Set.range z) → ∀ ha : a ∈ I,
      I.toCotangent ⟨a, ha⟩ ∈
        Submodule.span (R ⧸ I) (Set.range fun j => I.toCotangent ⟨z j, hm j⟩) := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨j, rfl⟩ := ha
      intro h
      exact Submodule.subset_span ⟨j, rfl⟩
    | zero =>
      intro h
      exact Submodule.zero_mem _
    | add a b ha hb ia ib =>
      intro h
      have he : (⟨a + b, h⟩ : I) =
          (⟨a, hz.symm ▸ ha⟩ : I) + (⟨b, hz.symm ▸ hb⟩ : I) := Subtype.ext rfl
      rw [he, map_add]
      exact Submodule.add_mem _ (ia (hz.symm ▸ ha)) (ib (hz.symm ▸ hb))
    | smul a b hb ib =>
      intro h
      have H := Submodule.smul_mem
        (Submodule.span (R ⧸ I) (Set.range fun j => I.toCotangent ⟨z j, hm j⟩))
        ((algebraMap R (R ⧸ I)) a) (ib (hz.symm ▸ hb))
      have he : (⟨a • b, h⟩ : I) = a • (⟨b, hz.symm ▸ hb⟩ : I) := Subtype.ext rfl
      rw [he, map_smul]
      simpa only [IsScalarTower.algebraMap_smul] using H
  exact H x hx' x.2

/-- Dual derivations detect every coefficient of the conormal generators. -/
theorem s2v_l1b_conormal_independent {ι : Type*} [Fintype ι] [DecidableEq ι]
    (I : Ideal R) (z : ι → R) (hm : ∀ j, z j ∈ I)
    (d : ι → Derivation A R R) (hd : ∀ j k, d j (z k) = if j = k then 1 else 0) :
    LinearIndependent (R ⧸ I) (fun j => I.toCotangent ⟨z j, hm j⟩) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have H := congrArg (s2v_l1b_conormalFunctional I (d j)) hc
  simpa [hd] using H

/-- Ideal generators with dual derivations give a basis with the specified vectors. -/
theorem s2v_l1b_conormal_basis_of_derivations {ι : Type*} [Fintype ι] [DecidableEq ι]
    (I : Ideal R) (z : ι → R) (hz : I = Ideal.span (Set.range z))
    (hm : ∀ j, z j ∈ I) (d : ι → Derivation A R R)
    (hd : ∀ j k, d j (z k) = if j = k then 1 else 0) :
    ∃ b : Module.Basis ι (R ⧸ I) I.Cotangent,
      ∀ j, b j = I.toCotangent ⟨z j, hm j⟩ := by
  refine ⟨Module.Basis.mk (s2v_l1b_conormal_independent I z hm d hd)
    (s2v_l1b_conormal_span I z hz hm).ge, ?_⟩
  intro j
  exact Module.Basis.mk_apply _ _ j

end HodgeLean.Foundations.Program
