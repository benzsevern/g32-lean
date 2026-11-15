import HodgeLean.Foundations.AlgebraicGeometry.ComplexTopology.Defs
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.AffineScheme
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.Topology.Algebra.MvPolynomial

/-! Evaluation topology for a finite polynomial presentation.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open Topology AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.ComplexTopology

variable {S : Type} [CommRing S] [Algebra ℂ S] {n m : ℕ}

lemma eval_generators (f : MvPolynomial (Fin n) ℂ →ₐ[ℂ] S)
    (φ : S →ₐ[ℂ] ℂ) (q : MvPolynomial (Fin n) ℂ) :
    MvPolynomial.eval (fun i => φ (f (MvPolynomial.X i))) q = φ (f q) := by
  have h : MvPolynomial.aeval (fun i => φ (f (MvPolynomial.X i))) = φ.comp f := by
    ext i
    simp only [MvPolynomial.aeval_X, AlgHom.comp_apply]
  exact DFunLike.congr_fun h q

def presentationPointEquiv (f : MvPolynomial (Fin n) ℂ →ₐ[ℂ] S)
    (hf : Function.Surjective f) (p : Fin m → MvPolynomial (Fin n) ℂ)
    (hp : Ideal.span (Set.range p) = RingHom.ker f.toRingHom) :
    (S →ₐ[ℂ] ℂ) ≃ zeroSet p where
  toFun φ := ⟨fun i => φ (f (MvPolynomial.X i)), by
    intro j
    rw [eval_generators]
    have hj : f (p j) = 0 := by
      apply RingHom.mem_ker.mp
      change p j ∈ RingHom.ker f.toRingHom
      rw [← hp]
      exact Ideal.subset_span ⟨j, rfl⟩
    rw [hj, map_zero]⟩
  invFun z := AlgHom.liftOfSurjective f hf (MvPolynomial.aeval z.val) (by
    rw [← hp]
    apply Ideal.span_le.mpr
    rintro q ⟨j, rfl⟩
    exact z.property j)
  left_inv φ := by
    ext r
    obtain ⟨q, rfl⟩ := hf r
    rw [AlgHom.liftOfSurjective_apply]
    exact eval_generators f φ q
  right_inv z := by
    apply Subtype.ext
    funext i
    change AlgHom.liftOfSurjective f hf _ _ (f (MvPolynomial.X i)) = z.val i
    rw [AlgHom.liftOfSurjective_apply, MvPolynomial.aeval_X]

lemma continuous_presentationPointEquiv (f : MvPolynomial (Fin n) ℂ →ₐ[ℂ] S)
    (hf : Function.Surjective f) (p : Fin m → MvPolynomial (Fin n) ℂ)
    (hp : Ideal.span (Set.range p) = RingHom.ker f.toRingHom) :
    @Continuous _ _ (affineAlgebraHomTopology S) inferInstance
      (presentationPointEquiv f hf p hp) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  exact (continuous_apply (f (MvPolynomial.X i))).comp continuous_induced_dom

lemma continuous_presentationPointEquiv_symm (f : MvPolynomial (Fin n) ℂ →ₐ[ℂ] S)
    (hf : Function.Surjective f) (p : Fin m → MvPolynomial (Fin n) ℂ)
    (hp : Ideal.span (Set.range p) = RingHom.ker f.toRingHom) :
    @Continuous _ _ inferInstance (affineAlgebraHomTopology S)
      (presentationPointEquiv f hf p hp).symm := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro r
  obtain ⟨q, rfl⟩ := hf r
  change Continuous (fun z : zeroSet p => AlgHom.liftOfSurjective f hf _ _ (f q))
  simp only [AlgHom.liftOfSurjective_apply]
  exact q.continuous_eval.comp continuous_subtype_val

def presentationPointHomeomorph (f : MvPolynomial (Fin n) ℂ →ₐ[ℂ] S)
    (hf : Function.Surjective f) (p : Fin m → MvPolynomial (Fin n) ℂ)
    (hp : Ideal.span (Set.range p) = RingHom.ker f.toRingHom) :
    @Homeomorph (S →ₐ[ℂ] ℂ) (zeroSet p) (affineAlgebraHomTopology S) inferInstance where
  toEquiv := presentationPointEquiv f hf p hp
  continuous_toFun := continuous_presentationPointEquiv f hf p hp
  continuous_invFun := continuous_presentationPointEquiv_symm f hf p hp

end HodgeLean.Foundations.ComplexTopology
