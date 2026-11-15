import HodgeLean.Adapters.NormalConeB4aGysinAnalyticParameter

/-! # Compatible evaluations on the comparison base change -/

noncomputable section
namespace HodgeLean.Adapters
open scoped TensorProduct

/-- Compatible field-valued evaluations determine the unique evaluation of
the tensor-product base change, including when either source is nonreduced. -/
theorem a3b4a_gysin_exists_tensor_evaluation
    {k D T S : Type*} [Field k] [CommRing D] [CommRing T] [CommRing S]
    [Algebra k D] [Algebra k T] [Algebra k S] [Algebra D T] [Algebra D S]
    [IsScalarTower k D T] [IsScalarTower k D S]
    (u : T →ₐ[k] k) (w : S →ₐ[k] k)
    (h : ∀ d : D, u (algebraMap D T d) = w (algebraMap D S d)) :
    ∃! g : TensorProduct D T S →ₐ[k] k,
      ∀ t : T, ∀ s : S, g (t ⊗ₜ[D] s) = u t * w s := by
  let v := u.comp (IsScalarTower.toAlgHom k D T)
  letI : Algebra D k := v.toRingHom.toAlgebra
  have : IsScalarTower k D k := IsScalarTower.of_algebraMap_eq fun a => (v.commutes a).symm
  let uD : T →ₐ[D] k := { u.toRingHom with commutes' := fun _ => rfl }
  let wD : S →ₐ[D] k := { w.toRingHom with commutes' := fun d => (h d).symm }
  let g := (Algebra.TensorProduct.lift uD wD (fun _ _ => Commute.all _ _)).restrictScalars k
  have hg : ∀ t : T, ∀ s : S, g (t ⊗ₜ[D] s) = u t * w s := by
    intro t s
    exact Algebra.TensorProduct.lift_tmul uD wD (fun _ _ => Commute.all _ _) t s
  refine ⟨g, hg, ?_⟩
  intro f hf
  apply AlgHom.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul t s => exact (hf t s).trans (hg t s).symm
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Continuous compatible families of complex evaluations lift continuously
to the tensor-product base change. -/
theorem a3b4a_gysin_exists_continuous_tensor_evaluation
    {X : Type*} [TopologicalSpace X]
    {D T S : Type} [CommRing D] [CommRing T] [CommRing S]
    [Algebra ℂ D] [Algebra ℂ T] [Algebra ℂ S] [Algebra D T] [Algebra D S]
    [IsScalarTower ℂ D T] [IsScalarTower ℂ D S]
    (u : X → (T →ₐ[ℂ] ℂ)) (w : X → (S →ₐ[ℂ] ℂ))
    (hu : Continuous u) (hw : Continuous w)
    (h : ∀ x : X, ∀ d : D, u x (algebraMap D T d) = w x (algebraMap D S d)) :
    ∃ G : X → (TensorProduct D T S →ₐ[ℂ] ℂ), Continuous G ∧
      ∀ x : X, ∀ t : T, ∀ s : S, G x (t ⊗ₜ[D] s) = u x t * w x s := by
  choose G hG using fun x => (a3b4a_gysin_exists_tensor_evaluation (u x) (w x) (h x)).exists
  refine ⟨G, ?_, hG⟩
  have heval : ∀ a : TensorProduct D T S, Continuous (fun x => G x a) := by
    intro a
    induction a using TensorProduct.induction_on with
    | zero => simpa only [map_zero] using (continuous_const : Continuous (fun _ : X => (0 : ℂ)))
    | tmul t s =>
      simp_rw [hG]
      exact ((AlgebraicGeometry.ComplexPoint.continuous_affineAlgebraHom_apply T t).comp hu).mul
        ((AlgebraicGeometry.ComplexPoint.continuous_affineAlgebraHom_apply S s).comp hw)
    | add a b ha hb =>
      simpa only [map_add] using ha.fun_add hb
  exact continuous_induced_rng.mpr (continuous_pi heval)

end HodgeLean.Adapters
