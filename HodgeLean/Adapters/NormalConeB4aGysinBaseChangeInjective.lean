import HodgeLean.Adapters.NormalConeB4aGysinBaseChangeLift

/-! # Uniqueness of nearby comparison points over their source -/

noncomputable section
namespace HodgeLean.Adapters
open AlgebraicGeometry ComplexAlgHom
open scoped TensorProduct

/-- The two factor evaluations determine a field-valued tensor evaluation. -/
theorem a3b4a_gysin_tensor_evaluation_ext
    {k D T S : Type*} [Field k] [CommRing D] [CommRing T] [CommRing S]
    [Algebra k D] [Algebra k T] [Algebra k S] [Algebra D T] [Algebra D S]
    [IsScalarTower k D T] [IsScalarTower k D S]
    (g h : TensorProduct D T S →ₐ[k] k)
    (hT : ∀ t : T, g (t ⊗ₜ[D] 1) = h (t ⊗ₜ[D] 1))
    (hS : ∀ s : S, g (1 ⊗ₜ[D] s) = h (1 ⊗ₜ[D] s)) : g = h := by
  apply AlgHom.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul t s =>
    have ht : t ⊗ₜ[D] s = (t ⊗ₜ[D] (1 : S)) * ((1 : T) ⊗ₜ[D] s) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [ht, map_mul, map_mul, hT, hS]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- On a fixed étale parameter chart, a comparison point is uniquely
determined by its projection to the original source. -/
theorem a3b4a_gysin_baseChange_projection_injective
    {n : ℕ} (T S : Type) [CommRing T] [CommRing S] [Algebra ℂ T] [Algebra ℂ S]
    [Algebra (complexPolynomialRing n) T] [Algebra (complexPolynomialRing n) S]
    [IsScalarTower ℂ (complexPolynomialRing n) T] [IsScalarTower ℂ (complexPolynomialRing n) S]
    [Algebra.Etale (complexPolynomialRing n) T] (u : T →ₐ[ℂ] ℂ)
    (g h : TensorProduct (complexPolynomialRing n) T S →ₐ[ℂ] ℂ)
    (hg : g.comp ((Algebra.TensorProduct.includeLeft :
      T →ₐ[complexPolynomialRing n] TensorProduct (complexPolynomialRing n) T S).restrictScalars ℂ)
        ∈ (etaleAlgHomProjectionChart (n := n) T u).source)
    (hh : h.comp ((Algebra.TensorProduct.includeLeft :
      T →ₐ[complexPolynomialRing n] TensorProduct (complexPolynomialRing n) T S).restrictScalars ℂ)
        ∈ (etaleAlgHomProjectionChart (n := n) T u).source)
    (hS : ∀ s : S, g (1 ⊗ₜ[complexPolynomialRing n] s) = h (1 ⊗ₜ[complexPolynomialRing n] s)) :
    g = h := by
  let L := (Algebra.TensorProduct.includeLeft :
    T →ₐ[complexPolynomialRing n] TensorProduct (complexPolynomialRing n) T S).restrictScalars ℂ
  have hbase (v : TensorProduct (complexPolynomialRing n) T S →ₐ[ℂ] ℂ)
      (d : complexPolynomialRing n) :
      (v.comp L) (algebraMap (complexPolynomialRing n) T d) =
        v (1 ⊗ₜ[complexPolynomialRing n] (algebraMap (complexPolynomialRing n) S d)) := by
    change v ((Algebra.TensorProduct.includeLeft :
      T →ₐ[complexPolynomialRing n] TensorProduct (complexPolynomialRing n) T S)
        (algebraMap (complexPolynomialRing n) T d)) =
      v ((Algebra.TensorProduct.includeRight :
        S →ₐ[complexPolynomialRing n] TensorProduct (complexPolynomialRing n) T S)
          (algebraMap (complexPolynomialRing n) S d))
    rw [AlgHom.commutes, AlgHom.commutes]
  have hL : g.comp L = h.comp L := by
    apply (etaleAlgHomProjectionChart (n := n) T u).injOn hg hh
    rw [etaleAlgHomProjectionChart_apply_of_mem T u (g.comp L) hg,
      etaleAlgHomProjectionChart_apply_of_mem T u (h.comp L) hh]
    congr 1
    apply AlgHom.ext
    intro d
    exact (hbase g d).trans ((hS _).trans (hbase h d).symm)
  apply a3b4a_gysin_tensor_evaluation_ext g h
  · intro t
    exact congrArg (fun f : T →ₐ[ℂ] ℂ => f t) hL
  · exact hS

/-- Every source point over the target of the chosen étale chart has exactly
one comparison point whose base restriction lies in that chart. -/
theorem a3b4a_gysin_exists_unique_chart_comparison_point
    {n : ℕ} (T S : Type) [CommRing T] [CommRing S] [Algebra ℂ T] [Algebra ℂ S]
    [Algebra (complexPolynomialRing n) T] [Algebra (complexPolynomialRing n) S]
    [IsScalarTower ℂ (complexPolynomialRing n) T] [IsScalarTower ℂ (complexPolynomialRing n) S]
    [Algebra.Etale (complexPolynomialRing n) T]
    (u : T →ₐ[ℂ] ℂ) (w : S →ₐ[ℂ] ℂ)
    (hw : mvPolynomialAlgHomHomeomorph n (etaleBaseAlgHom (n := n) S w) ∈
      (etaleAlgHomProjectionChart (n := n) T u).target) :
    ∃! g : TensorProduct (complexPolynomialRing n) T S →ₐ[ℂ] ℂ,
      g.comp ((Algebra.TensorProduct.includeLeft :
        T →ₐ[complexPolynomialRing n] TensorProduct (complexPolynomialRing n) T S).restrictScalars ℂ)
          ∈ (etaleAlgHomProjectionChart (n := n) T u).source ∧
      ∀ s : S, g (1 ⊗ₜ[complexPolynomialRing n] s) = w s := by
  let E := etaleAlgHomProjectionChart (n := n) T u
  let v := E.symm (mvPolynomialAlgHomHomeomorph n (etaleBaseAlgHom (n := n) S w))
  have hv : v ∈ E.source := E.map_target hw
  have hbase : etaleBaseAlgHom (n := n) T v = etaleBaseAlgHom (n := n) S w := by
    apply (mvPolynomialAlgHomHomeomorph n).injective
    rw [← etaleAlgHomProjectionChart_apply_of_mem T u v hv]
    exact E.right_inv hw
  obtain ⟨g, hg, _⟩ := a3b4a_gysin_exists_tensor_evaluation v w
    (fun d => congrArg (fun f : complexPolynomialRing n →ₐ[ℂ] ℂ => f d) hbase)
  have hL : g.comp ((Algebra.TensorProduct.includeLeft :
      T →ₐ[complexPolynomialRing n] TensorProduct (complexPolynomialRing n) T S).restrictScalars ℂ) = v := by
    apply AlgHom.ext
    intro t
    change g (t ⊗ₜ[complexPolynomialRing n] 1) = v t
    rw [hg, map_one, mul_one]
  have hsource : g.comp ((Algebra.TensorProduct.includeLeft :
      T →ₐ[complexPolynomialRing n] TensorProduct (complexPolynomialRing n) T S).restrictScalars ℂ)
        ∈ E.source := hL.symm ▸ hv
  have hS : ∀ s : S, g (1 ⊗ₜ[complexPolynomialRing n] s) = w s := by
    intro s
    rw [hg, map_one, one_mul]
  refine ⟨g, ⟨hsource, hS⟩, ?_⟩
  intro f hf
  exact a3b4a_gysin_baseChange_projection_injective T S u f g hf.1 hsource
    (fun s => (hf.2 s).trans (hS s).symm)

end HodgeLean.Adapters
