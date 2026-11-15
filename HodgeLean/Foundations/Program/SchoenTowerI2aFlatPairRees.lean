import HodgeLean.Foundations.Program.SchoenTowerI2aFlatReesTransport
import HodgeLean.Foundations.Program.SchoenTowerI2aPairReesGeneration

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

/-- Flat base change identifies the actual paired Rees fraction algebras,
retaining both their coefficient map and the specified fraction generator.
Source: Hartshorne, Algebraic Geometry, II.7, Proposition 7.13;
Mathlib, `Algebra.TensorProduct.adjoin_one_tmul_image_eq_top`. -/
theorem s2v_i2a_flat_pair_rees_base_change
    (R S : Type) [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    (x y : R) :
    let I := Ideal.span {x, y}
    let I' := Ideal.span {algebraMap R S x, algebraMap R S y}
    ∃ e : S ⊗[R] s2t_reesChart I x ≃ₐ[S] s2t_reesChart I' (algebraMap R S x),
      (∀ r, e ((1 : S) ⊗ₜ[R] algebraMap R (s2t_reesChart I x) r) =
        algebraMap S _ (algebraMap R S r)) ∧
      e ((1 : S) ⊗ₜ[R] s2v_i2a_reesFraction I x ⟨y, Ideal.subset_span (by simp)⟩) =
        s2v_i2a_reesFraction I' (algebraMap R S x)
          ⟨algebraMap R S y, Ideal.subset_span (by simp)⟩ := by
  classical
  intro I I'
  let C := s2t_reesChart I x
  let C' := s2t_reesChart I' (algebraMap R S x)
  obtain ⟨φ, hφinj, hbase, hratio⟩ := s2v_i2a_flat_rees_tensor_embedding R S I x
  obtain ⟨t, ht, hyt, hsur⟩ := s2t_pairChart_coordinate R x y
  have htactual : t = s2v_i2a_reesFraction I x ⟨y, Ideal.subset_span (by simp)⟩ :=
    Subtype.ext ht
  have hφt : φ ((1 : S) ⊗ₜ[R] t) = algebraMap S _ (algebraMap R S y) *
      IsLocalization.Away.invSelf (algebraMap R S x) := by
    rw [htactual]
    exact hratio _
  have hgen : Algebra.adjoin R ({t} : Set C) = ⊤ := by
    rw [Algebra.adjoin_singleton_eq_range_aeval]
    exact (AlgHom.range_eq_top _).mpr hsur
  have hTensor : Algebra.adjoin S ({(1 : S) ⊗ₜ[R] t} : Set (S ⊗[R] C)) = ⊤ := by
    simpa only [Set.image_singleton] using
      Algebra.TensorProduct.adjoin_one_tmul_image_eq_top (A := S) {t} hgen
  have hrange : φ.range = C' := by
    calc
      φ.range = (⊤ : Subalgebra S (S ⊗[R] C)).map φ := (Algebra.map_top φ).symm
      _ = (Algebra.adjoin S {(1 : S) ⊗ₜ[R] t}).map φ := by rw [hTensor]
      _ = Algebra.adjoin S {φ ((1 : S) ⊗ₜ[R] t)} := by
        rw [AlgHom.map_adjoin, Set.image_singleton]
      _ = C' := by rw [hφt]; exact (s2v_i2a_pair_rees_adjoin_ratio S _ _).symm
  let e := (AlgEquiv.ofInjective φ hφinj).trans (Subalgebra.equivOfEq _ _ hrange)
  refine ⟨e, ?_, ?_⟩
  · intro r
    apply Subtype.ext
    exact hbase r
  · apply Subtype.ext
    exact hratio _

end HodgeLean.Foundations.Program
