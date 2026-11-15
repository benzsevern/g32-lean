import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNReesRelations
import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNStepQuotient
import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNConormalQuotient

/-! # The natural Rees conormal cokernel without adapted transverse equations -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Polynomial
namespace HodgeLean.Foundations.Program.G32Native

variable {A B : Type*} [CommRing A] [CommRing B]

/-- The product of the exceptional parameter with the translated ratio is
already in the original pulled-back slice ideal. -/
theorem paired_c3_rees_total_ideal (f : A →+* B) (u v a : A) (t : B) (I : Ideal A)
    (hk : RingHom.ker (eval₂RingHom f t) = Ideal.span {C v - X * C u})
    (ha : v - a * u ∈ I) :
    I.map f ⊔ Ideal.span {f u * (t - f a)} = I.map f := by
  have hrel : f v = t * f u := by
    have hmem : C v - X * C u ∈ RingHom.ker (eval₂RingHom f t) := by
      rw [hk]
      exact Ideal.subset_span (Set.mem_singleton _)
    change eval₂ f t (C v - X * C u) = 0 at hmem
    simpa only [eval₂_sub, eval₂_C, eval₂_mul, eval₂_X, sub_eq_zero] using hmem
  apply sup_eq_left.mpr
  apply Ideal.span_le.mpr
  intro x hx
  rcases Set.mem_singleton_iff.mp hx with rfl
  have he : f u * (t - f a) = f (v - a * u) := by
    rw [map_sub, map_mul, hrel]
    ring
  rw [he]
  exact Ideal.mem_map_of_mem f ha

/-- The specified ratio generator has exactly the centre-slice ideal as
its kernel, in the actual chart quotient of conormal modules. -/
theorem paired_c3_rees_ideal_generator_kernel
    (f : A →+* B) (u v a : A) (t : B) (I : Ideal A)
    (hs : Function.Surjective (eval₂RingHom f t))
    (hk : RingHom.ker (eval₂RingHom f t) = Ideal.span {C v - X * C u})
    (ha : v - a * u ∈ I) :
    LinearMap.ker (pairedC3ChartIdealGenerator (I.map f) (f u) (t - f a)) =
      I.map f ⊔ Ideal.span {f u, t - f a} := by
  ext b
  change (Submodule.Quotient.mk (b •
    (⟨t - f a, Submodule.mem_sup_right (Ideal.subset_span (Set.mem_singleton _))⟩ :
      ↥(I.map f ⊔ Ideal.span {t - f a} : Ideal B))) :
        pairedC3ChartIdealQuotient (I.map f) (f u) (t - f a)) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  change b * (t - f a) ∈ (I.map f ⊔ Ideal.span {f u * (t - f a)}) ⊔
    (I.map f ⊔ Ideal.span {t - f a}) ^ 2 ↔ _
  rw [paired_c3_rees_total_ideal f u v a t I hk ha]
  exact paired_c3_rees_generator_relations f u v a t I hs hk ha b

/-- The cyclic chart quotient is the reduced centre-slice structure module,
using the original full slice ideal and the original ratio generator. -/
def pairedC3ReesChartIdealEquiv
    (f : A →+* B) (u v a : A) (t : B) (I : Ideal A)
    (hs : Function.Surjective (eval₂RingHom f t))
    (hk : RingHom.ker (eval₂RingHom f t) = Ideal.span {C v - X * C u})
    (ha : v - a * u ∈ I) :
    (B ⧸ (I.map f ⊔ Ideal.span {f u, t - f a})) ≃ₗ[B]
      pairedConormalIdealQuotient (I.map f) (I.map f ⊔ Ideal.span {t - f a}) := by
  let e := (Submodule.quotEquivOfEq _ _
    (paired_c3_rees_ideal_generator_kernel f u v a t I hs hk ha).symm).trans
      ((pairedC3ChartIdealGenerator (I.map f) (f u) (t - f a)).quotKerEquivOfSurjective
        (paired_c3_chart_ideal_generator_surjective (I.map f) (f u) (t - f a)))
  have hh := congrArg (fun T : Ideal B =>
    (show Submodule B B from T ⊔ (I.map f ⊔ Ideal.span {t - f a}) ^ 2).comap
      (I.map f ⊔ Ideal.span {t - f a}).subtype)
        (paired_c3_rees_total_ideal f u v a t I hk ha)
  exact e.trans (Submodule.quotEquivOfEq _ _ hh)

/-- The cokernel of the natural ideal-induced conormal map in a supplied
Rees chart has the untwisted reduced centre-slice structure module. No
choice of transverse generators or local conormal frame occurs in this result.
Source: Hartshorne, Algebraic Geometry, II.7.13 and II.8. -/
def pairedC3ReesConormalCokernelEquiv
    (f : A →+* B) (u v a : A) (t : B) (I : Ideal A)
    (hs : Function.Surjective (eval₂RingHom f t))
    (hk : RingHom.ker (eval₂RingHom f t) = Ideal.span {C v - X * C u})
    (ha : v - a * u ∈ I) :
    ((I.map f ⊔ Ideal.span {t - f a}).Cotangent ⧸
      LinearMap.range (Ideal.mapCotangent (I.map f)
        (I.map f ⊔ Ideal.span {t - f a}) (AlgHom.id B B) le_sup_left)) ≃ₗ[B]
      B ⧸ (I.map f ⊔ Ideal.span {f u, t - f a}) :=
  (pairedConormalCokernelIdealEquiv _ _ le_sup_left).trans
    (pairedC3ReesChartIdealEquiv f u v a t I hs hk ha).symm

end HodgeLean.Foundations.Program.G32Native
