import HodgeLean.Foundations.Program.SchoenTowerAdicFunctor

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace HodgeLean.Foundations.Program

/-- The adic map of an algebra structure map is an algebra homomorphism over the source. -/
def s2t_adicAlgHom {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (J : Ideal S) (h : I ≤ J.comap (algebraMap R S)) :
    AdicCompletion I R →ₐ[R] AdicCompletion J S := by
  refine { toRingHom := s2t_adicMap I J (algebraMap R S) h, commutes' := ?_ }
  intro r
  change s2t_adicMap I J (algebraMap R S) h
    (algebraMap R (AdicCompletion I R) r) = algebraMap R (AdicCompletion J S) r
  rw [AdicCompletion.algebraMap_apply]
  change s2t_adicMap I J (algebraMap R S) h (AdicCompletion.of I R r) =
    AdicCompletion.of J S (algebraMap R S r)
  exact s2t_adicMap_of I J (algebraMap R S) h r

/-- The actual adic map induced by an algebra homomorphism preserves its coefficient algebra. -/
def s2t_adicMapAlgHom {K A B : Type*} [CommRing K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] (I : Ideal A) (J : Ideal B) (f : A →ₐ[K] B)
    (h : I ≤ J.comap f.toRingHom) :
    AdicCompletion I A →ₐ[K] AdicCompletion J B := by
  refine { toRingHom := s2t_adicMap I J f.toRingHom h, commutes' := ?_ }
  intro k
  change s2t_adicMap I J f.toRingHom h (algebraMap K (AdicCompletion I A) k) =
    algebraMap K (AdicCompletion J B) k
  rw [AdicCompletion.algebraMap_apply]
  change s2t_adicMap I J f.toRingHom h (AdicCompletion.of I A (algebraMap K A k)) =
    AdicCompletion.of J B (algebraMap K B k)
  rw [s2t_adicMap_of]
  exact congrArg (AdicCompletion.of J B) (f.commutes k)

end HodgeLean.Foundations.Program
