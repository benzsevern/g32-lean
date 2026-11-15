import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Topology.Separation.Connected

noncomputable section

namespace HodgeLean.Foundations.Program.GeneralTypeIII

variable {G : Type*} [Group G]

/-- Normalization in the ambient group makes the intersection normal in the
normalizing subgroup. -/
theorem pel_normal_intersection (H K : Subgroup G)
    (hn : ∀ g ∈ K, ∀ x ∈ H, g⁻¹ * x * g ∈ H) :
    (H.comap K.subtype).Normal := by
  constructor
  intro x hx g
  change (g : G) * (x : G) * (g : G)⁻¹ ∈ H
  have h := hn (g : G)⁻¹ (K.inv_mem g.property) x hx
  simpa only [inv_inv] using h

/-- A noncentral element gives a nonconstant conjugation orbit. In a T1
topology, continuity and connectedness force that orbit to be infinite. -/
theorem pel_conjugation_orbit_infinite [TopologicalSpace G] [T1Space G]
    (K : Subgroup G) (hK : IsPreconnected (K : Set G))
    (x : G) (hcont : ContinuousOn (fun g : G => g⁻¹ * x * g) (K : Set G))
    (hnoncentral : ∃ g ∈ K, ¬ Commute x g) :
    ((fun g : G => g⁻¹ * x * g) '' (K : Set G)).Infinite := by
  obtain ⟨g, hg, hng⟩ := hnoncentral
  apply (hK.image _ hcont).infinite_of_nontrivial
  refine ⟨x, ?_, g⁻¹ * x * g, ⟨g, hg, rfl⟩, ?_⟩
  · exact ⟨1, K.one_mem, by simp only [inv_one, one_mul, mul_one]⟩
  · intro heq
    apply hng
    change x * g = g * x
    have h := congrArg (fun y : G => g * y) heq
    simpa only [← mul_assoc, mul_inv_cancel, one_mul] using h.symm

/-- The noncentral witness in a normalized intersection rules out a finite
intersection, provided its conjugation orbit is continuous. -/
theorem pel_normal_intersection_infinite [TopologicalSpace G] [T1Space G]
    (H K : Subgroup G) (hK : IsPreconnected (K : Set G))
    (hn : ∀ g ∈ K, ∀ x ∈ H, g⁻¹ * x * g ∈ H)
    (x : G) (hx : x ∈ H) (hxK : x ∈ K)
    (hcont : ContinuousOn (fun g : G => g⁻¹ * x * g) (K : Set G))
    (hnoncentral : ∃ g ∈ K, ¬ Commute x g) :
    ((H ⊓ K : Subgroup G) : Set G).Infinite := by
  apply (pel_conjugation_orbit_infinite K hK x hcont hnoncentral).mono
  rintro y ⟨g, hg, rfl⟩
  exact ⟨hn g hg x hx, K.mul_mem (K.mul_mem (K.inv_mem hg) hxK) hg⟩

#print axioms pel_normal_intersection
#print axioms pel_conjugation_orbit_infinite
#print axioms pel_normal_intersection_infinite

end HodgeLean.Foundations.Program.GeneralTypeIII
