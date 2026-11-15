import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.NhdsWithin

open Set Topology Filter
namespace HodgeLean.Foundations.Program

/-- An open embedding inherits a nonisolated marked image point. -/
theorem s0_punctured_neBot_of_open_embedding
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {f : A → B} (hf : IsOpenEmbedding f) (a : A)
    [NeBot (𝓝[≠] (f a))] : NeBot (𝓝[≠] a) := by
  constructor
  intro h
  have ha := (isOpen_singleton_iff_punctured_nhds a).mpr h
  have hb : IsOpen ({f a} : Set B) := by
    simpa only [Set.image_singleton] using hf.isOpenMap _ ha
  exact (Filter.neBot_iff.mp (inferInstance : NeBot (𝓝[≠] (f a))))
    ((isOpen_singleton_iff_punctured_nhds (f a)).mp hb)

#print axioms s0_punctured_neBot_of_open_embedding
end HodgeLean.Foundations.Program
