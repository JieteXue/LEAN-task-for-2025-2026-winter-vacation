import Mathlib.Tactic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Order.Directed

namespace GLM

variable {K E F : Type*} [NontriviallyNormedField K]
  [NormedAddCommGroup E] [NormedSpace K E]
  [NormedAddCommGroup F] [NormedSpace K F]
  {U : Set (Submodule K E)}

  {mappings : ∀ M ∈ U, M →L[K] F}
  {covering : ∀ x : E, ∃ M ∈ U, x ∈ M}
  {compatible : ∀ {M N} (hM : M ∈ U) (hN : N ∈ U)
    (x : E) (hxM : x ∈ M) (hxN : x ∈ N),
    mappings M hM ⟨x, hxM⟩ = mappings N hN ⟨x, hxN⟩}
  {directed : DirectedOn (· ≤ ·) U}

open Classical

/- The following is the part for Q1
  We show that the mapping is unique first -/

theorem gluedLinearMap_unique
  {covering : ∀ x : E, ∃ M ∈ U, x ∈ M}
  (f g : E →ₗ[K] F)
  (hf : ∀ S (hS : S ∈ U), f.comp S.subtype = mappings S hS)
  (hg : ∀ S (hS : S ∈ U), g.comp S.subtype = mappings S hS) :
  f = g := by
  ext x
  rcases covering x with ⟨S, hS, hx⟩
  calc
    f x = (f.comp S.subtype) ⟨x, hx⟩ := rfl
    _ = mappings S hS ⟨x, hx⟩ := by
      exact congrFun (congrArg DFunLike.coe (hf S hS)) ⟨x, hx⟩
    _ = (g.comp S.subtype) ⟨x, hx⟩ := by
      exact Eq.symm (DFunLike.congr (hg S hS) rfl)
    _ = g x := rfl


/- Then we construct a mapping satisfies the conditions -/

noncomputable
def gluedLinearMap

  (U : Set (Submodule K E))
  (mappings : ∀ M ∈ U, M →L[K] F)
  {covering : ∀ x : E, ∃ M ∈ U, x ∈ M}
  {compatible : ∀ {M N} (hM : M ∈ U) (hN : N ∈ U)
    (x : E) (hxM : x ∈ M) (hxN : x ∈ N),
    mappings M hM ⟨x, hxM⟩ = mappings N hN ⟨x, hxN⟩}
  {directed : DirectedOn (· ≤ ·) U}:

  E →ₗ[K] F :=
  { toFun := fun x =>
      let M := (covering x).choose
      let ⟨hM, hx⟩ := (covering x).choose_spec
      mappings M hM ⟨x, hx⟩


    map_add' := by
      intro x y
      -- Find the subspace containing x and y resp.
      let Mx := (covering x).choose
      let ⟨hMx, hx⟩ := (covering x).choose_spec
      let My := (covering y).choose
      let ⟨hMy, hy⟩ := (covering y).choose_spec

      -- Find a subspace containing both Mx and My
      rcases directed Mx hMx My hMy with ⟨S, hS, hMxS, hMyS⟩
      have hxS : x ∈ S := hMxS hx
      have hyS : y ∈ S := hMyS hy

      -- Find a subspace T containing both S and x+y
      let Mxy := (covering (x + y)).choose
      let ⟨hMxy, hxy⟩ := (covering (x + y)).choose_spec
      rcases directed S hS Mxy hMxy with ⟨T, hT, hST, hMxyT⟩
      have hxT : x ∈ T := hST hxS
      have hyT : y ∈ T := hST hyS
      have hxyT : x + y ∈ T := hMxyT hxy

      simp
      calc
        mappings Mxy hMxy ⟨x + y, hxy⟩
            = mappings T hT ⟨x + y, hxyT⟩ := compatible hMxy hT (x + y) hxy hxyT
        _ = mappings T hT (⟨x, hxT⟩ + ⟨y, hyT⟩) := by simp
        _ = mappings T hT ⟨x, hxT⟩ + mappings T hT ⟨y, hyT⟩ := by rw [map_add]
        _ = mappings Mx hMx ⟨x, hx⟩ + mappings T hT ⟨y, hyT⟩ := by
              rw [compatible hT hMx x hxT hx]
        _ = mappings Mx hMx ⟨x, hx⟩ + mappings My hMy ⟨y, hy⟩ := by
              rw [compatible hT hMy y hyT hy]
    map_smul' := by
      intro c x

      let Mx := (covering x).choose
      let ⟨hMx, hx⟩ := (covering x).choose_spec
      let Mcx := (covering (c • x)).choose
      let ⟨hMcx, hcx⟩ := (covering (c • x)).choose_spec

      rcases directed Mx hMx Mcx hMcx with ⟨S, hS, hMS, hMScx⟩
      have hxS : x ∈ S := hMS hx
      have hcxS : c • x ∈ S := hMScx hcx
      simp

      calc
        mappings Mcx hMcx ⟨c • x, hcx⟩
            = mappings S hS ⟨c • x, hcxS⟩ := compatible hMcx hS (c • x) hcx hcxS
        _ = mappings S hS (c • ⟨x, hxS⟩) := by simp
        _ = c • mappings S hS ⟨x, hxS⟩ := by rw [map_smul]
        _ = c • mappings Mx hMx ⟨x, hx⟩ := by rw [compatible hS hMx x hxS hx]
}






/- The following part is for Q2
  We have defined a linear mapping from E to F,
  now we show that this mapping must be continuous -/

end GLM
