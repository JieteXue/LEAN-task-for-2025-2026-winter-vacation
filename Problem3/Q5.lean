import Mathlib.Order.Filter.Tendsto
import Mathlib.Data.Set.Accumulate
import Mathlib.Topology.Bornology.Basic
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Ultrafilter
import Mathlib.Topology.Defs.Ultrafilter
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.BigOperators.Fin
import Init.Prelude
#check Finset.prod_range_succ
lemma yuan {α :Type} [Monoid α] {a:ℕ → α}:(List.map a (List.range 0)).prod=1:=by
 simp
lemma shen {α :Type} [Monoid α] {a:ℕ → α}(i : ℕ):(List.map a (List.range (i+2))).prod
=(List.map a (List.range i)).prod*(a (i)*a (i+1)):=by
 induction' i with n hn
 ·simp
  rw[List.prod_range_succ]
  rw[List.prod_range_succ]
  rw[yuan]
  rw[one_mul]
 ·rw[List.prod_range_succ]
  rw[hn]
  rw[mul_assoc]
  rw[mul_assoc]
  rw[← mul_assoc]
  rw[← List.prod_range_succ]
theorem problem {α :Type} [Monoid α] {a b:ℕ → α}(i c: ℕ):(List.map a (List.range (i+2))).prod *
(List.map b (List.range c)).prod
=(List.map a (List.range i)).prod*(a (i)*a (i+1))*(List.map b (List.range c)).prod:=by
 rw[shen]
