import «upper_bound».«main»
import «finite_verification».«main»
import Definitions
theorem root : {n : ℕ | digitFactorialSum n = n} = {1, 2, 145, 40585} := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro h
    have hbound := upper_bound n h
    exact (finite_verification n hbound).mp h
  · intro h
    rcases h with rfl | rfl | rfl | rfl
    · exact (finite_verification 1 (by norm_num)).mpr (Or.inl rfl)
    · exact (finite_verification 2 (by norm_num)).mpr (Or.inr (Or.inl rfl))
    · exact (finite_verification 145 (by norm_num)).mpr (Or.inr (Or.inr (Or.inl rfl)))
    · exact (finite_verification 40585 (by norm_num)).mpr (Or.inr (Or.inr (Or.inr rfl)))
