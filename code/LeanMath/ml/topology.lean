import Mathlib.Topology.Instances.Real.Lemmas

open Set Filter Topology

-- In the next example we could use `tauto` in each proof instead of knowing the lemmas
example {α : Type*} (s : Set α) : Filter α :=
  { sets := { t | s ⊆ t }
    univ_sets := subset_univ s
    sets_of_superset := fun hU hUV ↦ Subset.trans hU hUV
    inter_sets := fun hU hV ↦ subset_inter hU hV }
