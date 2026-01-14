import Sumcheck.Src.Hypercube

noncomputable def expected_hypercube_0 : Finset (Fin 0 → ZMod 19) := { (Fin.elim0 : Fin 0 → ZMod 19) }
lemma it_should_hypercube_n_0_correctly : hypercube_n 0 = expected_hypercube_0 := by
  decide

noncomputable def expected_hypercube_1 : Finset (Fin 1 → ZMod 19) := { ![0], ![1] }
lemma it_should_hypercube_n_1_correctly : hypercube_n 1 = expected_hypercube_1 := by
  decide

noncomputable def expected_hypercube_2 : Finset (Fin 2 → ZMod 19) := { ![0, 0], ![0, 1], ![1, 0], ![1, 1] }
lemma it_should_hypercube_n_2_correctly : hypercube_n 2 = expected_hypercube_2 := by
  decide

noncomputable def expected_hypercube_3 : Finset (Fin 3 → ZMod 19) := { ![0, 0, 0], ![0, 0, 1], ![0, 1, 0], ![0, 1, 1], ![1, 0, 0], ![1, 0, 1], ![1, 1, 0], ![1, 1, 1] }
lemma it_should_hypercube_n_3_correctly : hypercube_n 3 = expected_hypercube_3 := by
  decide
