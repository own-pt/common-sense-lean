import bs_merge_test

constants  SpinalColumn BananaSlug10 : U

/- SUMO axioms -/

/- EDITED (see https://github.com/own-pt/cl-krr/issues/23) -/
axiom a72773 : ∀ a : U, ((ins a Animal)
  ∧ (¬ ∃ p : U, ins p SpinalColumn ∧ part p a)) 
  → ¬ ins a Vertebrate

/- EDITED -/
axiom a72774 : ¬ ∃ s : U, ins s SpinalColumn ∧ part s BananaSlug10

axiom a72772 : ins BananaSlug10 Animal

-- commented in list.kif
axiom novo1 : ∀ (x L : U), ins L Entity → ins L List → ins (ConsFn x L) List