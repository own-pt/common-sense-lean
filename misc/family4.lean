
constant Class : Type

-- SUMO immediateSubclass
constant subClass : Class → Class → Type

-- SUMO subclass
constant Inherits : Class → Class → Type

constant inhz (c : Class) : Inherits c c
constant inhs (c1 c2 c3 : Class) : subClass c1 c2 → Inherits c2 c3 → Inherits c1 c3

constants Human Hominid Entity : Class

constant human_hominid : subClass Human Hominid
constant hominid_entity : subClass Hominid Entity

meta def prove_subclass : tactic unit :=
`[apply human_hominid] <|> `[apply hominid_entity]

meta def prove_inherits : tactic unit :=
`[apply inhz] <|> (`[apply inhs] >> prove_subclass >> prove_inherits)


noncomputable def test1 : Inherits Human Hominid := by prove_inherits

noncomputable def test2 : Inherits Human Entity := by prove_inherits
