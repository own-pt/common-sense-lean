/- Spatial Reasoning Problem 03 -/
/- It can be found at: github.com/ontologyportal/sumo/blob/master/tests/SpatialQs.txt -/

/- (3) John is in his house.  John's house is in San Jose.  Is John in San Jose? -/

constant U : Type
universe U

constants Physical City TransitiveRelation SanJose JohnsHouse John Inside : U
constant subclass : U → U → Prop
constant ins : U → U → Prop
constant orientation: U → U → U → Prop
constant located : U → U → Prop

/- axioms from problem -/

axiom a1 : subclass City Physical               -- (subclass City Physical)
axiom a2 : ins JohnsHouse Physical              -- (instance JohnsHouse Physical)
axiom a3 : ins John Physical                    -- (instance John Physical)
axiom a4 : ins SanJose City                     -- (instance SanJose City)
axiom a6 : located JohnsHouse SanJose           -- (located JohnsHouse SanJose)
axiom a5 : orientation John JohnsHouse Inside   -- (orientation John JohnsHouse Inside)
axiom a7 : ins located TransitiveRelation       -- (instance located TransitiveRelation)

/- axioms from SUMO -/

axiom a8 : ∀ (R A B C), (ins R TransitiveRelation) ∧ (R A B) ∧ (R A C) → R A C

/- axioms added -/
axiom a9 : ∀ OBJ1 OBJ2, (orientation OBJ1 OBJ2 Inside) → (located OBJ1 OBJ2)
