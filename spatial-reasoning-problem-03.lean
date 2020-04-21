/- Spatial Reasoning Problem 03 -/
/- It can be found at: github.com/ontologyportal/sumo/blob/master/tests/SpatialQs.txt -/

/- (3) John is in his house.  John's house is in San Jose.  Is John in San Jose? -/

constant U : Type
universe U

constants Relation BinaryPredicate Entity
located Physical TransitiveRelation : U

constant subclass : U → U → Prop
constant domain: U → ℕ → U → Prop
constant ins : U → U → Prop

constants City SanJose JohnsHouse John Inside : U
constant orientation : U → U → U → Prop
constant holds : U → U → U → Prop

axiom a1 : subclass City Physical               -- (subclass City Physical)
axiom a2 : ins JohnsHouse Physical              -- (instance JohnsHouse Physical)
axiom a3 : ins John Physical                    -- (instance John Physical)
axiom a4 : ins SanJose City                     -- (instance SanJose City)
axiom a5 : orientation John JohnsHouse Inside   -- (orientation John JohnsHouse Inside)
axiom a6 : ins located TransitiveRelation       -- (instance located TransitiveRelation)
axiom a7 : holds located JohnsHouse SanJose  -- (located JohnsHouse SanJose)

/- axioms from SUMO -/
axiom a8 : ∀ (R A B C), (ins R TransitiveRelation) ∧ (holds R A B) ∧ (holds R B C) → holds R A C

/- axioms added -/
axiom a9 : ∀ OBJ1 OBJ2, (orientation OBJ1 OBJ2 Inside) → (holds located OBJ1 OBJ2)

/- Demonstration Start -/
theorem john_is_in_san_jose : holds located John SanJose :=
begin
    have h1, from (a9 _ _) a5,
    exact (a8 _ _ _ _) ⟨a6,⟨h1,a7⟩⟩
end
