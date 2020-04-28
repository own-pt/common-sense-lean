/- Spatial Reasoning Problem 07 -/
/- It can be found at: SpatialQs.txt -/

/- (7) Pittsburgh is north of Washington, DC.
   New York City is north of Pittsburgh.
   Is New York City north of Washington, DC? -/

constant U : Type

constants North South Pittsburgh Washington_DC New_York
TransitivePositionalAttribute PositionalAttribute : U

constant ins : U → U → Prop
constant located : U → U → Prop
constant subclass : U → U → Prop
constant orientation: U → U → U → Prop

/- axioms from problem -/
axiom a1 : orientation Pittsburgh Washington_DC North
axiom a2 : orientation New_York Pittsburgh North

/- axioms to be added -/
-- (subclass TransitivePositionalAttribute PositionalAttribute)
axiom a3 : subclass TransitivePositionalAttribute PositionalAttribute

-- (instance North TransitivePositionalAttribute)
axiom a4 : ∀ A B C P, (orientation A B P)
    ∧ (orientation B C P)
    ∧ (ins P TransitivePositionalAttribute)
    → (orientation A C P)

-- (instance North TransitivePositionalAttribute)
axiom a5 : ins North TransitivePositionalAttribute

/- demonstration start -/
theorem new_york_city_north_of_washington_dc:
orientation New_York Washington_DC North :=
    by exact (a4 _ _ _ _) ⟨a2 ,⟨a1, a5⟩⟩
