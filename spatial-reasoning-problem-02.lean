/- Spatial Reasoning Problem 02 -/
/- It can be found at: github.com/ontologyportal/sumo/blob/master/tests/SpatialQs.txt -/

/- (2) If x is on the right of y, and z is on the left of y, then x is on the right of z -/

constant U : Type
universe U

constants X Y Z : U
constants Right Left : U
constant ins : U → U → Prop
constant located : U → U → Prop
constant subclass : U → U → Prop
constant orientation: U → U → U → Prop

/- axioms from problem -/

axiom a1 : orientation X Y Right            -- (orientation X Y Right)
axiom a2 : orientation Z Y Left             -- (orientation Z Y Left)
axiom a3 : ∀ OBJ1 OBJ2,
    (orientation OBJ1 OBJ2 Right) ↔ (orientation OBJ2 OBJ1 Left)

/- axioms to be added -/
axiom a4 : ∀ X Y Z, (orientation X Y Right) ∧ (orientation Z Y Left)
    → (orientation X Z Right)

theorem x_is_on_the_right_of_z: orientation X Z Right :=
    by exact (a4 _ _ _) ⟨a1, a2⟩ 
