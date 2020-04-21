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
axiom a4 : ∀ X Y Z R, (orientation X Y R) ∧ (orientation Y Z R)
    → (orientation X Z R)
axiom a5 : ∀ X Y Z, (orientation X Y Right) ∧ (orientation Z Y Left)
    → (orientation X Z Right)

theorem x_is_on_the_right_of_z: orientation X Z Right :=
begin

end

/-

1. (not (orientation X Z Right)) [] negated_conjecture
2. (forall (?VAR1 ?VAR2 ?VAR3)
    (=> (and (orientation ?VAR3 ?VAR2 Left) (orientation ?VAR1 ?VAR2 Right))
        (orientation ?VAR1 ?VAR3 Right))) [] kb_SUMO_3
3. (forall (?VAR1 ?VAR2 ?VAR3)
    (or (orientation ?VAR1 ?VAR3 Right)
        (not (orientation ?VAR3 ?VAR2 Left))
        (not (orientation ?VAR1 ?VAR2 Right)))) [2] ennf_transformation
4. (forall (?VAR1 ?VAR2 ?VAR3)
    (or (or (orientation ?VAR1 ?VAR3 Right)
        (not (orientation ?VAR3 ?VAR2 Left)))
        (not (orientation ?VAR1 ?VAR2 Right)))) [3] flattening
5. (forall (?VAR1 ?VAR2 ?VAR3)
    (or (or (orientation ?VAR2 ?VAR1 Right)
    (not (orientation ?VAR1 ?VAR3 Left)))
    (not (orientation ?VAR2 ?VAR3 Right)))) [4] cnf_transformation
6. (forall (?VAR1) (or (not (orientation Z ?VAR1 Left))
    (not (orientation X ?VAR1 Right)))) [1, 5] resolution
7. (orientation Z Y Left) [] kb_SUMO_118
8. (not (orientation X Y Right)) [6, 7] resolution
9. (orientation X Y Right) [] kb_SUMO_117
10. false [8, 9] subsumption_resolution

-/
