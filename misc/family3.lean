
constant Class : Type

-- SUMO immediateSubclass
@[class] constant subClass : Class → Class → Type

-- SUMO subclass
@[class] constant Inherits : Class → Class → Type

@[instance] constant inhz (c : Class) : Inherits c c
@[instance] constant inhs (c1 c2 c3 : Class) [subClass c1 c2] [Inherits c2 c3] : Inherits c1 c3

constants Human Hominid Entity : Class

@[instance] constant human_hominid : subClass Human Hominid
@[instance] constant hominid_entity : subClass Hominid Entity

set_option class.instance_max_depth 100
set_option trace.class_instances true

noncomputable def test1 : Inherits Human Hominid := by apply_instance
noncomputable def test2 : Inherits Human Entity := by apply_instance


-- constant partition : SetOrClass → SetOrClass → SetOrClass → Prop

