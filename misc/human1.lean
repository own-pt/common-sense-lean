/-

From adam's serie:

https://www.youtube.com/watch?v=SkruxPmN0kk
https://www.youtube.com/watch?v=nvHatVfiLPU

-/

universe u

constants Entity Hominid Human : Type u
constant subclass : Type u → Type u → Prop

axiom sub_hh : subclass Human Hominid

constant hasBirth (x : Type) (c : Hominid) : subclass x c → Prop

constant h : Human

#check hasBirth h



constant isHominid : Entity  → Prop
constant hasHair : Entity → Prop

def isHuman (x : Entity) : Prop  := isHominid x ∧ hasHair x

constant hasBirth : { x : Entity // isHominid x } → Prop

