---- MODULE LightSwitchProof ----
EXTENDS TLAPS

VARIABLE light

Init == light = "off"

Toggle ==
    \/ /\ light = "off" /\ light' = "on"
    \/ /\ light = "on"  /\ light' = "off"

Next == Toggle

Spec == Init /\ [][Next]_light

TypeInvariant == light \in {"off", "on"}

THEOREM Spec => []TypeInvariant
<1>1. Init => TypeInvariant
      BY DEF Init, TypeInvariant
<1>2. TypeInvariant /\ [Next]_light => TypeInvariant'
  <2>1. ASSUME TypeInvariant, Toggle
        PROVE  TypeInvariant'
        BY <2>1 DEF TypeInvariant, Toggle
  <2>2. ASSUME TypeInvariant, UNCHANGED light
        PROVE  TypeInvariant'
        BY <2>2 DEF TypeInvariant
  <2>3. QED
        BY <2>1, <2>2 DEF Next
<1>3. QED
      BY <1>1, <1>2, PTL DEF Spec
====