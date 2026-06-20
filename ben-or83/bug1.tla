---- MODULE bug1 ----
EXTENDS Integers, TLAPS
CONSTANT P(_,_), S, T
THEOREM ASSUME NEW x PROVE x \in { P(a,b) : a \in S, b \in T } => TRUE
  OBVIOUS
====
