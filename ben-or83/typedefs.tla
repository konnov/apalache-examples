------------------------------- MODULE typedefs --------------------------------
EXTENDS Variants

(*
 * Type definitions:
 *
 * Type-1 messages.
 * @typeAlias: msgA = { src: REPLICA, r: Int, v: Int };
 *
 * Type-2 messages.
 * @typeAlias: msgB = Q({ src: REPLICA, r: Int }) | D({ src: REPLICA, r: Int, v: Int });
 *)
typedefs_aliases == TRUE

\* predefined constants for the steps
S1 == "S1_OF_STEP"
S2 == "S2_OF_STEP"
S3 == "S3_OF_STEP"

\* @type: (REPLICA, Int, Int) => $msgA;
M1(src, round, value) == [ src |-> src, r |-> round, v |-> value ]

\* @type: (REPLICA, Int) => $msgB;
Q2(src, round) == Variant("Q", [ src |-> src, r |-> round ])

\* @type: $msgB => Bool;
IsQ2(msg) == VariantTag(msg) = "Q"

\* @type: $msgB => { src: REPLICA, r: Int };
AsQ2(msg) == VariantGetUnsafe("Q", msg)

\* @type: (REPLICA, Int, Int) => $msgB;
D2(src, round, value) == Variant("D", [ src |-> src, r |-> round, v |-> value ])

\* @type: $msgB => Bool;
IsD2(msg) == VariantTag(msg) = "D"

\* @type: $msgB => { src: REPLICA, r: Int, v: Int };
AsD2(msg) == VariantGetUnsafe("D", msg)

================================================================================