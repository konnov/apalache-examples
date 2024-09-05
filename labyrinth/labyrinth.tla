----------------------- MODULE labyrinth -----------------------
(* A labyrinth example to demonstrate different exploration
 * techniques in Apalache.
 *
 * Igor Konnov, 2024
 *)
EXTENDS Integers, Sequences

CONSTANT
    \* The maximal x-coordinate.
    \* @type: Int;
    MAX_X,
    \* The maximal y-coordinate.
    \* @type: Int;
    MAX_Y,
    \* The set of walls.
    \* @type: Set(<<Int, Int>>);
    WALLS,
    \* The goal coordinates.
    \* @type: <<Int, Int>>;
    GOAL

VARIABLES
    \* @type: Int;
    x,
    \* @type: Int;
    y

Init == x = 0 /\ y = 0

Left ==
    \E d \in 1 .. MAX_X:
        /\ x - d >= 0 /\ x' = x - d
        /\ \A i \in 1..MAX_X:
            (i <= d) => <<x - i, y>> \notin WALLS
        /\ UNCHANGED y

Right ==
    \E d \in 1 .. MAX_X:
        /\ x + d <= MAX_X /\ x' = x + d
        /\ \A i \in 1..MAX_X:
            (i <= d) => <<x + i, y>> \notin WALLS
        /\ UNCHANGED y

Up ==
    \E d \in 1 .. MAX_Y:
        /\ y - d >= 0 /\ y' = y - d
        /\ \A j \in 1..MAX_Y:
            (j <= d) => <<x, y - j>> \notin WALLS
        /\ UNCHANGED x

Down ==
    \E d \in 1 .. MAX_Y:
        /\ y + d <= MAX_Y /\ y' = y + d
        /\ \A j \in 1..MAX_Y:
            (j <= d) => <<x, y + j>> \notin WALLS
        /\ UNCHANGED x

Next == Left \/ Right \/ Up \/ Down

\* Check this invariant to find a path to the goal:
\* apalache-mc check --length=20 --inv=GoalInv MC_labyrinth_10x10.tla
GoalInv == <<x, y>> /= GOAL

\* Check this invariant to make sure that we do not walk through walls:
\* apalache-mc check --length=20 --inv=NoWallInv MC_labyrinth_10x10.tla
NoWallInv == <<x, y>> \notin WALLS

\* A few definitions to check NoWallInv for arbitrary long executions.

TypeOK ==
    /\ x \in 0..MAX_X
    /\ y \in 0..MAX_Y

\* 1. apalache-mc check --length=0 --init=IndInv --inv=NoWallInv MC_labyrinth_10x10.tla
\* 2. apalache-mc check --length=0 --init=Init --inv=IndInv MC_labyrinth_10x10.tla
\* 3. apalache-mc check --length=1 --init=IndInv --inv=IndInv MC_labyrinth_10x10.tla
IndInv == TypeOK /\ NoWallInv

================================================================