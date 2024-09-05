--------------- MODULE MC_labyrinth_100x100_empty --------------------
MAX_X == 99
MAX_Y == 99
\* @type: <<Int, Int>>;
GOAL == <<99, 99>>
\* @type: Set(<<Int, Int>>);
WALLS == {
}

VARIABLES
    \* @type: Int;
    x,
    \* @type: Int;
    y

INSTANCE labyrinth

=====================================================================