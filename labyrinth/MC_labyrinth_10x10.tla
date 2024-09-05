------------------------ MODULE MC_labyrinth_10x10 --------------------
MAX_X == 9
MAX_Y == 9
\* @type: <<Int, Int>>;
GOAL == <<9, 9>>
\* @type: Set(<<Int, Int>>);
WALLS == {
    <<0, 1>>, <<2, 0>>, <<2, 1>>,
    <<4, 1>>, <<4, 2>>, <<5, 2>>,
    <<0, 3>>, <<1, 3>>, <<2, 3>>,
    <<4, 4>>, <<5, 4>>, <<1, 5>>,
    <<7, 1>>, <<7, 2>>, <<7, 3>>,
    <<7, 5>>, <<8, 5>>, <<9, 5>>,
    <<3, 6>>, <<5, 6>>,
    <<1, 7>>, <<2, 7>>, <<3, 7>>,
    <<4, 7>>, <<5, 7>>, <<6, 7>>,
    <<7, 7>>, <<8, 7>>, <<9, 7>>,
    <<2, 8>>, <<6, 8>>, <<8, 8>>,
    <<0, 9>>, <<4, 9>>
}

VARIABLES
    \* @type: Int;
    x,
    \* @type: Int;
    y

INSTANCE labyrinth

=====================================================================