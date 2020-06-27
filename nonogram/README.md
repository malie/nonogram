
# two nonogram solvers

The first searches recursively, the other encodes Nonograms into propositional logic
and uses Armin Biere's [picosat](http://fmv.jku.at/picosat/) to get the solution.

A non-trivial Nonogram is solved in a bit more than 100ms.
(It took me a bit over one one hour to solve)


https://www.nonograms.org/nonograms/i/33908
```
                1   1                    
                1 3 4 1 1           1    
              3 2 2 2 1 1           1 2 2
              1 1 1 1 2 1 3 4 4 5 5 1 5 1
            5 2 2 1 1 1 1 3 1 1 1 4 1 1 1
        1 1|_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |
        2 4|_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |
      1 1 1|_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |
          5|_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |
        2 4|_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |
    1 1 2 1|_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |
    2 1 4 1|_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |
    1 1 4 1|_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |
      1 2 6|_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |
  1 1 2 2 1|_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |
1 1 2 1 1 1|_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |
    2 1 1 1|_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |
  2 1 1 2 2|_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |
      2 3 1|_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |
        3 3|_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |

(("encoding ms",7.620121),("picosat ms",118.722454))

```
[example solution](example-solution.md)
