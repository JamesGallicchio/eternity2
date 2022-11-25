

## Need to divide N objects into K non-empty piles
## at each point in time, one of the non-empty piles is chosen u. at random, and an object is removed
## game ends when there's only 1 non-empty pile. 

### Maximize number of rounds

### Conjecture: divide as evenly as possible (N/K)

### piles of sizes A, B, C

f(A, B, C) = 1 + f(A-1,B,C)/3 + f(A,B-1,C)/3 + f(A, B, C-1)/3
f(A, 0, 0) = 0
f(0, B, 0) = 0
f(0, 0, C) = 0.

### Idea: always increase the smallest one

### Counter-example: [7,9,1]. Then [8,9,1] is better than [7,9,2].

### Idea: if unbalanced, move one from the tallest to the shortest.

##### Conjecture: f(A+1, B, C-1) >= f(A, B, C). 
            f(A+1, B, C-2)
            # f(A, B, C-1)
             f(A+1, B-1, C-1)

            # f(A, B, C-1)
            f(A-1, B, C) <= f(A, B, C-1) 
             f(A, B-1, C)
