To calculate (in parallel) all solutions to board suite boards:
```
sbatch run_solve_board_suite.sbatch --suite <directory>
```

To calculate (in parallel) all discrimination search info for
solved board suite boards:
```
sbatch run_calc_discr_search_stats.sbatch --suite <directory>
```

In general <directory> would be `puzzles/board_suite`, but
if you want to limit it to boards of a single size you can
pass that sub-directory in instead. This is useful if the
programs are hitting the memory cap.
