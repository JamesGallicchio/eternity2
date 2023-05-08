#!/bin/bash

LOG_FILE=~/log/solve_board_suite_$1.log

TO_SOLVE=$(  grep -oP "\w+(?= to be solved)" $LOG_FILE)
STARTED=$(   grep "starting" $LOG_FILE | wc -l)
TIMED_OUT=$( grep "ERROR"    $LOG_FILE | wc -l)
FOUND_ALL=$( grep "All"      $LOG_FILE | wc -l)

NOT_STARTED=$( echo "$TO_SOLVE-$STARTED" | bc)
IN_PROGRESS=$( echo "$STARTED-$TIMED_OUT-$FOUND_ALL" | bc )

NEW_SOLS=$(  grep "\.sol"    $LOG_FILE | wc -l)

AVE_CPU=$( sstat -j $1.batch -aPo AveCPU | tail -n 1 )
MAX_RSS=$( sstat -j $1.batch -aPo MaxRSS | tail -n 1 | numfmt --from=iec --to=iec )
ELAPSED=$( sacct -j $1.batch -o elapsed -P | tail -n 1 )

echo "Started $STARTED/$TO_SOLVE ($NOT_STARTED remaining)"
echo "  Running  : $IN_PROGRESS"
echo "  Found All: $FOUND_ALL"
echo "  Timed Out: $TIMED_OUT"
echo ""
echo "Tot. new sols (all boards): $NEW_SOLS"
echo ""
echo -e "Time Elapsed: $ELAPSED\t\tCPU Time: $AVE_CPU\t\tMemory Usage: $MAX_RSS"
echo ""
echo ""
echo "Log Output:"
tail -n 20 $LOG_FILE
