#!/bin/bash
#SBATCH -A mth210009p
#SBATCH -N 1
#SBATCH -p RM
#SBATCH -t 48:00:00                  # set duration of the job
#SBATCH --ntasks=1                   # task = one (potentially multithread) computation
#SBATCH --cpus-per-task=128
#SBATCH -o run_solve_board_suite.o%j # set output name of log file

#echo commands to stdout
set -x

LOG_FILE=~/log/calc_discr_search_stats_$SLURM_JOB_ID.log

~/eternity2/lean/build/bin/eternity2 calc-discr-search-stats --logfile $LOG_FILE "${@}"
