#!/bin/bash
#SBATCH -A mth210009p
#SBATCH -N 1
#SBATCH -p RM
#SBATCH -t 24:00:00                  # set duration of the job
#SBATCH --ntasks=1                   # task = one (potentially multithread) computation
#SBATCH --cpus-per-task=128
#SBATCH -o run_solve_board_suite.o%j # set output name of log file

#echo commands to stdout
set -x

~/eternity2/bridges/run_solve_board_suite.sh $SLURM_JOB_ID "$@"
