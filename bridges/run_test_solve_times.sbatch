#!/bin/bash
#SBATCH -A mth210009p
#SBATCH -N 1
#SBATCH -p RM
#SBATCH -t 24:00:00                  # set duration of the job
#SBATCH --ntasks=1                   # task = one (potentially multithread) computation
#SBATCH --cpus-per-task=128
#SBATCH -o run_test_solve_times.out  # set output name of log file

#echo commands to stdout
set -x

~/eternity2/bridges/run_test_solve_times.sh $1 $2
