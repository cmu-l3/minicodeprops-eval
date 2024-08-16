#!/bin/bash

TASK="tactic_prediction"
MAX_ITERS=100
NUM_SAMPLES=32
TEMPERATURES=0.0
DATASET="minicodeprops"
DATA="data/minicodeprops_bench_ps.jsonl"

MODEL="l3lab/ntp-mathlib-context-deepseek-coder-1.3b"
NAME="ntp-mathlib-context-deepseek-coder-1.3b"

OUTPUT_DIR="output/${NAME}_mcp"

REPL_PATH="./repl"
LEAN_PATH="./MiniCodePropsLeanSrc"

python check.py --task ${TASK} --model-name ${MODEL} --dataset-name ${DATASET} --dataset-path ${DATA} --output-dir ${OUTPUT_DIR} --max-iters ${MAX_ITERS} --num-samples ${NUM_SAMPLES} --temperatures ${TEMPERATURES} --repl-path ${REPL_PATH} --lean-env-path ${LEAN_PATH} 
