#!/bin/bash

TASK="full_proof"
MAX_ITERS=100
NUM_SAMPLES=32
TEMPERATURES=0.7
DATASET="minicodeprops"
DATA="data/minicodeprops_bench_ps.jsonl"

MODEL="gpt-4o"
NAME="gpt-4o"

OUTPUT_DIR="output/${NAME}_mcp"

REPL_PATH="./repl"
LEAN_PATH="./MiniCodePropsLeanSrc"

python check_api.py --task ${TASK} --model-name ${MODEL} --dataset-name ${DATASET} --dataset-path ${DATA} --output-dir ${OUTPUT_DIR} --max-iters ${MAX_ITERS} --num-samples ${NUM_SAMPLES} --temperatures ${TEMPERATURES} --repl-path ${REPL_PATH} --lean-env-path ${LEAN_PATH} 