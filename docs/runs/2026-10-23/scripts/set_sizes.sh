#!/bin/bash
# set_sizes.sh <exe>: mix_streams.sh for triples against pairs: the 35 triples at the pairs' total budget (12000 each,
# 420000 in all) and at the pairs' per-stream budget (20000), then pairs and triples together at 20000 (does a triple
# stream add functions the pairs miss?).
DIR=$(dirname "$0")
SIZES=3 BUDGET=12000 SINGLE=0 bash "$DIR/mix_streams.sh" "$1"
SIZES=3 BUDGET=20000 SINGLE=0 bash "$DIR/mix_streams.sh" "$1"
SIZES="2 3" BUDGET=20000 SINGLE=0 bash "$DIR/mix_streams.sh" "$1"
