# arm_env.sh, sourced: the environments of a gate arm, one NAME=value per line, for `mapfile -t`: the sweep's (<salt> <out
# dir>) and the held-out check's (<rules file> <law file>, Windows paths). The one home of the sweep's recipe:
# layout_check.sh fails on another script that sets its output variable.
sweep_env() { printf '%s\n' MACHINE_STATE=0 "SALT=$1" "SWEEP_OUT=$2"; }
held_env() { printf '%s\n' MACHINE_STATE=0 CHECK_FAST=1 "CHECK_RULES=$1" "CHECK_LAWFILE=$2"; }
