#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<USAGE
Usage: $(basename "$0") [options]

Options:
  --dim INT                Dimension (default: 6)
  --root INT               Root of unity (default: 12)
  --mubs INT               Target MUB count (default: 3)
  --tab-dir PATH           Table directory (default: tabs_quant_d6_20260218)
  --part-count INT         Number of partitions (default: 64)
  --parallel-jobs INT      Concurrent workers (default: max(1, ncpu-1))
  --threads-per-job INT    --threads passed to each search worker (default: 1)
  --java-xmx SIZE          Java heap per worker, e.g. 1g, 2g (default: 2g)
  --jar-path PATH          Path to assembly jar (default: target/scala-2.13/mub_search_scala-assembly-0.1.0-SNAPSHOT.jar)
  --log-dir PATH           Log output directory (default: runs/partitioned_...)
  --exact                  Use exact table mode (adds --exact)
  --help                   Show help

Environment variables with same names are also supported:
  DIM ROOT MUBS TAB_DIR PART_COUNT PARALLEL_JOBS THREADS_PER_JOB JAVA_XMX JAR_PATH LOG_DIR
USAGE
}

DIM=${DIM:-6}
ROOT=${ROOT:-12}
MUBS=${MUBS:-3}
TAB_DIR=${TAB_DIR:-tabs_quant_d6_20260218}
PART_COUNT=${PART_COUNT:-64}
THREADS_PER_JOB=${THREADS_PER_JOB:-1}
JAVA_XMX=${JAVA_XMX:-2g}
JAR_PATH=${JAR_PATH:-target/scala-2.13/mub_search_scala-assembly-0.1.0-SNAPSHOT.jar}
EXACT_MODE=${EXACT_MODE:-0}

NCPU=$(sysctl -n hw.ncpu 2>/dev/null || getconf _NPROCESSORS_ONLN 2>/dev/null || echo 2)
DEFAULT_JOBS=$((NCPU - 1))
if (( DEFAULT_JOBS < 1 )); then
  DEFAULT_JOBS=1
fi
PARALLEL_JOBS=${PARALLEL_JOBS:-$DEFAULT_JOBS}

while (($# > 0)); do
  case "$1" in
    --dim)
      DIM="$2"; shift 2 ;;
    --root)
      ROOT="$2"; shift 2 ;;
    --mubs)
      MUBS="$2"; shift 2 ;;
    --tab-dir)
      TAB_DIR="$2"; shift 2 ;;
    --part-count)
      PART_COUNT="$2"; shift 2 ;;
    --parallel-jobs)
      PARALLEL_JOBS="$2"; shift 2 ;;
    --threads-per-job)
      THREADS_PER_JOB="$2"; shift 2 ;;
    --java-xmx)
      JAVA_XMX="$2"; shift 2 ;;
    --jar-path)
      JAR_PATH="$2"; shift 2 ;;
    --log-dir)
      LOG_DIR="$2"; shift 2 ;;
    --exact)
      EXACT_MODE=1; shift ;;
    --help)
      usage; exit 0 ;;
    *)
      echo "Unknown argument: $1" >&2
      usage >&2
      exit 2 ;;
  esac
done

if (( PARALLEL_JOBS < 1 )); then
  echo "parallel-jobs must be >= 1" >&2
  exit 2
fi
if (( THREADS_PER_JOB < 1 )); then
  echo "threads-per-job must be >= 1" >&2
  exit 2
fi
if (( PART_COUNT < 1 )); then
  echo "part-count must be >= 1" >&2
  exit 2
fi

MODE="quant"
if (( EXACT_MODE == 1 )); then
  MODE="exact"
fi

ORTH_PATH="$TAB_DIR/orth_dim=${DIM}_root=${ROOT}_${MODE}"
UB_PATH="$TAB_DIR/unbiased_dim=${DIM}_root=${ROOT}_${MODE}"

if ! command -v java >/dev/null 2>&1; then
  echo "Missing java on PATH" >&2
  exit 1
fi
if [[ ! -f "$JAR_PATH" ]]; then
  echo "Missing assembly jar: $JAR_PATH" >&2
  echo "Build it first with: sbt assembly" >&2
  exit 1
fi
if [[ ! -f "$ORTH_PATH" ]]; then
  echo "Missing orth table: $ORTH_PATH" >&2
  exit 1
fi
if [[ ! -f "$UB_PATH" ]]; then
  echo "Missing unbiased table: $UB_PATH" >&2
  exit 1
fi

if [[ -z "${LOG_DIR:-}" ]]; then
  TS=$(date -u +"%Y%m%dT%H%M%SZ")
  LOG_DIR="runs/partitioned_${TS}_d${DIM}_r${ROOT}_m${MUBS}_${MODE}"
fi
mkdir -p "$LOG_DIR"

META_FILE="$LOG_DIR/meta.txt"
{
  echo "start_utc=$(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo "dim=$DIM"
  echo "root=$ROOT"
  echo "mubs=$MUBS"
  echo "tab_dir=$TAB_DIR"
  echo "mode=$MODE"
  echo "part_count=$PART_COUNT"
  echo "parallel_jobs=$PARALLEL_JOBS"
  echo "threads_per_job=$THREADS_PER_JOB"
  echo "java_xmx=$JAVA_XMX"
  echo "jar_path=$JAR_PATH"
  echo "ncpu=$NCPU"
  echo "orth_path=$ORTH_PATH"
  echo "ub_path=$UB_PATH"
} > "$META_FILE"

declare -a PIDS
declare -a LOGS

success_part=""
success_log=""
failed=0

cleanup_running() {
  for ((p=0; p<PART_COUNT; p++)); do
    pid="${PIDS[$p]:-}"
    if [[ -n "$pid" ]]; then
      kill "$pid" 2>/dev/null || true
    fi
  done
  for ((p=0; p<PART_COUNT; p++)); do
    pid="${PIDS[$p]:-}"
    if [[ -n "$pid" ]]; then
      wait "$pid" 2>/dev/null || true
      PIDS[$p]=""
    fi
  done
}

on_signal() {
  echo "Received signal, stopping running workers..." | tee -a "$META_FILE" >&2
  cleanup_running
  exit 130
}
trap on_signal INT TERM

start_worker() {
  local part="$1"
  local log="$LOG_DIR/part_$(printf "%02d" "$part")_of_$(printf "%02d" "$((PART_COUNT-1))").log"
  LOGS[$part]="$log"
  local -a cmd=(
    java
    -XX:+UseParallelGC
    -Xmx"$JAVA_XMX"
    -jar "$JAR_PATH"
    search
    --dim "$DIM"
    --root "$ROOT"
    --mubs "$MUBS"
    --tab_dir "$TAB_DIR"
    --part_worker "$part"
    --part_count "$PART_COUNT"
    --threads "$THREADS_PER_JOB"
  )
  if (( EXACT_MODE == 1 )); then
    cmd+=(--exact)
  fi

  {
    echo "# worker=$part start_utc=$(date -u +%Y-%m-%dT%H:%M:%SZ)"
    date
    printf '# cmd='
    printf '%q ' "${cmd[@]}"
    printf '\n'
    "${cmd[@]}"
    rc=$?
    echo "# worker=$part exit_code=$rc end_utc=$(date -u +%Y-%m-%dT%H:%M:%SZ)"
    exit "$rc"
  } >"$log" 2>&1 &

  PIDS[$part]=$!
  echo "Started worker $part (pid=${PIDS[$part]}) -> $log"
}

running=0
completed=0
next_part=0

while (( running < PARALLEL_JOBS && next_part < PART_COUNT )); do
  start_worker "$next_part"
  ((running+=1))
  ((next_part+=1))
done

while (( completed < PART_COUNT )); do
  # Stop immediately if any running worker has found a witness.
  for ((p=0; p<PART_COUNT; p++)); do
    pid="${PIDS[$p]:-}"
    log="${LOGS[$p]:-}"
    if [[ -n "$pid" && -n "$log" && -f "$log" ]]; then
      if grep -qm1 '^first basis:' "$log"; then
        success_part="$p"
        success_log="$log"
        break
      fi
    fi
  done

  if [[ -n "$success_part" ]]; then
    echo "FOUND COMPLETE EXAMPLE in worker $success_part. Stopping all workers." | tee -a "$META_FILE"
    echo "success_part=$success_part" >> "$META_FILE"
    echo "success_log=$success_log" >> "$META_FILE"
    cleanup_running
    exit 2
  fi

  progressed=0
  for ((p=0; p<PART_COUNT; p++)); do
    pid="${PIDS[$p]:-}"
    if [[ -n "$pid" ]] && ! kill -0 "$pid" 2>/dev/null; then
      progressed=1
      if wait "$pid"; then
        rc=0
      else
        rc=$?
      fi
      PIDS[$p]=""
      ((running-=1))
      ((completed+=1))
      log="${LOGS[$p]:-}"

      if [[ -n "$log" && -f "$log" ]] && grep -qm1 '^first basis:' "$log"; then
        success_part="$p"
        success_log="$log"
        break
      fi

      if (( rc != 0 )); then
        echo "Worker $p exited non-zero (rc=$rc). Log: $log" | tee -a "$META_FILE" >&2
        failed=1
      else
        if [[ -n "$log" && -f "$log" ]] && grep -qm1 "no set of ${MUBS} hadamards" "$log"; then
          echo "Worker $p finished: no set of $MUBS hadamards"
        else
          echo "Worker $p finished without expected terminal marker. Log: $log" | tee -a "$META_FILE"
        fi
      fi
    fi
  done

  if [[ -n "$success_part" ]]; then
    echo "FOUND COMPLETE EXAMPLE in worker $success_part. Stopping all workers." | tee -a "$META_FILE"
    echo "success_part=$success_part" >> "$META_FILE"
    echo "success_log=$success_log" >> "$META_FILE"
    cleanup_running
    exit 2
  fi

  if (( failed != 0 )); then
    echo "Stopping due to worker failure." | tee -a "$META_FILE" >&2
    cleanup_running
    exit 1
  fi

  while (( running < PARALLEL_JOBS && next_part < PART_COUNT )); do
    start_worker "$next_part"
    ((running+=1))
    ((next_part+=1))
  done

  if (( completed >= PART_COUNT )); then
    break
  fi

  if (( progressed == 0 )); then
    sleep 1
  fi
done

echo "All $PART_COUNT workers completed; no complete example of $MUBS MUBs found." | tee -a "$META_FILE"
exit 0
