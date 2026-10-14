#!/usr/bin/env bash
# Audit the nine headline statements using this project's Lean toolchain.
# Linux uses Comparator's bubblewrap sandbox. The explicit --local-unsandboxed
# option supports development on macOS; it is not a Palomar verification verdict.
set -euo pipefail
cd "$(dirname "$0")"

comparator_args=()
case "${1:-}" in
  "") ;;
  --local-unsandboxed)
    comparator_args+=(--inadvisably-no-sandbox)
    echo "Local development audit: Linux sandbox isolation is disabled." >&2
    ;;
  *) echo "usage: $0 [--local-unsandboxed]" >&2; exit 2 ;;
esac
if [ "$#" -gt 1 ]; then
  echo "usage: $0 [--local-unsandboxed]" >&2
  exit 2
fi

for required_command in lake lean python3; do
  if ! command -v "$required_command" >/dev/null 2>&1; then
    echo "error: $required_command is required" >&2
    exit 2
  fi
done
if [ "${1:-}" != --local-unsandboxed ] && ! command -v bwrap >/dev/null 2>&1; then
  echo "error: bwrap is required for the sandboxed Linux audit" >&2
  exit 2
fi

lean_prefix=$(lean --print-prefix)
for tool in leanexport leanchecker nanoda_bin con-ron; do
  if [ ! -x "$lean_prefix/bin/$tool" ]; then
    echo "error: the project toolchain does not bundle $tool" >&2
    exit 2
  fi
done

# Palomar supplies its own protected kernel configuration. Mirror that locally
# without adding an external_kernels field to the submitted configuration.
audit_config=$(mktemp "${TMPDIR:-/tmp}/brownian-images-comparator.XXXXXX")
trap 'rm -f "$audit_config"' EXIT
python3 - comparator-config.json "$audit_config" "$lean_prefix" <<'PY'
import json
from pathlib import Path
import sys

source, destination, prefix = sys.argv[1:]
config = json.loads(Path(source).read_text(encoding="utf-8"))
if "external_kernels" in config:
    raise SystemExit("external_kernels is not a Palomar submitter field")
config.pop("enable_nanoda", None)
config["external_kernels"] = {
    "nanoda": [f"{prefix}/bin/nanoda_bin"],
    "con-ron": [f"{prefix}/bin/con-ron"],
}
Path(destination).write_text(json.dumps(config, indent=2) + "\n", encoding="utf-8")
PY

lake comparator --config "$audit_config" "${comparator_args[@]}"
