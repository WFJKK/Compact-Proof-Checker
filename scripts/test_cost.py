#!/usr/bin/env python3
"""Reproduction of cost-v4: `compactcheck cost` against the Python checker on proof files of real runs.

    python3 scripts/test_cost.py <pipeline repo> <run folder> [<run folder> ...] [--limit N] [--only TEXT] [--log FILE]

For every proof file of the runs' development networks (round_*/attempt_*/proofs/<network>__<knob>.json.gz),
runs the Python checker (core.check.checker.check_proof, the current cost model) and `compactcheck cost`, and
compares the certified count and the length, category by category. Networks are exported once into a
cache next to the log. Resumes from the log if interrupted. Prints every difference and a summary; exits 1
if any proof differs.

Needs the pipeline's Python environment and `lake build compactcheck`.
"""

from __future__ import annotations

import argparse
import gzip
import json
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
PROJECT = HERE.parent
CHECKER = PROJECT / ".lake" / "build" / "bin" / "compactcheck"


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("repo", type=Path)
    ap.add_argument("runs", type=Path, nargs="+")
    ap.add_argument("--limit", type=int, default=0)
    ap.add_argument("--only", default="", help="only records whose id contains this text")
    ap.add_argument("--log", type=Path, default=Path("cost-compare.jsonl"))
    args = ap.parse_args()
    repo = args.repo.resolve()
    sys.path.insert(0, str(repo))
    from core.check.checker import check_proof
    from core.model_folder import load_model_folder
    from core.zoo import networks

    done = set()
    if args.log.exists():
        for line in args.log.read_text().splitlines():
            if line.strip():
                done.add(json.loads(line)["record_id"])
    cache = args.log.parent / "cost-networks"
    cache.mkdir(parents=True, exist_ok=True)
    agree = differ = new = 0
    for run in args.runs:
        cfg = json.loads(json.dumps(__import__("yaml").safe_load((run / "config.yaml").read_text())))
        model = cfg["model"]
        folder = load_model_folder(repo / model)
        dev = {e["id"] for e in networks(folder)}
        for line in (run / "archive.jsonl").read_text().splitlines():
            if not line.strip():
                continue
            rec = json.loads(line)
            if rec.get("status") != "ok" or rec["network"] not in dev or rec["record_id"] in done:
                continue
            if args.only and args.only not in rec["record_id"]:
                continue
            gz = run / f"round_{rec['round']:03d}" / f"attempt_{rec['attempt']}" / "proofs" / f"{rec['network']}__{knob_label(rec)}.json.gz"
            if not gz.exists():
                continue
            net_json = cache / f"{rec['network']}.json"
            if not net_json.exists():
                r = subprocess.run([sys.executable, "-B", str(HERE / "export_network.py"), str(repo), model, rec["network"], str(net_json)],
                                   capture_output=True, text=True)
                if r.returncode != 0:
                    print(f"{rec['network']}: export failed: {r.stderr[-300:]}")
                    continue
            proof = json.loads(gzip.decompress(gz.read_bytes()))
            py = check_proof(proof, folder, rec["network"])
            with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False) as f:
                json.dump(proof, f)
                proof_path = f.name
            r = subprocess.run([str(CHECKER), "cost", str(net_json), proof_path], capture_output=True, text=True, timeout=3600)
            Path(proof_path).unlink()
            last = r.stdout.strip().splitlines()[-1] if r.stdout.strip() else ""
            lean = json.loads(last) if last.startswith("{") else {"status": "error", "reason": r.stderr[-300:]}
            row = {"record_id": rec["record_id"], "python": py["certified"], "python_length": py["length"],
                   "python_by_rule": py.get("length_by_rule"), "lean": lean.get("certified"), "lean_length": lean.get("length"),
                   "lean_by_category": lean.get("by_category"), "lean_status": lean.get("status", "ok"), "lean_reason": lean.get("reason")}
            row["agree"] = row["python"] == row["lean"] and row["python_length"] == row["lean_length"]
            with open(args.log, "a") as f:
                f.write(json.dumps(row) + "\n")
            new += 1
            if row["agree"]:
                agree += 1
            else:
                differ += 1
                print(f"{rec['record_id']}: Python {py['certified']} / {py['length']} {py.get('length_by_rule')}; "
                      f"Lean {row['lean']} / {row['lean_length']} {row['lean_by_category']} {row['lean_reason'] or ''}")
            if args.limit and new >= args.limit:
                break
    print(f"{agree} agree, {differ} differ ({new} new); log {args.log}")
    return 1 if differ else 0


def knob_label(rec: dict) -> str:
    """As core.archive.knob_label: the budget when the run scores at fixed budgets, else the knob value."""
    b = rec.get("budget")
    return f"b{int(b)}" if b is not None else f"k{float(rec['knob']):g}"


if __name__ == "__main__":
    sys.exit(main())
