import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path


# read historical bytes without checking out or changing the current branch.
def historical_bytes(root, revision, relative):
    return subprocess.check_output(
        ["git", "show", f"{revision}:{relative}"], cwd=root
    )


# compare current files or a historical commit with its saved verification receipt.
def main():
    parser = argparse.ArgumentParser(description="Check the October 1 verification receipt.")
    parser.add_argument("--revision", help="full 40-character commit containing the historical snapshot")
    args = parser.parse_args()
    root = Path(__file__).resolve().parent.parent
    if args.revision and not re.fullmatch(r"[0-9a-f]{40}", args.revision):
        parser.error("--revision requires a full lowercase 40-character commit SHA")

    # the historical receipt and its files must come from the same commit.
    def read_bytes(relative):
        target = (root / relative).resolve()
        if not target.is_relative_to(root):
            raise SystemExit(f"receipt path leaves the project: {relative}")
        if args.revision:
            return historical_bytes(root, args.revision, relative)
        return target.read_bytes()

    receipt = json.loads(read_bytes("audit/verification.json"))
    if receipt.get("full_nivat_verified") is not True:
        raise SystemExit("the receipt does not record a completed full theorem check")
    checked = 0
    for group in ("library_files", "inputs", "project_files", "logs"):
        for relative, expected in receipt[group].items():
            if hashlib.sha256(read_bytes(relative)).hexdigest() != expected:
                raise SystemExit(f"file differs from the verified snapshot: {relative}")
            checked += 1
    location = args.revision or "current working tree"
    print(f"verified snapshot matches: {checked} files ({location})")


if __name__ == "__main__":
    main()
