import hashlib
import json
from pathlib import Path


# compare the delivered files with the exact successful verification snapshot.
def main():
    root = Path(__file__).resolve().parent.parent
    receipt = json.loads((root / "audit/verification.json").read_text(encoding="utf-8"))
    if receipt.get("full_nivat_verified") is not True:
        raise SystemExit("the receipt does not record a completed full theorem check")
    checked = 0
    for group in ("library_files", "inputs", "project_files", "logs"):
        for relative, expected in receipt[group].items():
            target = (root / relative).resolve()
            if not target.is_relative_to(root):
                raise SystemExit(f"receipt path leaves the project: {relative}")
            if not target.is_file() or hashlib.sha256(target.read_bytes()).hexdigest() != expected:
                raise SystemExit(f"file differs from the verified snapshot: {relative}")
            checked += 1
    print(f"verified snapshot matches: {checked} files")


if __name__ == "__main__":
    main()
