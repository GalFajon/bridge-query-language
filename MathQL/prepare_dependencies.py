"""Work around lean-json v0.3.0's deprecation warnings under Lean v4.35.

Run after Lake has fetched dependencies and before ``lake build``. The patch is
limited to Lake's ignored package cache; it does not change upstream sources.
"""

from pathlib import Path


def main() -> None:
    lakefile = Path(__file__).resolve().parent / ".lake/packages/json/lakefile.lean"
    source = lakefile.read_text(encoding="utf-8")
    old = "leanOptions := #[⟨`warningAsError, true⟩]"
    new = "leanOptions := #[⟨`warningAsError, false⟩]"
    if new in source:
        print("lean-json compatibility setting is already applied")
        return
    if source.count(old) != 1:
        raise RuntimeError(f"Expected lean-json v0.3.0 setting not found in {lakefile}")
    lakefile.write_text(source.replace(old, new), encoding="utf-8")
    print("Disabled warnings-as-errors in Lake's cached lean-json v0.3.0")


if __name__ == "__main__":
    main()
