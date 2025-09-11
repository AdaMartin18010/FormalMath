#!/usr/bin/env python3
import argparse
import json
import os
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DOCS = ROOT / "docs"
META = DOCS / "_meta"


def load_rules():
    rules_path = ROOT / "tools" / "config" / "rules.json"
    if rules_path.exists():
        with open(rules_path, "r", encoding="utf-8") as f:
            return json.load(f)
    return {
        "terminology": {
            "bilingual_required": True
        },
        "symbols": {
            "latex_math_inline": "balanced-$"
        }
    }


def load_terms_symbols():
    ts_path = META / "terms-and-symbols.yaml"
    if not ts_path.exists():
        return {}
    try:
        import yaml  # optional, best-effort
        with open(ts_path, "r", encoding="utf-8") as f:
            return yaml.safe_load(f) or {}
    except Exception:
        return {}


def iter_files(scope, files):
    if files:
        for f in files:
            p = (ROOT / f).resolve()
            if p.is_file():
                yield p
        return
    base = (ROOT / scope).resolve()
    for dirpath, _, filenames in os.walk(base):
        for name in filenames:
            if name.endswith((".md", ".yaml", ".yml")):
                yield Path(dirpath) / name


def check_balanced_dollar(text):
    return text.count("$") % 2 == 0


def check_aliases(text, alias_list):
    issues = []
    for alias in alias_list:
        if alias in text:
            issues.append({"type": "terminology_alias", "token": alias})
    return issues


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--scope", default="docs")
    parser.add_argument("--rules", default="terminology,symbols")
    parser.add_argument("--files", nargs="*")
    parser.add_argument("--report", default="out/report.json")
    args = parser.parse_args()

    rules = load_rules()
    ts = load_terms_symbols()
    forbid_aliases = ts.get("terminology", {}).get("alias_policy", {}).get("forbid_aliases", [])

    files_scanned = 0
    issues = []

    for path in iter_files(args.scope, args.files):
        files_scanned += 1
        try:
            text = path.read_text(encoding="utf-8")
        except Exception as e:
            issues.append({"type": "io_error", "file": str(path), "hint": str(e)})
            continue

        # 跳过元数据与模板目录的内容检查
        rel = path.relative_to(ROOT).as_posix()
        is_meta = rel.startswith("docs/_meta/")
        is_templates = rel.startswith("docs/_templates/")

        if "symbols" in args.rules and not (is_meta or is_templates):
            if not check_balanced_dollar(text):
                issues.append({"type": "latex_unbalanced_inline", "file": str(path), "hint": "补齐$"})

        if "terminology" in args.rules and forbid_aliases and not (is_meta or is_templates):
            for item in check_aliases(text, forbid_aliases):
                item["file"] = str(path)
                issues.append(item)

        link_pattern = re.compile(r"\]\(([^)]+)\)")
        for match in link_pattern.finditer(text):
            href = match.group(1)
            if href.startswith("http://") or href.startswith("https://"):
                continue
            target = (path.parent / href).resolve()
            if not target.exists() and not href.startswith("#"):
                issues.append({"type": "broken_link", "file": str(path), "href": href})

    score = max(0.0, 1.0 - (len(issues) / max(1, files_scanned)))
    report = {"summary": {"files": files_scanned, "issues": len(issues), "score": round(score, 4)}, "issues": issues}

    out_path = (ROOT / args.report).resolve()
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(report, ensure_ascii=False, indent=2), encoding="utf-8")
    print(json.dumps(report, ensure_ascii=False))

    # 阶段性策略：仅输出报告，不中断流水线（待问题收敛后再收紧门禁）
    sys.exit(0)


if __name__ == "__main__":
    main()


