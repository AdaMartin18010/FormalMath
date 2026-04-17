#!/usr/bin/env python3
"""自动更新质量仪表盘中的可自动化指标。

统计 Markdown / Lean4 文件数量，并更新 output/00-质量仪表盘.md 中的对应行。
"""

import argparse
import re
import sys
from datetime import datetime, timezone
from pathlib import Path


PROJECT_ROOT = Path(__file__).resolve().parent.parent
DASHBOARD_PATH = PROJECT_ROOT / "output" / "00-质量仪表盘.md"

# 默认忽略的目录
IGNORED_DIRS = {".git", "node_modules", "__pycache__", ".pytest_cache", "dist", "build", "00-归档"}


def is_ignored(path: Path) -> bool:
    """检查路径是否位于被忽略的目录中。"""
    for part in path.parts:
        if part in IGNORED_DIRS:
            return True
    return False


def count_md_files(root: Path) -> int:
    """统计指定根目录下的 .md 文件数（排除忽略目录）。"""
    if not root.exists():
        return 0
    return sum(1 for p in root.rglob("*.md") if not is_ignored(p))


def count_lean_files() -> int:
    """统计全项目中 .lean 文件总数。"""
    return sum(1 for p in PROJECT_ROOT.rglob("*.lean") if not is_ignored(p))


def update_dashboard(dry_run: bool = False) -> tuple[str, dict]:
    """读取仪表盘，更新自动化指标，返回新内容和变更摘要。"""
    if not DASHBOARD_PATH.exists():
        raise FileNotFoundError(f"仪表盘文件不存在: {DASHBOARD_PATH}")

    text = DASHBOARD_PATH.read_text(encoding="utf-8")
    today = datetime.now(timezone.utc).strftime("%Y-%m-%d")

    # 统计数据
    total_md = count_md_files(PROJECT_ROOT)
    docs_md = count_md_files(PROJECT_ROOT / "docs")
    lean_total = count_lean_files()

    changes = {
        "total_md": total_md,
        "docs_md": docs_md,
        "lean_total": lean_total,
        "date": today,
    }

    # 更新表格行：| 全项目 Markdown 文档数 | ... | ... | YYYY-MM-DD |
    def repl_total_md(match: re.Match) -> str:
        return f"| 全项目 Markdown 文档数 | {total_md} | 自动化扫描 | {today} |"

    text = re.sub(
        r"\| 全项目 Markdown 文档数 \s*\|[^|]+\|[^|]+\|[^|]+\|",
        repl_total_md,
        text,
    )

    def repl_docs_md(match: re.Match) -> str:
        return f"| docs/ 目录文档数 | {docs_md} | 自动化扫描 | {today} |"

    text = re.sub(
        r"\| docs/ 目录文档数 \s*\|[^|]+\|[^|]+\|[^|]+\|",
        repl_docs_md,
        text,
    )

    def repl_lean(match: re.Match) -> str:
        return f"| Lean4 `.lean` 文件总数 | {lean_total} | 自动化扫描 | {today} |"

    text = re.sub(
        r"\| Lean4 `\.lean` 文件总数 \s*\|[^|]+\|[^|]+\|[^|]+\|",
        repl_lean,
        text,
    )

    if not dry_run:
        DASHBOARD_PATH.write_text(text, encoding="utf-8")

    return text, changes


def main() -> int:
    parser = argparse.ArgumentParser(
        description="自动更新 FormalMath 质量仪表盘中的可自动化指标",
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument(
        "--dry-run",
        "-n",
        action="store_true",
        help="仅输出将要更新的内容，不实际写入文件",
    )
    parser.add_argument(
        "--output",
        "-o",
        type=str,
        default=None,
        help="将更新后的仪表盘内容输出到指定文件（dry-run 时也可用）",
    )
    args = parser.parse_args()

    new_text, changes = update_dashboard(dry_run=args.dry_run)

    if args.dry_run:
        print("[DRY-RUN] 以下内容将被更新到仪表盘:\n")
    else:
        print("[DONE] 仪表盘已更新:\n")

    print(f"  全项目 Markdown 文档数 : {changes['total_md']}")
    print(f"  docs/ 目录文档数       : {changes['docs_md']}")
    print(f"  Lean4 .lean 文件总数   : {changes['lean_total']}")
    print(f"  更新日期               : {changes['date']}")
    print(f"  目标文件               : {DASHBOARD_PATH}")

    if args.output:
        out_path = Path(args.output)
        out_path.write_text(new_text, encoding="utf-8")
        print(f"\n内容已额外写入: {out_path}")

    return 0


if __name__ == "__main__":
    sys.exit(main())
