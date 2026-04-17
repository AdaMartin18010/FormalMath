#!/usr/bin/env python3
"""质量门禁检查脚本。

扫描项目中常见的质量违规项，输出 JSON 报告并在发现违规时返回非零退出码。
"""

import argparse
import json
import re
import sys
from pathlib import Path


# 项目根目录（脚本位于 scripts/ 下）
PROJECT_ROOT = Path(__file__).resolve().parent.parent

# 入口文档模式
ENTRY_PATTERNS = ["README.md", "INDEX.md", "00-README.md"]

# 虚假宣传禁止词汇
FORBIDDEN_WORDS = [
    "100% 完成",
    "99.995%",
    "A+ 质量",
    "世界级标准",
]

# 强制要求 references frontmatter 的核心目录
CORE_DIRECTORIES = [
    PROJECT_ROOT / "docs",
    PROJECT_ROOT / "concept",
    PROJECT_ROOT / "数学家理念体系",
]

# Lean4 目录
LEAN4_DIR = PROJECT_ROOT / "docs" / "09-形式化证明" / "Lean4"

# 空壳文档扫描目录
SHELL_DIRECTORIES = [
    PROJECT_ROOT / "docs",
    PROJECT_ROOT / "concept",
    PROJECT_ROOT / "数学家理念体系",
]

# 空壳文档阈值（字节）
SHELL_THRESHOLD = 200

# 默认忽略的目录（与 gitignore 类似）
IGNORED_DIRS = {".git", "node_modules", "__pycache__", ".pytest_cache", "dist", "build", "00-归档"}


def is_ignored(path: Path) -> bool:
    """检查路径是否位于被忽略的目录中。"""
    for part in path.parts:
        if part in IGNORED_DIRS:
            return True
    return False


def find_entry_docs() -> list[Path]:
    """查找所有入口文档。"""
    entries = set()
    # 根目录显式入口文档
    for name in ("README.md", "INDEX.md"):
        p = PROJECT_ROOT / name
        if p.exists():
            entries.add(p)
    # 递归查找入口文档模式
    for pattern in ENTRY_PATTERNS:
        for p in PROJECT_ROOT.rglob(pattern):
            if not is_ignored(p):
                entries.add(p)
    return sorted(entries)


def check_forbidden_words(paths: list[Path]) -> list[dict]:
    """检查入口文档中是否包含禁止词汇。"""
    violations = []
    for path in paths:
        try:
            text = path.read_text(encoding="utf-8")
        except Exception as exc:
            violations.append({
                "file": str(path.relative_to(PROJECT_ROOT)),
                "check": "forbidden_words",
                "message": f"无法读取文件: {exc}",
            })
            continue
        for word in FORBIDDEN_WORDS:
            if word in text:
                # 记录行号
                for lineno, line in enumerate(text.splitlines(), start=1):
                    if word in line:
                        violations.append({
                            "file": str(path.relative_to(PROJECT_ROOT)),
                            "check": "forbidden_words",
                            "word": word,
                            "line": lineno,
                            "message": f"发现禁止词汇 '{word}'",
                        })
    return violations


def extract_frontmatter(text: str) -> str | None:
    """提取 Markdown 文件的 YAML frontmatter（如果存在）。"""
    if not text.startswith("---"):
        return None
    end_match = re.search(r"\n---\s*(?:\n|$)", text, re.MULTILINE)
    if not end_match:
        return None
    return text[:end_match.end()]


def check_references_field() -> list[dict]:
    """检查核心目录下的 .md 文件是否包含 references frontmatter 字段。"""
    violations = []
    for directory in CORE_DIRECTORIES:
        if not directory.exists():
            continue
        for path in directory.rglob("*.md"):
            if is_ignored(path):
                continue
            try:
                text = path.read_text(encoding="utf-8")
            except Exception as exc:
                violations.append({
                    "file": str(path.relative_to(PROJECT_ROOT)),
                    "check": "references_field",
                    "message": f"无法读取文件: {exc}",
                })
                continue
            fm = extract_frontmatter(text)
            if fm is None:
                # 没有 frontmatter，视为缺失 references
                violations.append({
                    "file": str(path.relative_to(PROJECT_ROOT)),
                    "check": "references_field",
                    "message": "缺少 YAML frontmatter，未找到 references 字段",
                })
            elif "references:" not in fm:
                violations.append({
                    "file": str(path.relative_to(PROJECT_ROOT)),
                    "check": "references_field",
                    "message": "YAML frontmatter 中缺少 references 字段",
                })
    return violations


def check_empty_lean_files() -> list[dict]:
    """检查 Lean4 目录中是否存在 0 字节 .lean 文件。"""
    violations = []
    if not LEAN4_DIR.exists():
        return violations
    for path in LEAN4_DIR.rglob("*.lean"):
        if is_ignored(path):
            continue
        size = path.stat().st_size
        if size == 0:
            violations.append({
                "file": str(path.relative_to(PROJECT_ROOT)),
                "check": "empty_lean_file",
                "message": f"发现 0 字节 .lean 文件",
                "size": size,
            })
    return violations


def check_shell_documents() -> list[dict]:
    """检查指定目录中是否存在明显空壳文档（< 200 字节）。"""
    violations = []
    for directory in SHELL_DIRECTORIES:
        if not directory.exists():
            continue
        for path in directory.rglob("*.md"):
            if is_ignored(path):
                continue
            size = path.stat().st_size
            if size < SHELL_THRESHOLD:
                violations.append({
                    "file": str(path.relative_to(PROJECT_ROOT)),
                    "check": "shell_document",
                    "message": f"文档大小仅 {size} 字节，低于阈值 {SHELL_THRESHOLD} 字节",
                    "size": size,
                })
    return violations


def main() -> int:
    parser = argparse.ArgumentParser(
        description="FormalMath 质量门禁检查脚本",
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument(
        "--output",
        "-o",
        type=str,
        default="-",
        help="JSON 报告输出路径，默认为标准输出",
    )
    parser.add_argument(
        "--verbose",
        "-v",
        action="store_true",
        help="输出详细信息",
    )
    args = parser.parse_args()

    entry_docs = find_entry_docs()
    violations: list[dict] = []

    # 1. 禁止词汇检查
    violations.extend(check_forbidden_words(entry_docs))

    # 2. references frontmatter 检查
    violations.extend(check_references_field())

    # 3. 0 字节 lean 文件检查
    violations.extend(check_empty_lean_files())

    # 4. 空壳文档检查
    violations.extend(check_shell_documents())

    report = {
        "status": "failed" if violations else "passed",
        "total_violations": len(violations),
        "violations": violations,
        "summary": {
            "entry_docs_checked": len(entry_docs),
            "forbidden_word_violations": sum(1 for v in violations if v["check"] == "forbidden_words"),
            "references_field_violations": sum(1 for v in violations if v["check"] == "references_field"),
            "empty_lean_file_violations": sum(1 for v in violations if v["check"] == "empty_lean_file"),
            "shell_document_violations": sum(1 for v in violations if v["check"] == "shell_document"),
        },
    }

    json_text = json.dumps(report, ensure_ascii=False, indent=2)
    if args.output == "-":
        print(json_text)
    else:
        out_path = Path(args.output)
        out_path.write_text(json_text, encoding="utf-8")
        if args.verbose:
            print(f"报告已写入: {out_path}")

    return 1 if violations else 0


if __name__ == "__main__":
    sys.exit(main())
