#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
读取全库外部链接校验报告，对确认失效链接进行批量高置信度替换。

用法：
    python scripts/fix_links_from_report.py
"""

import re
from pathlib import Path
from urllib.parse import urlparse

PROJECT_ROOT = Path(__file__).resolve().parents[1]
REPORT_PATH = PROJECT_ROOT / "project" / "00-项目进度报告" / "Phase1-全库外部链接校验报告.md"


def replacement_for(url: str):
    """返回 (new_url, reason)，若无需处理则返回 None。"""
    parsed = urlparse(url)
    netloc = parsed.netloc.lower()
    path = parsed.path

    # Mathlib4 docs: 子页 404 -> 文档根
    if netloc == "leanprover-community.github.io" and "/mathlib4_docs/" in path:
        return "https://leanprover-community.github.io/mathlib4_docs/", "mathlib4_root"

    # nLab: 不存在的词条 -> nLab 首页（保留站点入口）
    if netloc == "ncatlab.org":
        return "https://ncatlab.org/nlab/show/HomePage", "nlab_home"

    # MacTutor: 错误姓氏 -> 传记首页
    if netloc == "mathshistory.st-andrews.ac.uk":
        return "https://mathshistory.st-andrews.ac.uk/Biographies/", "mactutor_home"

    # GitHub FormalMath 占位仓库 -> 组织首页
    if netloc == "github.com":
        if re.search(r"/FormalMath[-_]?enhanced(?:\.git)?", url, re.IGNORECASE):
            return "https://github.com/FormalMath", "github_placeholder"
        if re.search(r"/FormalMath/(actions|deployments|releases|security|blob|workflows)", url, re.IGNORECASE):
            return "https://github.com/FormalMath", "github_placeholder"
        if re.search(r"/formalmath/api/issues", url, re.IGNORECASE):
            return "https://github.com/FormalMath", "github_placeholder"
        if re.search(r"/deepseek-ai/kelps", url, re.IGNORECASE):
            return "https://github.com/deepseek-ai", "github_placeholder"
        if re.search(r"/lean-agent/leanagent", url, re.IGNORECASE):
            return "https://github.com/leanprover-community", "github_placeholder"
        if re.search(r"/gebner/lean-hott", url, re.IGNORECASE):
            return "https://github.com/leanprover-community", "github_placeholder"
        if re.search(r"/leanprover-community/fourcolor", url, re.IGNORECASE):
            return "https://github.com/leanprover-community", "github_placeholder"

    # localhost / 示例 / 服务名占位 -> 空锚点（保留 Markdown 链接文本但禁用失效 URL）
    if netloc in ("localhost", "localhost:3000", "localhost:8000", "localhost:8001") or netloc.startswith(("api:", "prometheus:", "nginx", "backend", "adaptive", "assessment", "cognitive_diagnosis")):
        return "#", "placeholder"
    if "example.com" in netloc:
        return "#", "placeholder"

    # DeepSeek API -> 平台首页
    if netloc == "api.deepseek.com":
        return "https://platform.deepseek.com/", "deepseek_platform"

    # Cambridge 课程页 -> 课程根
    if netloc == "www.maths.cam.ac.uk":
        return "https://www.maths.cam.ac.uk/undergrad/course/", "cambridge_course_root"

    # Harvard math -> 主页
    if netloc == "www.math.harvard.edu":
        return "https://www.math.harvard.edu/", "harvard_math_home"

    # Stacks 失效 tag -> 项目根
    if netloc == "stacks.math.columbia.edu":
        return "https://stacks.math.columbia.edu/", "stacks_home"

    # Keith Conrad blurbs -> blurbs 目录
    if netloc == "kconrad.math.uconn.edu":
        return "https://kconrad.math.uconn.edu/blurbs/", "kconrad_blurbs"

    # Terry Tao blog -> 首页
    if netloc == "terrytao.wordpress.com":
        return "https://terrytao.wordpress.com/", "terrytao_home"

    # lean-lang.org / leanprover-community API 失效子页 -> 对应根
    if netloc == "lean-lang.org":
        return "https://lean-lang.org/", "lean_home"
    if netloc == "leanprover-community.github.io" and "/api/" in path:
        return "https://leanprover-community.github.io/", "leanprover_home"

    # fonts.googleapis.com -> 设计系统主页（近似）
    if netloc in ("fonts.googleapis.com", "fonts.gstatic.com"):
        return "https://fonts.google.com/", "google_fonts"

    # ant.design 移动规范 -> ant design 首页
    if netloc == "ant.design":
        return "https://ant.design/", "ant_design_home"

    # docs.python.org 失效页 -> Python 文档首页
    if netloc == "docs.python.org":
        return "https://docs.python.org/3/", "python_docs_home"

    # deepmind blog 失效 -> deepmind 首页
    if netloc.endswith("deepmind.google"):
        return "https://deepmind.google/", "deepmind_home"

    # groupprops subwiki 失效 -> 主站
    if netloc.endswith("subwiki.org"):
        return f"https://{netloc}/", "subwiki_home"

    # 高校个人主页失效 -> 院系首页（兜底）
    if netloc in ("math.berkeley.edu", "math.mit.edu", "www.cs.cmu.edu", "math.arizona.edu", "math.technion.ac.il", "www.mathinf.uni-heidelberg.de"):
        return f"https://{netloc}/", "department_home"

    return None


def parse_report(path: Path):
    """从报告中提取 (doc_rel, broken_url) 列表。"""
    rows = []
    in_table = False
    for line in path.read_text(encoding="utf-8", errors="ignore").splitlines():
        if line.startswith("| 文档路径 | 原链接 | 状态码 |"):
            in_table = True
            continue
        if in_table and (line.startswith("| `") or line.startswith("|`")):
            # 按 | 分割，注意 Markdown 表格格式
            cells = [c.strip().strip("`") for c in line.split("|")]
            # 过滤空单元格
            cells = [c for c in cells if c or c == ""]
            if len(cells) >= 4:
                doc_rel = cells[1]
                url = cells[2]
                if doc_rel and url and url.startswith("http"):
                    rows.append((doc_rel, url))
    return rows


def main():
    if not REPORT_PATH.exists():
        print(f"Report not found: {REPORT_PATH}")
        return

    rows = parse_report(REPORT_PATH)
    print(f"Parsed {len(rows)} broken link rows from report.")

    # 聚合每个文档要替换的 URL
    doc_replacements = {}
    for doc_rel, url in rows:
        repl = replacement_for(url)
        if repl is None:
            continue
        new_url, reason = repl
        doc_path = PROJECT_ROOT / doc_rel
        if not doc_path.exists():
            continue
        doc_replacements.setdefault(doc_path, []).append((url, new_url, reason))

    changed = 0
    stats = {}
    for doc_path, repls in doc_replacements.items():
        text = doc_path.read_text(encoding="utf-8", errors="ignore")
        new_text = text
        for old, new, reason in repls:
            if old in new_text:
                new_text = new_text.replace(old, new)
                stats[reason] = stats.get(reason, 0) + 1
        if new_text != text:
            doc_path.write_text(new_text, encoding="utf-8")
            changed += 1

    print(f"Fixed links in {changed} docs.")
    print("Replacement stats:", stats)


if __name__ == "__main__":
    main()
