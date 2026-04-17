#!/usr/bin/env python3
"""将 Markdown 质量仪表盘渲染为单页 HTML。

仅使用 Python 标准库，通过简单的字符串替换实现 Markdown -> HTML 转换。
"""

import argparse
import html
import re
import sys
from pathlib import Path


PROJECT_ROOT = Path(__file__).resolve().parent.parent
DASHBOARD_MD = PROJECT_ROOT / "output" / "00-质量仪表盘.md"
OUTPUT_HTML = PROJECT_ROOT / "output" / "quality-dashboard.html"


def escape_inline(text: str) -> str:
    """转义行内 HTML 特殊字符。"""
    return html.escape(text)


def render_inline(text: str) -> str:
    """渲染行内元素：代码、加粗、斜体、删除线、链接。"""
    # 行内代码 `...`
    text = re.sub(r"`([^`]+)`", r"<code>\1</code>", text)
    # 加粗 **...** 或 __...__
    text = re.sub(r"\*\*(.+?)\*\*", r"<strong>\1</strong>", text)
    text = re.sub(r"__(.+?)__", r"<strong>\1</strong>", text)
    # 斜体 *...* 或 _..._
    text = re.sub(r"\*(.+?)\*", r"<em>\1</em>", text)
    text = re.sub(r"_(.+?)_", r"<em>\1</em>", text)
    # 删除线 ~~...~~
    text = re.sub(r"~~(.+?)~~", r"<del>\1</del>", text)
    # 链接 [text](url)
    text = re.sub(
        r"\[([^\]]+)\]\(([^)]+)\)",
        lambda m: f'<a href="{html.escape(m.group(2))}">{html.escape(m.group(1))}</a>',
        text,
    )
    return text


def md_to_html(md_text: str) -> str:
    """将 Markdown 文本转换为 HTML 片段。"""
    lines = md_text.splitlines()
    html_lines: list[str] = []
    i = 0
    n = len(lines)

    in_code = False
    code_lines: list[str] = []
    code_lang = ""

    in_table = False
    table_rows: list[list[str]] = []

    in_quote = False
    quote_lines: list[str] = []

    in_ul = False
    in_ol = False
    list_items: list[str] = []

    def flush_table():
        nonlocal in_table, table_rows
        if not in_table or not table_rows:
            return
        # 第一行为表头，第二行为分隔行，后续为数据行
        html_lines.append('<table class="dashboard-table">')
        header = table_rows[0]
        html_lines.append("<thead><tr>")
        for cell in header:
            html_lines.append(f"<th>{render_inline(escape_inline(cell.strip()))}</th>")
        html_lines.append("</tr></thead>")
        html_lines.append("<tbody>")
        for row in table_rows[2:]:
            html_lines.append("<tr>")
            for cell in row:
                html_lines.append(f"<td>{render_inline(escape_inline(cell.strip()))}</td>")
            html_lines.append("</tr>")
        html_lines.append("</tbody></table>")
        in_table = False
        table_rows = []

    def flush_quote():
        nonlocal in_quote, quote_lines
        if not in_quote:
            return
        inner = "\n".join(quote_lines)
        # 递归渲染内部（去除开头的 > ）
        inner_html = md_to_html(inner)
        html_lines.append(f'<blockquote class="dashboard-quote">{inner_html}</blockquote>')
        in_quote = False
        quote_lines = []

    def flush_list():
        nonlocal in_ul, in_ol, list_items
        if in_ul:
            html_lines.append("<ul>")
            for item in list_items:
                html_lines.append(f"<li>{render_inline(escape_inline(item.strip()))}</li>")
            html_lines.append("</ul>")
            in_ul = False
        elif in_ol:
            html_lines.append("<ol>")
            for item in list_items:
                html_lines.append(f"<li>{render_inline(escape_inline(item.strip()))}</li>")
            html_lines.append("</ol>")
            in_ol = False
        list_items = []

    while i < n:
        line = lines[i]
        stripped = line.strip()

        # 代码块
        if stripped.startswith("```"):
            if in_code:
                # 结束代码块
                code_content = "\n".join(code_lines)
                html_lines.append(f'<pre><code class="language-{code_lang}">{escape_inline(code_content)}</code></pre>')
                in_code = False
                code_lines = []
                code_lang = ""
            else:
                # 开始代码块
                flush_table()
                flush_quote()
                flush_list()
                in_code = True
                code_lang = stripped[3:].strip() or "text"
            i += 1
            continue

        if in_code:
            code_lines.append(line)
            i += 1
            continue

        # 空行
        if stripped == "":
            flush_table()
            flush_quote()
            flush_list()
            i += 1
            continue

        # 水平线
        if re.match(r"^\s*-{3,}\s*$", stripped):
            flush_table()
            flush_quote()
            flush_list()
            html_lines.append("<hr />")
            i += 1
            continue

        # 标题
        m = re.match(r"^(#{1,6})\s+(.*)$", stripped)
        if m:
            flush_table()
            flush_quote()
            flush_list()
            level = len(m.group(1))
            content = render_inline(escape_inline(m.group(2)))
            html_lines.append(f"<h{level}>{content}</h{level}>")
            i += 1
            continue

        # 引用块
        if stripped.startswith(">"):
            flush_table()
            flush_list()
            in_quote = True
            quote_lines.append(stripped[1:].lstrip())
            i += 1
            continue

        # 无序列表
        if re.match(r"^[-*]\s+", stripped):
            flush_table()
            flush_quote()
            in_ul = True
            list_items.append(re.sub(r"^[-*]\s+", "", stripped))
            i += 1
            continue

        # 有序列表
        if re.match(r"^\d+\.\s+", stripped):
            flush_table()
            flush_quote()
            in_ol = True
            list_items.append(re.sub(r"^\d+\.\s+", "", stripped))
            i += 1
            continue

        # 表格
        if "|" in stripped:
            flush_quote()
            flush_list()
            in_table = True
            cells = [c for c in stripped.split("|")]
            # 去掉首尾空单元格（由开头的 | 引起）
            if cells and cells[0].strip() == "":
                cells = cells[1:]
            if cells and cells[-1].strip() == "":
                cells = cells[:-1]
            table_rows.append(cells)
            i += 1
            continue

        # 普通段落
        flush_table()
        flush_quote()
        flush_list()
        html_lines.append(f"<p>{render_inline(escape_inline(stripped))}</p>")
        i += 1

    flush_table()
    flush_quote()
    flush_list()

    return "\n".join(html_lines)


def build_html(body_html: str, title: str = "FormalMath 质量仪表盘") -> str:
    """将 HTML 片段包装为完整单页 HTML。"""
    return f"""<!DOCTYPE html>
<html lang="zh-CN">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>{title}</title>
<style>
  :root {{
    --bg-color: #f8f9fa;
    --text-color: #212529;
    --accent-color: #0056b3;
    --border-color: #dee2e6;
    --quote-bg: #e9ecef;
    --code-bg: #f1f3f5;
  }}
  body {{
    font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, "Helvetica Neue", Arial, sans-serif;
    line-height: 1.6;
    color: var(--text-color);
    background-color: var(--bg-color);
    max-width: 960px;
    margin: 0 auto;
    padding: 2rem 1rem;
  }}
  h1, h2, h3, h4, h5, h6 {{
    color: var(--accent-color);
    margin-top: 1.8rem;
    margin-bottom: 0.8rem;
  }}
  h1 {{ font-size: 1.8rem; border-bottom: 2px solid var(--border-color); padding-bottom: 0.3rem; }}
  h2 {{ font-size: 1.5rem; }}
  h3 {{ font-size: 1.25rem; }}
  p {{ margin: 0.6rem 0; }}
  a {{ color: var(--accent-color); text-decoration: none; }}
  a:hover {{ text-decoration: underline; }}
  ul, ol {{ margin: 0.5rem 0; padding-left: 1.5rem; }}
  li {{ margin: 0.2rem 0; }}
  code {{
    font-family: SFMono-Regular, Consolas, "Liberation Mono", Menlo, monospace;
    background-color: var(--code-bg);
    padding: 0.15rem 0.3rem;
    border-radius: 3px;
    font-size: 0.9em;
  }}
  pre {{
    background-color: var(--code-bg);
    padding: 1rem;
    border-radius: 5px;
    overflow-x: auto;
  }}
  pre code {{ padding: 0; background: none; }}
  blockquote.dashboard-quote {{
    background-color: var(--quote-bg);
    border-left: 4px solid var(--accent-color);
    margin: 1rem 0;
    padding: 0.8rem 1rem;
    color: #495057;
  }}
  blockquote.dashboard-quote p {{ margin: 0.3rem 0; }}
  table.dashboard-table {{
    width: 100%;
    border-collapse: collapse;
    margin: 1rem 0;
    background-color: #fff;
  }}
  table.dashboard-table th,
  table.dashboard-table td {{
    border: 1px solid var(--border-color);
    padding: 0.6rem 0.8rem;
    text-align: left;
    vertical-align: top;
  }}
  table.dashboard-table th {{
    background-color: #e9ecef;
    font-weight: 600;
  }}
  table.dashboard-table tr:nth-child(even) {{
    background-color: #f8f9fa;
  }}
  hr {{
    border: none;
    border-top: 1px solid var(--border-color);
    margin: 1.5rem 0;
  }}
  .honesty-banner {{
    background-color: #fff3cd;
    border: 1px solid #ffeeba;
    color: #856404;
    padding: 1rem;
    border-radius: 5px;
    margin-bottom: 1.5rem;
  }}
  .honesty-banner strong {{
    color: #856404;
  }}
</style>
</head>
<body>
  <div class="honesty-banner">
    <strong>诚实状态声明：</strong>本仪表盘反映项目的真实质量状态，而非宣传口径。此处披露的数据基于可审计的自动化扫描或人工核查结果，旨在建立公开透明的质量跟踪机制。
  </div>
{body_html}
</body>
</html>
"""


def main() -> int:
    parser = argparse.ArgumentParser(
        description="将 Markdown 质量仪表盘渲染为 HTML",
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument(
        "--input",
        "-i",
        type=str,
        default=str(DASHBOARD_MD),
        help=f"输入的 Markdown 文件路径（默认: {DASHBOARD_MD}）",
    )
    parser.add_argument(
        "--output",
        "-o",
        type=str,
        default=str(OUTPUT_HTML),
        help=f"输出的 HTML 文件路径（默认: {OUTPUT_HTML}）",
    )
    args = parser.parse_args()

    input_path = Path(args.input)
    if not input_path.exists():
        print(f"错误: 输入文件不存在: {input_path}", file=sys.stderr)
        return 1

    md_text = input_path.read_text(encoding="utf-8")
    body_html = md_to_html(md_text)
    full_html = build_html(body_html)

    output_path = Path(args.output)
    output_path.write_text(full_html, encoding="utf-8")
    print(f"HTML 已生成: {output_path}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
