#!/usr/bin/env python3
"""
FormalMath 用户手册 HTML 生成脚本
"""

import os

def merge_markdown_files():
    """合并所有 Markdown 文件为一个文件"""
    
    files = [
        'README.md',
        '01-快速开始指南.md',
        '02-功能使用说明.md',
        '03-学习路径指南.md',
        '04-常见问题解答.md',
        '05-故障排除指南.md'
    ]
    
    merged_content = []
    
    for file in files:
        if os.path.exists(file):
            with open(file, 'r', encoding='utf-8') as f:
                content = f.read()
                merged_content.append(content)
                merged_content.append('\n\n---\n\n')  # 添加分隔线
        else:
            print(f"警告: 文件 {file} 不存在")
    
    # 保存合并后的文件
    with open('用户手册-合并版.md', 'w', encoding='utf-8') as f:
        f.write('\n'.join(merged_content))
    
    print("✓ Markdown 文件合并完成: 用户手册-合并版.md")
    return '用户手册-合并版.md'


def convert_to_html(md_file):
    """将 Markdown 转换为 HTML"""
    try:
        import markdown
        
        with open(md_file, 'r', encoding='utf-8') as f:
            md_content = f.read()
        
        # 使用扩展
        html_content = markdown.markdown(
            md_content,
            extensions=[
                'tables',
                'fenced_code',
                'toc',
                'nl2br'
            ]
        )
        
        # 添加样式
        html_full = f'''<!DOCTYPE html>
<html lang="zh-CN">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>FormalMath 用户手册</title>
<style>
    :root {{
        --primary-color: #3498db;
        --secondary-color: #2c3e50;
        --accent-color: #e74c3c;
        --bg-color: #ffffff;
        --text-color: #333333;
        --code-bg: #f8f9fa;
        --border-color: #e0e0e0;
    }}
    
    * {{
        box-sizing: border-box;
    }}
    
    body {{
        font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", "Microsoft YaHei", "SimSun", sans-serif;
        line-height: 1.8;
        font-size: 16px;
        color: var(--text-color);
        max-width: 900px;
        margin: 0 auto;
        padding: 20px;
        background: var(--bg-color);
    }}
    
    h1 {{
        color: var(--secondary-color);
        font-size: 2em;
        border-bottom: 3px solid var(--primary-color);
        padding-bottom: 15px;
        margin-top: 50px;
    }}
    
    h1:first-of-type {{
        margin-top: 20px;
    }}
    
    h2 {{
        color: var(--secondary-color);
        font-size: 1.6em;
        margin-top: 40px;
        border-left: 4px solid var(--primary-color);
        padding-left: 15px;
    }}
    
    h3 {{
        color: #555;
        font-size: 1.3em;
        margin-top: 30px;
    }}
    
    h4 {{
        color: #666;
        font-size: 1.1em;
        margin-top: 25px;
    }}
    
    p {{
        margin: 15px 0;
    }}
    
    code {{
        background: var(--code-bg);
        padding: 2px 6px;
        border-radius: 3px;
        font-family: "Consolas", "Monaco", "Courier New", monospace;
        font-size: 0.9em;
        color: var(--accent-color);
    }}
    
    pre {{
        background: var(--code-bg);
        padding: 20px;
        border-radius: 8px;
        overflow-x: auto;
        border-left: 4px solid var(--primary-color);
        margin: 20px 0;
    }}
    
    pre code {{
        background: none;
        color: var(--text-color);
        padding: 0;
    }}
    
    table {{
        border-collapse: collapse;
        width: 100%;
        margin: 25px 0;
        box-shadow: 0 2px 4px rgba(0,0,0,0.1);
    }}
    
    th, td {{
        border: 1px solid var(--border-color);
        padding: 12px 15px;
        text-align: left;
    }}
    
    th {{
        background: var(--primary-color);
        color: white;
        font-weight: 600;
    }}
    
    tr:nth-child(even) {{
        background: #f8f9fa;
    }}
    
    tr:hover {{
        background: #e8f4f8;
    }}
    
    a {{
        color: var(--primary-color);
        text-decoration: none;
        border-bottom: 1px dotted var(--primary-color);
    }}
    
    a:hover {{
        border-bottom: 1px solid var(--primary-color);
    }}
    
    blockquote {{
        border-left: 4px solid var(--primary-color);
        margin: 25px 0;
        padding: 15px 25px;
        background: #f8f9fa;
        color: #555;
        font-style: italic;
    }}
    
    hr {{
        border: none;
        border-top: 2px solid var(--border-color);
        margin: 50px 0;
    }}
    
    ul, ol {{
        margin: 20px 0;
        padding-left: 35px;
    }}
    
    li {{
        margin: 10px 0;
    }}
    
    img {{
        max-width: 100%;
        height: auto;
        border-radius: 8px;
    }}
    
    /* 目录样式 */
    .toc {{
        background: #f8f9fa;
        padding: 25px;
        border-radius: 8px;
        margin: 30px 0;
        border: 1px solid var(--border-color);
    }}
    
    .toc ul {{
        list-style: none;
        padding-left: 20px;
    }}
    
    .toc li {{
        margin: 8px 0;
    }}
    
    /* 打印样式 */
    @media print {{
        body {{
            font-size: 12pt;
            max-width: none;
        }}
        
        h1 {{
            page-break-before: always;
        }}
        
        h1:first-of-type {{
            page-break-before: avoid;
        }}
        
        pre {{
            white-space: pre-wrap;
            word-wrap: break-word;
        }}
        
        a {{
            text-decoration: none;
            color: var(--text-color);
        }}
    }}
    
    /* 响应式设计 */
    @media (max-width: 768px) {{
        body {{
            padding: 15px;
            font-size: 15px;
        }}
        
        h1 {{
            font-size: 1.6em;
        }}
        
        h2 {{
            font-size: 1.3em;
        }}
        
        table {{
            font-size: 0.9em;
        }}
        
        th, td {{
            padding: 8px 10px;
        }}
    }}
</style>
</head>
<body>
<div class="header">
<h1>FormalMath 用户手册</h1>
<p style="text-align: center; color: #666;">版本 v1.0 | 2026年4月4日</p>
</div>
{html_content}
<div class="footer" style="margin-top: 50px; padding-top: 20px; border-top: 1px solid #ddd; text-align: center; color: #999; font-size: 0.9em;">
<p>FormalMath 项目 | 开源数学教育知识库</p>
<p>最后更新: 2026年4月4日</p>
</div>
</body>
</html>'''
        
        html_file = 'index.html'
        with open(html_file, 'w', encoding='utf-8') as f:
            f.write(html_full)
        
        print(f"✓ HTML 转换完成: {html_file}")
        return html_file
        
    except ImportError:
        print("错误: 需要安装 markdown 库")
        print("运行: pip install markdown")
        return None
    except Exception as e:
        print(f"错误: {e}")
        return None


def main():
    """主函数"""
    print("=" * 60)
    print("FormalMath 用户手册 HTML 生成工具")
    print("=" * 60)
    print()
    
    # 步骤1: 合并 Markdown 文件
    print("步骤 1/2: 合并 Markdown 文件...")
    md_file = merge_markdown_files()
    print()
    
    # 步骤2: 转换为 HTML
    print("步骤 2/2: 转换为 HTML...")
    html_file = convert_to_html(md_file)
    
    print()
    print("=" * 60)
    if html_file:
        print(f"✓ 完成! HTML 文件: {html_file}")
        print(f"✓ Markdown 合并文件: {md_file}")
        print()
        print("使用说明:")
        print("1. 用浏览器打开 index.html 查看在线文档")
        print("2. 在浏览器中选择'打印'可保存为 PDF")
        print("3. 或使用 pandoc 生成 PDF: pandoc 用户手册-合并版.md -o 用户手册.pdf")
    else:
        print("✗ HTML 生成失败")
    print("=" * 60)


if __name__ == '__main__':
    main()
