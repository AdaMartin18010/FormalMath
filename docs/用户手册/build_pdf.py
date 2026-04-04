#!/usr/bin/env python3
"""
FormalMath 用户手册 PDF 生成脚本
使用 weasyprint 或 markdown + pdfkit 生成 PDF
"""

import os
import sys

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
<html>
<head>
<meta charset="utf-8">
<title>FormalMath 用户手册</title>
<style>
    @page {{
        size: A4;
        margin: 2.5cm;
        @bottom-center {{
            content: counter(page);
        }}
    }}
    body {{
        font-family: "Segoe UI", "Microsoft YaHei", "SimSun", sans-serif;
        line-height: 1.8;
        font-size: 11pt;
        color: #333;
    }}
    h1 {{
        color: #2c3e50;
        font-size: 24pt;
        border-bottom: 3px solid #3498db;
        padding-bottom: 10px;
        page-break-before: always;
    }}
    h1:first-of-type {{
        page-break-before: avoid;
    }}
    h2 {{
        color: #34495e;
        font-size: 18pt;
        margin-top: 30px;
        border-left: 4px solid #3498db;
        padding-left: 15px;
    }}
    h3 {{
        color: #7f8c8d;
        font-size: 14pt;
        margin-top: 20px;
    }}
    code {{
        background: #f8f9fa;
        padding: 2px 6px;
        border-radius: 3px;
        font-family: "Consolas", "Monaco", monospace;
        font-size: 10pt;
        color: #e83e8c;
    }}
    pre {{
        background: #f8f9fa;
        padding: 15px;
        border-radius: 5px;
        overflow-x: auto;
        border-left: 4px solid #3498db;
    }}
    pre code {{
        background: none;
        color: #333;
    }}
    table {{
        border-collapse: collapse;
        width: 100%;
        margin: 20px 0;
    }}
    th, td {{
        border: 1px solid #ddd;
        padding: 12px;
        text-align: left;
    }}
    th {{
        background: #3498db;
        color: white;
        font-weight: bold;
    }}
    tr:nth-child(even) {{
        background: #f8f9fa;
    }}
    a {{
        color: #3498db;
        text-decoration: none;
    }}
    a:hover {{
        text-decoration: underline;
    }}
    blockquote {{
        border-left: 4px solid #3498db;
        margin: 20px 0;
        padding: 10px 20px;
        background: #f8f9fa;
        color: #666;
    }}
    hr {{
        border: none;
        border-top: 2px solid #ecf0f1;
        margin: 40px 0;
    }}
    ul, ol {{
        margin: 15px 0;
        padding-left: 30px;
    }}
    li {{
        margin: 8px 0;
    }}
</style>
</head>
<body>
{html_content}
</body>
</html>'''
        
        html_file = '用户手册.html'
        with open(html_file, 'w', encoding='utf-8') as f:
            f.write(html_full)
        
        print(f"✓ HTML 转换完成: {html_file}")
        return html_file
        
    except ImportError:
        print("错误: 需要安装 markdown 库")
        print("运行: pip install markdown")
        return None


def convert_to_pdf_weasyprint(html_file):
    """使用 weasyprint 转换为 PDF"""
    try:
        from weasyprint import HTML, CSS
        
        pdf_file = '用户手册.pdf'
        HTML(html_file).write_pdf(pdf_file)
        
        print(f"✓ PDF 生成完成: {pdf_file}")
        return pdf_file
        
    except ImportError:
        print("错误: 需要安装 weasyprint 库")
        print("运行: pip install weasyprint")
        return None
    except Exception as e:
        print(f"PDF 生成失败: {e}")
        return None


def convert_to_pdf_pdfkit(html_file):
    """使用 pdfkit 转换为 PDF"""
    try:
        import pdfkit
        
        options = {
            'page-size': 'A4',
            'margin-top': '2.5cm',
            'margin-right': '2.5cm',
            'margin-bottom': '2.5cm',
            'margin-left': '2.5cm',
            'encoding': 'UTF-8',
            'enable-local-file-access': None,
            'footer-center': '[page]/[topage]',
            'footer-font-size': '9',
        }
        
        pdf_file = '用户手册.pdf'
        pdfkit.from_file(html_file, pdf_file, options=options)
        
        print(f"✓ PDF 生成完成: {pdf_file}")
        return pdf_file
        
    except ImportError:
        print("错误: 需要安装 pdfkit 库")
        print("运行: pip install pdfkit")
        print("注意: 还需要安装 wkhtmltopdf")
        return None
    except Exception as e:
        print(f"PDF 生成失败: {e}")
        return None


def main():
    """主函数"""
    print("=" * 60)
    print("FormalMath 用户手册 PDF 生成工具")
    print("=" * 60)
    print()
    
    # 步骤1: 合并 Markdown 文件
    print("步骤 1/3: 合并 Markdown 文件...")
    md_file = merge_markdown_files()
    print()
    
    # 步骤2: 转换为 HTML
    print("步骤 2/3: 转换为 HTML...")
    html_file = convert_to_html(md_file)
    if not html_file:
        print("HTML 转换失败，中止")
        return
    print()
    
    # 步骤3: 转换为 PDF
    print("步骤 3/3: 转换为 PDF...")
    
    # 尝试使用 weasyprint
    pdf_file = convert_to_pdf_weasyprint(html_file)
    
    if not pdf_file:
        # 尝试使用 pdfkit
        print("尝试使用 pdfkit...")
        pdf_file = convert_to_pdf_pdfkit(html_file)
    
    print()
    print("=" * 60)
    if pdf_file:
        print(f"✓ 完成! PDF 文件: {pdf_file}")
        print(f"✓ HTML 文件: {html_file}")
        print(f"✓ Markdown 合并文件: {md_file}")
    else:
        print("✗ PDF 生成失败")
        print(f"✓ 但已生成 HTML 文件: {html_file}")
        print("您可以手动将 HTML 打印为 PDF")
    print("=" * 60)


if __name__ == '__main__':
    main()
