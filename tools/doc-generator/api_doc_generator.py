#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
API文档自动生成器
API Documentation Generator

自动从Python源代码中提取文档字符串，生成API参考文档
"""

import ast
import inspect
import importlib.util
from pathlib import Path
from typing import List, Dict, Any, Optional
from datetime import datetime
from dataclasses import dataclass


@dataclass
class APIMember:
    """API成员信息"""
    name: str
    type: str  # module, class, function, method
    docstring: str
    signature: Optional[str] = None
    source_file: Optional[str] = None
    line_number: int = 0
    decorators: List[str] = None
    parameters: List[Dict[str, Any]] = None
    returns: Optional[str] = None
    
    def __post_init__(self):
        if self.decorators is None:
            self.decorators = []
        if self.parameters is None:
            self.parameters = []


class APIDocGenerator:
    """
    API文档生成器
    
    自动解析Python源代码，提取类和函数的文档，生成结构化的API文档
    """
    
    def __init__(self, output_dir: Path, template_dir: Path = None):
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(parents=True, exist_ok=True)
        self.template_dir = template_dir
        self.api_members: List[APIMember] = []
        
    def generate_from_directory(self, source_dir: Path) -> List[str]:
        """
        从目录生成API文档
        
        Args:
            source_dir: 源代码目录
            
        Returns:
            生成的文件路径列表
        """
        generated_files = []
        source_dir = Path(source_dir)
        
        # 查找所有Python文件
        python_files = list(source_dir.rglob("*.py"))
        
        print(f"  找到 {len(python_files)} 个Python文件")
        
        # 解析每个文件
        for py_file in python_files:
            try:
                self._parse_file(py_file)
            except Exception as e:
                print(f"  警告: 解析 {py_file} 失败: {e}")
        
        # 生成文档
        if self.api_members:
            # 生成模块索引
            index_path = self._generate_module_index()
            generated_files.append(str(index_path))
            
            # 按模块生成详细文档
            module_files = self._generate_module_docs()
            generated_files.extend(module_files)
            
            # 生成HTML版本
            html_path = self._generate_html_docs()
            generated_files.append(str(html_path))
            
            # 生成JSON版本
            json_path = self._generate_json_docs()
            generated_files.append(str(json_path))
        
        return generated_files
    
    def _parse_file(self, file_path: Path):
        """解析Python文件"""
        content = file_path.read_text(encoding='utf-8')
        
        try:
            tree = ast.parse(content)
        except SyntaxError as e:
            print(f"  语法错误在 {file_path}: {e}")
            return
        
        module_name = file_path.stem
        
        for node in ast.iter_child_nodes(tree):
            if isinstance(node, ast.ClassDef):
                self._parse_class(node, module_name, file_path)
            elif isinstance(node, ast.FunctionDef):
                self._parse_function(node, module_name, file_path)
    
    def _parse_class(self, node: ast.ClassDef, module_name: str, file_path: Path):
        """解析类定义"""
        docstring = ast.get_docstring(node) or ""
        
        # 获取基类
        bases = []
        for base in node.bases:
            if isinstance(base, ast.Name):
                bases.append(base.id)
            elif isinstance(base, ast.Attribute):
                bases.append(f"{base.value.id}.{base.attr}")
        
        member = APIMember(
            name=node.name,
            type="class",
            docstring=docstring,
            source_file=str(file_path),
            line_number=node.lineno,
            decorators=[d.id for d in node.decorator_list if isinstance(d, ast.Name)]
        )
        self.api_members.append(member)
        
        # 解析类中的方法
        for item in node.body:
            if isinstance(item, ast.FunctionDef):
                self._parse_method(item, node.name, file_path)
    
    def _parse_function(self, node: ast.FunctionDef, module_name: str, file_path: Path):
        """解析函数定义"""
        docstring = ast.get_docstring(node) or ""
        signature = self._get_signature(node)
        
        member = APIMember(
            name=node.name,
            type="function",
            docstring=docstring,
            signature=signature,
            source_file=str(file_path),
            line_number=node.lineno,
            decorators=[d.id for d in node.decorator_list if isinstance(d, ast.Name)],
            parameters=self._get_parameters(node)
        )
        self.api_members.append(member)
    
    def _parse_method(self, node: ast.FunctionDef, class_name: str, file_path: Path):
        """解析方法定义"""
        docstring = ast.get_docstring(node) or ""
        signature = self._get_signature(node)
        
        method_type = "method"
        if node.name.startswith('__') and node.name.endswith('__'):
            method_type = "dunder_method"
        elif node.name.startswith('_'):
            method_type = "private_method"
        
        member = APIMember(
            name=f"{class_name}.{node.name}",
            type=method_type,
            docstring=docstring,
            signature=signature,
            source_file=str(file_path),
            line_number=node.lineno,
            decorators=[d.id for d in node.decorator_list if isinstance(d, ast.Name)],
            parameters=self._get_parameters(node)
        )
        self.api_members.append(member)
    
    def _get_signature(self, node: ast.FunctionDef) -> str:
        """获取函数签名"""
        args = []
        
        # 位置参数
        for arg in node.args.args:
            arg_str = arg.arg
            if arg.annotation:
                if isinstance(arg.annotation, ast.Name):
                    arg_str += f": {arg.annotation.id}"
                elif isinstance(arg.annotation, ast.Constant):
                    arg_str += f": {arg.annotation.value}"
            args.append(arg_str)
        
        # 默认参数
        defaults_start = len(args) - len(node.args.defaults)
        for i, default in enumerate(node.args.defaults):
            if isinstance(default, ast.Constant):
                args[defaults_start + i] += f" = {default.value}"
        
        # 返回类型
        returns = ""
        if node.returns:
            if isinstance(node.returns, ast.Name):
                returns = f" -> {node.returns.id}"
            elif isinstance(node.returns, ast.Constant):
                returns = f" -> {node.returns.value}"
        
        return f"({', '.join(args)}){returns}"
    
    def _get_parameters(self, node: ast.FunctionDef) -> List[Dict[str, Any]]:
        """获取参数信息"""
        params = []
        
        for arg in node.args.args:
            param_info = {
                'name': arg.arg,
                'type': None,
                'default': None
            }
            if arg.annotation:
                if isinstance(arg.annotation, ast.Name):
                    param_info['type'] = arg.annotation.id
                elif isinstance(arg.annotation, ast.Constant):
                    param_info['type'] = arg.annotation.value
            params.append(param_info)
        
        return params
    
    def _generate_module_index(self) -> Path:
        """生成模块索引"""
        output_path = self.output_dir / "index.md"
        
        lines = [
            "# API文档索引\n",
            f"**生成时间**: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n",
            f"**总API数**: {len(self.api_members)}\n\n",
            "## 模块列表\n"
        ]
        
        # 按模块分组
        modules = {}
        for member in self.api_members:
            module = member.source_file.split('\\')[-1] if member.source_file else "unknown"
            if module not in modules:
                modules[module] = []
            modules[module].append(member)
        
        for module, members in sorted(modules.items()):
            lines.append(f"### {module}\n")
            
            # 类
            classes = [m for m in members if m.type == "class"]
            if classes:
                lines.append("**类**:\n")
                for cls in classes:
                    lines.append(f"- `{cls.name}` - {cls.docstring[:50]}...\n")
                lines.append("\n")
            
            # 函数
            functions = [m for m in members if m.type == "function"]
            if functions:
                lines.append("**函数**:\n")
                for func in functions:
                    lines.append(f"- `{func.name}{func.signature or '()'}`\n")
                lines.append("\n")
        
        output_path.write_text(''.join(lines), encoding='utf-8')
        return output_path
    
    def _generate_module_docs(self) -> List[str]:
        """生成各模块详细文档"""
        generated = []
        modules_dir = self.output_dir / "modules"
        modules_dir.mkdir(exist_ok=True)
        
        # 按源文件分组
        by_file = {}
        for member in self.api_members:
            key = member.source_file or "unknown"
            if key not in by_file:
                by_file[key] = []
            by_file[key].append(member)
        
        for file_path, members in by_file.items():
            file_name = Path(file_path).stem
            output_path = modules_dir / f"{file_name}.md"
            
            lines = [f"# {file_name}\n\n"]
            lines.append(f"**源文件**: `{file_path}`\n\n")
            
            # 类
            classes = [m for m in members if m.type == "class"]
            if classes:
                lines.append("## 类\n\n")
                for cls in classes:
                    lines.append(f"### {cls.name}\n\n")
                    lines.append(f"```python\nclass {cls.name}\n```\n\n")
                    if cls.docstring:
                        lines.append(f"{cls.docstring}\n\n")
            
            # 函数
            functions = [m for m in members if m.type == "function"]
            if functions:
                lines.append("## 函数\n\n")
                for func in functions:
                    lines.append(f"### {func.name}\n\n")
                    sig = func.signature or "()"
                    lines.append(f"```python\ndef {func.name}{sig}\n```\n\n")
                    if func.docstring:
                        lines.append(f"{func.docstring}\n\n")
                    
                    if func.parameters:
                        lines.append("**参数**:\n\n")
                        for param in func.parameters:
                            type_str = f": {param['type']}" if param['type'] else ""
                            lines.append(f"- `{param['name']}{type_str}`\n")
                        lines.append("\n")
            
            output_path.write_text(''.join(lines), encoding='utf-8')
            generated.append(str(output_path))
        
        return generated
    
    def _generate_html_docs(self) -> Path:
        """生成HTML格式的API文档"""
        output_path = self.output_dir / "api_reference.html"
        
        css_styles = """
        * { margin: 0; padding: 0; box-sizing: border-box; }
        body { font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, sans-serif; 
               line-height: 1.6; color: #333; background: #f5f7fa; padding: 20px; }
        .container { max-width: 1200px; margin: 0 auto; }
        .header { background: linear-gradient(135deg, #667eea 0%, #764ba2 100%); 
                  color: white; padding: 40px; border-radius: 12px; margin-bottom: 30px; }
        .header h1 { font-size: 2.5em; margin-bottom: 10px; }
        .api-card { background: white; padding: 25px; border-radius: 12px; 
                    margin-bottom: 20px; box-shadow: 0 2px 4px rgba(0,0,0,0.05); }
        .api-card h2 { color: #667eea; margin-bottom: 15px; }
        .api-card .signature { background: #f8f9fa; padding: 15px; border-radius: 6px; 
                               font-family: 'Consolas', monospace; margin: 10px 0; }
        .api-card .docstring { color: #555; margin-top: 15px; }
        .badge { display: inline-block; padding: 4px 12px; border-radius: 12px; 
                 font-size: 0.85em; font-weight: 500; margin-right: 8px; }
        .badge-class { background: #e3f2fd; color: #1976d2; }
        .badge-function { background: #e8f5e9; color: #388e3c; }
        .badge-method { background: #fff3e0; color: #f57c00; }
        """
        
        html_parts = [
            '<!DOCTYPE html>',
            '<html lang="zh-CN">',
            '<head>',
            '    <meta charset="UTF-8">',
            '    <meta name="viewport" content="width=device-width, initial-scale=1.0">',
            '    <title>FormalMath API 文档</title>',
            f'    <style>{css_styles}</style>',
            '</head>',
            '<body>',
            '    <div class="container">',
            '        <div class="header">',
            '            <h1>📚 FormalMath API 文档</h1>',
            f'            <p>生成时间: {datetime.now().strftime("%Y-%m-%d %H:%M:%S")}</p>',
            f'            <p>API总数: {len(self.api_members)}</p>',
            '        </div>'
        ]
        
        for member in self.api_members[:100]:  # 限制显示数量
            badge_class = f"badge-{member.type}"
            html_parts.append('        <div class="api-card">')
            html_parts.append(f'            <span class="badge {badge_class}">{member.type}</span>')
            html_parts.append(f'            <h2>{member.name}</h2>')
            if member.signature:
                html_parts.append(f'            <div class="signature">{member.signature}</div>')
            if member.docstring:
                html_parts.append(f'            <div class="docstring">{member.docstring[:200]}...</div>')
            html_parts.append('        </div>')
        
        html_parts.extend([
            '    </div>',
            '</body>',
            '</html>'
        ])
        
        output_path.write_text('\n'.join(html_parts), encoding='utf-8')
        return output_path
    
    def _generate_json_docs(self) -> Path:
        """生成JSON格式的API文档"""
        output_path = self.output_dir / "api_reference.json"
        
        data = {
            'generated_at': datetime.now().isoformat(),
            'total_apis': len(self.api_members),
            'apis': [
                {
                    'name': m.name,
                    'type': m.type,
                    'signature': m.signature,
                    'docstring': m.docstring,
                    'source_file': m.source_file,
                    'line_number': m.line_number,
                    'parameters': m.parameters
                }
                for m in self.api_members
            ]
        }
        
        import json
        output_path.write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding='utf-8')
        return output_path


def main():
    """主函数 - 示例用法"""
    generator = APIDocGenerator(
        output_dir=Path("tools/doc-generator/output/api"),
        template_dir=Path("tools/doc-generator/templates")
    )
    
    files = generator.generate_from_directory(Path("tools"))
    print(f"\n生成文件:")
    for f in files:
        print(f"  - {f}")


if __name__ == '__main__':
    main()
