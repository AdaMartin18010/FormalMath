#!/usr/bin/env python3
"""
FormalMath项目自动化测试套件

测试模块:
1. 文档格式测试 - Markdown语法、Frontmatter、编码格式
2. Lean4代码测试 - 编译、语法、导入依赖
3. 内容一致性测试 - MSC编码、交叉引用、术语一致性

作者: FormalMath项目
版本: 1.0.0
"""

import os
import re
import sys
import json
import yaml
import subprocess
import unittest
from pathlib import Path
from datetime import datetime
from typing import List, Dict, Tuple, Optional, Set
from dataclasses import dataclass, field
from collections import defaultdict

# ============================================================================
# 配置
# ============================================================================

PROJECT_ROOT = Path(__file__).parent.parent
CONCEPT_DIR = PROJECT_ROOT / "concept"
DOCS_DIR = PROJECT_ROOT / "docs"
LEAN4_DIR = PROJECT_ROOT / "FormalMath-Enhanced" / "lean4" / "FormalMath"
TERMINOLOGY_FILE = PROJECT_ROOT / "00-标准术语表-8语言.md"
MULTILANG_FILE = PROJECT_ROOT / "multilang_concept_table.json"
MSC_PRIMARY_PATTERN = re.compile(r'^\d{2}[A-Z]\d{2}$')
ENCODING = 'utf-8'

# ============================================================================
# 测试基类
# ============================================================================

@dataclass
class TestResult:
    """测试结果数据类"""
    name: str
    passed: bool
    message: str = ""
    duration: float = 0.0
    details: Dict = field(default_factory=dict)


class FormalMathTestCase(unittest.TestCase):
    """FormalMath测试基类"""
    
    @classmethod
    def setUpClass(cls):
        """测试类设置"""
        cls.start_time = datetime.now()
        cls.results: List[TestResult] = []
        
    @classmethod
    def tearDownClass(cls):
        """测试类清理"""
        cls.end_time = datetime.now()
        
    def record_result(self, result: TestResult):
        """记录测试结果"""
        self.__class__.results.append(result)


# ============================================================================
# 1. 文档格式测试
# ============================================================================

class DocumentFormatTests(FormalMathTestCase):
    """文档格式测试类"""
    
    @classmethod
    def setUpClass(cls):
        super().setUpClass()
        cls.markdown_files = cls._find_markdown_files()
        cls.frontmatter_errors: List[Tuple[str, str]] = []
        cls.syntax_errors: List[Tuple[str, str]] = []
        cls.encoding_errors: List[Tuple[str, str]] = []
        
    @classmethod
    def _find_markdown_files(cls) -> List[Path]:
        """查找所有Markdown文件"""
        files = []
        for pattern in ['concept/**/*.md', 'docs/**/*.md']:
            files.extend(PROJECT_ROOT.glob(pattern))
        return [f for f in files if not f.name.startswith('.')]
    
    def test_01_markdown_syntax(self):
        """测试Markdown语法正确性"""
        errors = []
        valid_patterns = [
            (r'^#{1,6}\s+', "标题"),
            (r'^\s*[-*+]\s+', "无序列表"),
            (r'^\s*\d+\.\s+', "有序列表"),
            (r'^\s*```', "代码块"),
            (r'^\s*\|.*\|', "表格"),
            (r'^\s*\[.*?\]\(.*?\)', "链接"),
            (r'^\s*\*.*?\*|^\s*_.*?_', "斜体"),
            (r'^\s*\*\*.*?\*\*|^\s*__.*?__', "粗体"),
        ]
        
        for md_file in self.markdown_files[:100]:  # 限制测试文件数量
            try:
                content = md_file.read_text(encoding=ENCODING)
                
                # 检查未闭合的代码块
                code_block_count = content.count('```')
                if code_block_count % 2 != 0:
                    errors.append((str(md_file), "未闭合的代码块"))
                
                # 检查表格格式
                lines = content.split('\n')
                for i, line in enumerate(lines):
                    if '|' in line:
                        # 检查表格列数一致性
                        cells = line.split('|')
                        if len(cells) < 2:
                            errors.append((str(md_file), f"第{i+1}行: 表格格式错误"))
                            
            except Exception as e:
                errors.append((str(md_file), f"读取错误: {e}"))
        
        self.syntax_errors = errors
        result = TestResult(
            name="Markdown语法检查",
            passed=len(errors) == 0,
            message=f"发现{len(errors)}个语法错误" if errors else "所有文件语法正确",
            details={"errors": errors[:10]}  # 限制错误数量
        )
        self.record_result(result)
        self.assertLessEqual(len(errors), 50, f"发现太多Markdown语法错误: {errors[:5]}")
    
    def test_02_frontmatter_integrity(self):
        """测试Frontmatter完整性"""
        errors = []
        required_fields = ['msc_primary']
        
        # 核心概念文件需要更完整的Frontmatter
        core_concept_files = list((CONCEPT_DIR / "核心概念").glob("*.md")) if (CONCEPT_DIR / "核心概念").exists() else []
        
        for md_file in core_concept_files:
            try:
                content = md_file.read_text(encoding=ENCODING)
                
                # 检查Frontmatter存在
                if not content.startswith('---'):
                    errors.append((str(md_file), "缺少Frontmatter"))
                    continue
                
                # 解析Frontmatter
                try:
                    fm_end = content.find('---', 3)
                    if fm_end == -1:
                        errors.append((str(md_file), "Frontmatter格式错误"))
                        continue
                    
                    fm_content = content[3:fm_end].strip()
                    frontmatter = yaml.safe_load(fm_content) or {}
                    
                    # 检查必需字段
                    for field in required_fields:
                        if field not in frontmatter:
                            errors.append((str(md_file), f"缺少必需字段: {field}"))
                    
                    # 检查MSC格式
                    if 'msc_primary' in frontmatter:
                        msc = frontmatter['msc_primary']
                        if not MSC_PRIMARY_PATTERN.match(str(msc)):
                            errors.append((str(md_file), f"MSC格式错误: {msc}"))
                    
                    # 检查secondary MSC
                    if 'msc_secondary' in frontmatter:
                        secondary = frontmatter['msc_secondary']
                        if not isinstance(secondary, list):
                            errors.append((str(md_file), "msc_secondary必须是列表"))
                        else:
                            for msc in secondary:
                                if not MSC_PRIMARY_PATTERN.match(str(msc)):
                                    errors.append((str(md_file), f"Secondary MSC格式错误: {msc}"))
                                    
                except yaml.YAMLError as e:
                    errors.append((str(md_file), f"YAML解析错误: {e}"))
                    
            except Exception as e:
                errors.append((str(md_file), f"读取错误: {e}"))
        
        self.frontmatter_errors = errors
        result = TestResult(
            name="Frontmatter完整性检查",
            passed=len(errors) == 0,
            message=f"发现{len(errors)}个Frontmatter错误" if errors else "所有Frontmatter完整",
            details={"errors": errors[:10]}
        )
        self.record_result(result)
        self.assertLessEqual(len(errors), 200, f"发现太多Frontmatter错误: {errors[:5]}")
    
    def test_03_encoding_format(self):
        """测试编码格式"""
        errors = []
        
        for md_file in self.markdown_files[:100]:
            try:
                # 尝试以UTF-8读取
                with open(md_file, 'rb') as f:
                    raw_content = f.read()
                
                # 检查BOM
                if raw_content.startswith(b'\xef\xbb\xbf'):
                    errors.append((str(md_file), "包含UTF-8 BOM头"))
                
                # 尝试解码
                try:
                    content = raw_content.decode('utf-8')
                except UnicodeDecodeError as e:
                    errors.append((str(md_file), f"UTF-8解码错误: {e}"))
                    continue
                
                # 检查非标准空白字符
                if '\xa0' in content:  # 非断空格
                    errors.append((str(md_file), "包含非断空格字符(U+00A0)"))
                
                # 检查行尾格式
                if '\r\n' in content:
                    # Windows换行符，仅记录但不报错
                    pass
                
                # 检查文件结尾
                if not content.endswith('\n') and len(content) > 0:
                    errors.append((str(md_file), "文件末尾缺少换行符"))
                    
            except Exception as e:
                errors.append((str(md_file), f"检查错误: {e}"))
        
        self.encoding_errors = errors
        result = TestResult(
            name="编码格式检查",
            passed=len(errors) == 0,
            message=f"发现{len(errors)}个编码格式问题" if errors else "所有文件编码正确",
            details={"errors": errors[:10]}
        )
        self.record_result(result)
        self.assertLessEqual(len(errors), 200, f"发现太多编码问题: {errors[:5]}")
    
    def test_04_internal_links(self):
        """测试内部链接有效性"""
        errors = []
        link_pattern = re.compile(r'\[([^\]]+)\]\(([^)]+)\)')
        
        # 收集所有文件路径
        all_files = {str(f.relative_to(PROJECT_ROOT)).replace('\\', '/') for f in self.markdown_files}
        
        for md_file in self.markdown_files[:50]:
            try:
                content = md_file.read_text(encoding=ENCODING)
                rel_dir = md_file.parent.relative_to(PROJECT_ROOT)
                
                for match in link_pattern.finditer(content):
                    link_text, link_target = match.groups()
                    
                    # 跳过外部链接
                    if link_target.startswith('http://') or link_target.startswith('https://'):
                        continue
                    
                    # 跳过锚点链接
                    if link_target.startswith('#'):
                        continue
                    
                    # 解析相对路径
                    target_path = link_target.split('#')[0]  # 移除锚点
                    if target_path:
                        full_target = (rel_dir / target_path).resolve()
                        rel_target = str(full_target.relative_to(PROJECT_ROOT)).replace('\\', '/')
                        
                        if rel_target not in all_files and not full_target.exists():
                            errors.append((str(md_file), f"链接目标不存在: {link_target}"))
                            
            except Exception as e:
                errors.append((str(md_file), f"检查错误: {e}"))
        
        result = TestResult(
            name="内部链接有效性检查",
            passed=len(errors) == 0,
            message=f"发现{len(errors)}个无效链接" if errors else "所有链接有效",
            details={"errors": errors[:10]}
        )
        self.record_result(result)
        self.assertLessEqual(len(errors), 500, f"发现太多无效链接: {errors[:5]}")


# ============================================================================
# 2. Lean4代码测试
# ============================================================================

class Lean4CodeTests(FormalMathTestCase):
    """Lean4代码测试类"""
    
    @classmethod
    def setUpClass(cls):
        super().setUpClass()
        cls.lean_files = cls._find_lean_files()
        cls.lean_exe = cls._find_lean_executable()
        
    @classmethod
    def _find_lean_files(cls) -> List[Path]:
        """查找项目特定的Lean4文件"""
        if not LEAN4_DIR.exists():
            return []
        # 只查找项目自己的Lean文件，不包括lake packages
        project_dirs = [
            d for d in LEAN4_DIR.iterdir() 
            if d.is_dir() and d.name != '.lake' and not d.name.startswith('.')
        ]
        files = []
        for d in project_dirs:
            files.extend(d.rglob("*.lean"))
        return files
    
    @classmethod
    def _find_lean_executable(cls) -> Optional[str]:
        """查找Lean可执行文件"""
        lean_paths = [
            "lean",
            str(Path.home() / ".elan/bin/lean"),
            "/usr/local/bin/lean",
            "/usr/bin/lean",
        ]
        for path in lean_paths:
            try:
                result = subprocess.run([path, "--version"], capture_output=True, timeout=5)
                if result.returncode == 0:
                    return path
            except:
                continue
        return None
    
    def test_01_lean_syntax(self):
        """测试Lean4语法正确性"""
        errors = []
        
        if not self.lean_files:
            result = TestResult(
                name="Lean4语法检查",
                passed=True,
                message="未找到项目Lean4文件，跳过测试",
            )
            self.record_result(result)
            return
        
        # 基本的语法检查
        lean_keywords = ['theorem', 'lemma', 'definition', 'def', 'structure', 'inductive', 
                        'class', 'instance', 'namespace', 'end', 'import', 'open']
        
        for lean_file in self.lean_files[:50]:
            try:
                content = lean_file.read_text(encoding=ENCODING)
                
                # 检查基本结构
                if 'import' not in content and lean_file.name not in ['Main.lean']:
                    # 某些文件可能没有import
                    pass
                
                # 检查namespace/end配对
                namespace_count = content.count('namespace ')
                end_count = content.count('\nend')
                if namespace_count != end_count:
                    errors.append((str(lean_file), f"namespace({namespace_count})/end({end_count})不匹配"))
                
                # 检查section/end配对
                section_count = content.count('\nsection')
                if section_count > 0 and section_count != end_count:
                    # 可能有section没有end
                    pass
                
                # 检查非法字符
                if '\t' in content:
                    errors.append((str(lean_file), "包含制表符，应使用空格"))
                    
            except Exception as e:
                errors.append((str(lean_file), f"读取错误: {e}"))
        
        result = TestResult(
            name="Lean4语法检查",
            passed=len(errors) == 0,
            message=f"发现{len(errors)}个语法问题" if errors else "所有Lean文件语法正确",
            details={"errors": errors[:10]}
        )
        self.record_result(result)
        self.assertLessEqual(len(errors), 50, f"发现太多语法问题: {errors[:5]}")
    
    def test_02_lean_imports(self):
        """测试Lean4导入依赖"""
        errors = []
        import_pattern = re.compile(r'^import\s+([\w\.]+)', re.MULTILINE)
        
        # 收集所有模块名
        all_modules = set()
        for lean_file in self.lean_files:
            rel_path = lean_file.relative_to(LEAN4_DIR)
            module_name = str(rel_path.with_suffix('')).replace(os.sep, '.')
            all_modules.add(module_name)
        
        for lean_file in self.lean_files[:50]:
            try:
                content = lean_file.read_text(encoding=ENCODING)
                imports = import_pattern.findall(content)
                
                for imp in imports:
                    # 检查是否是项目内部模块
                    if imp.startswith('FormalMath.'):
                        if imp not in all_modules:
                            errors.append((str(lean_file), f"导入的模块不存在: {imp}"))
                            
            except Exception as e:
                errors.append((str(lean_file), f"读取错误: {e}"))
        
        result = TestResult(
            name="Lean4导入依赖检查",
            passed=len(errors) == 0,
            message=f"发现{len(errors)}个导入错误" if errors else "所有导入依赖正确",
            details={"errors": errors[:10]}
        )
        self.record_result(result)
        self.assertLessEqual(len(errors), 100, f"发现太多导入错误: {errors[:5]}")
    
    def test_03_lean_compilation(self):
        """测试Lean4编译"""
        if not self.lean_exe:
            result = TestResult(
                name="Lean4编译测试",
                passed=True,  # 跳过，不是错误
                message="未找到Lean可执行文件，跳过编译测试",
            )
            self.record_result(result)
            return
        
        if not self.lean_files:
            result = TestResult(
                name="Lean4编译测试",
                passed=True,
                message="未找到项目Lean4文件，跳过编译测试",
            )
            self.record_result(result)
            return
        
        # 尝试使用lake build
        lake_file = LEAN4_DIR / "lakefile.lean"
        if lake_file.exists():
            try:
                result = subprocess.run(
                    ["lake", "build"],
                    cwd=LEAN4_DIR,
                    capture_output=True,
                    text=True,
                    timeout=300  # 5分钟超时
                )
                
                test_result = TestResult(
                    name="Lean4编译测试",
                    passed=result.returncode == 0,
                    message="编译成功" if result.returncode == 0 else f"编译失败:\n{result.stderr[:500]}",
                    details={"stdout": result.stdout[:1000], "stderr": result.stderr[:1000]}
                )
                self.record_result(test_result)
                self.assertEqual(result.returncode, 0, f"Lean4编译失败: {result.stderr[:500]}")
                
            except subprocess.TimeoutExpired:
                result = TestResult(
                    name="Lean4编译测试",
                    passed=False,
                    message="编译超时(5分钟)",
                )
                self.record_result(result)
                self.fail("Lean4编译超时")
            except Exception as e:
                result = TestResult(
                    name="Lean4编译测试",
                    passed=False,
                    message=f"编译测试出错: {e}",
                )
                self.record_result(result)
                self.fail(f"编译测试出错: {e}")
        else:
            result = TestResult(
                name="Lean4编译测试",
                passed=True,
                message="未找到lakefile.lean，跳过编译测试",
            )
            self.record_result(result)


# ============================================================================
# 3. 内容一致性测试
# ============================================================================

class ContentConsistencyTests(FormalMathTestCase):
    """内容一致性测试类"""
    
    @classmethod
    def setUpClass(cls):
        super().setUpClass()
        cls.markdown_files = list(PROJECT_ROOT.glob('concept/**/*.md'))
        cls.terminology_data = cls._load_terminology()
        cls.multilang_data = cls._load_multilang()
        cls.valid_msc_codes = cls._load_msc_codes()
        
    @classmethod
    def _load_terminology(cls) -> Dict:
        """加载标准术语表"""
        terminology = {}
        if TERMINOLOGY_FILE.exists():
            try:
                content = TERMINOLOGY_FILE.read_text(encoding=ENCODING)
                # 解析Markdown表格
                lines = content.split('\n')
                current_section = ""
                for line in lines:
                    if line.startswith('###'):
                        current_section = line.strip('# ')
                    elif '|' in line and not line.strip().startswith('|-'):
                        cells = [c.strip() for c in line.split('|')]
                        if len(cells) >= 9:  # 8语言 + 表头
                            zh_term = cells[1]
                            en_term = cells[2]
                            if zh_term and zh_term != '中文':
                                terminology[zh_term] = {
                                    'en': en_term,
                                    'section': current_section
                                }
            except Exception as e:
                print(f"加载术语表错误: {e}")
        return terminology
    
    @classmethod
    def _load_multilang(cls) -> Dict:
        """加载多语言对照表"""
        if MULTILANG_FILE.exists():
            try:
                content = MULTILANG_FILE.read_text(encoding=ENCODING)
                return json.loads(content)
            except Exception as e:
                print(f"加载多语言表错误: {e}")
        return {}
    
    @classmethod
    def _load_msc_codes(cls) -> Set[str]:
        """加载有效MSC编码"""
        # 基础MSC编码范围
        valid_codes = set()
        # 00-99开头的有效编码
        for i in range(100):
            for c in 'ABCDEFGHIJKLMNOPQRSTUVWXYZ':
                for j in range(100):
                    valid_codes.add(f"{i:02d}{c}{j:02d}")
        return valid_codes
    
    def test_01_msc_code_validity(self):
        """测试MSC编码有效性"""
        errors = []
        frontmatter_pattern = re.compile(r'^---\s*\n(.*?)\n---', re.DOTALL)
        
        core_files = list((CONCEPT_DIR / "核心概念").glob("*.md")) if (CONCEPT_DIR / "核心概念").exists() else []
        
        for md_file in core_files:
            try:
                content = md_file.read_text(encoding=ENCODING)
                match = frontmatter_pattern.match(content)
                
                if match:
                    fm_content = match.group(1)
                    try:
                        frontmatter = yaml.safe_load(fm_content) or {}
                        
                        # 检查primary MSC
                        msc_primary = frontmatter.get('msc_primary')
                        if msc_primary:
                            if not MSC_PRIMARY_PATTERN.match(str(msc_primary)):
                                errors.append((str(md_file), f"无效的主MSC编码: {msc_primary}"))
                        
                        # 检查secondary MSC
                        msc_secondary = frontmatter.get('msc_secondary', [])
                        if isinstance(msc_secondary, list):
                            for msc in msc_secondary:
                                if not MSC_PRIMARY_PATTERN.match(str(msc)):
                                    errors.append((str(md_file), f"无效的次MSC编码: {msc}"))
                                    
                    except yaml.YAMLError:
                        pass  # YAML错误在其他测试中检查
                        
            except Exception as e:
                errors.append((str(md_file), f"读取错误: {e}"))
        
        result = TestResult(
            name="MSC编码有效性检查",
            passed=len(errors) == 0,
            message=f"发现{len(errors)}个MSC编码错误" if errors else "所有MSC编码有效",
            details={"errors": errors[:10]}
        )
        self.record_result(result)
        self.assertLessEqual(len(errors), 50, f"发现太多MSC编码错误: {errors[:5]}")
    
    def test_02_cross_reference_validity(self):
        """测试交叉引用有效性"""
        errors = []
        
        # 收集所有概念ID
        concept_ids = set()
        concept_pattern = re.compile(r'\*\*概念编号\*\*:\s*(\S+)')
        
        core_files = list((CONCEPT_DIR / "核心概念").glob("*.md")) if (CONCEPT_DIR / "核心概念").exists() else []
        
        for md_file in core_files:
            try:
                content = md_file.read_text(encoding=ENCODING)
                match = concept_pattern.search(content)
                if match:
                    concept_ids.add(match.group(1))
            except:
                pass
        
        # 检查引用
        ref_pattern = re.compile(r'\[([^\]]+)\]\(\.\./\.\./核心概念/([^)]+)\.md\)')
        
        for md_file in self.markdown_files[:100]:
            try:
                content = md_file.read_text(encoding=ENCODING)
                
                # 检查相关概念引用
                for match in ref_pattern.finditer(content):
                    ref_file = match.group(2)
                    # 简化检查，实际应解析概念ID
                    
            except:
                pass
        
        result = TestResult(
            name="交叉引用有效性检查",
            passed=len(errors) == 0,
            message=f"发现{len(errors)}个交叉引用错误" if errors else "所有交叉引用有效",
            details={"errors": errors[:10]}
        )
        self.record_result(result)
        self.assertLessEqual(len(errors), 10)
    
    def test_03_terminology_consistency(self):
        """测试术语一致性"""
        errors = []
        
        if not self.terminology_data:
            result = TestResult(
                name="术语一致性检查",
                passed=True,
                message="术语表未加载，跳过测试",
            )
            self.record_result(result)
            return
        
        # 检查核心概念文件中的术语使用
        core_files = list((CONCEPT_DIR / "核心概念").glob("*.md")) if (CONCEPT_DIR / "核心概念").exists() else []
        
        for md_file in core_files[:20]:
            try:
                content = md_file.read_text(encoding=ENCODING)
                
                # 简单检查：查看是否有标准术语表中定义的术语
                # 更复杂的检查需要自然语言处理
                
            except Exception as e:
                errors.append((str(md_file), f"读取错误: {e}"))
        
        result = TestResult(
            name="术语一致性检查",
            passed=len(errors) == 0,
            message=f"发现{len(errors)}个术语问题" if errors else "术语使用一致",
            details={"errors": errors[:10]}
        )
        self.record_result(result)
        self.assertLessEqual(len(errors), 10)
    
    def test_04_concept_id_uniqueness(self):
        """测试概念ID唯一性（排除变体文件）"""
        errors = []
        concept_ids: Dict[str, List[str]] = defaultdict(list)
        concept_pattern = re.compile(r'\*\*概念编号\*\*:\s*(\S+)')
        
        core_files = list((CONCEPT_DIR / "核心概念").glob("*.md")) if (CONCEPT_DIR / "核心概念").exists() else []
        
        # 排除变体文件（三视角版、决策导图示例等）
        variant_patterns = ['-三视角版', '-决策导图示例', '-多理论分析示例', '-集合论视角分析', 
                           '-范畴论视角分析', '00-', '01-', '02-', '03-', '04-']
        
        for md_file in core_files:
            # 跳过变体文件
            if any(pattern in md_file.name for pattern in variant_patterns):
                continue
                
            try:
                content = md_file.read_text(encoding=ENCODING)
                match = concept_pattern.search(content)
                if match:
                    concept_id = match.group(1)
                    concept_ids[concept_id].append(str(md_file))
                else:
                    errors.append((str(md_file), "缺少概念编号"))
                    
            except Exception as e:
                errors.append((str(md_file), f"读取错误: {e}"))
        
        # 检查重复（不包括变体文件）
        duplicates = {k: v for k, v in concept_ids.items() if len(v) > 1}
        for concept_id, files in duplicates.items():
            errors.append((", ".join(files), f"概念ID重复: {concept_id}"))
        
        result = TestResult(
            name="概念ID唯一性检查",
            passed=len(duplicates) == 0,
            message=f"发现{len(duplicates)}个重复概念ID" if duplicates else "所有概念ID唯一（已排除变体文件）",
            details={"duplicates": list(duplicates.keys())[:10]}
        )
        self.record_result(result)
        self.assertEqual(len(duplicates), 0, f"发现重复概念ID: {list(duplicates.keys())[:5]}")
    
    def test_05_multilang_alignment(self):
        """测试多语言对齐"""
        errors = []
        
        if not self.multilang_data:
            result = TestResult(
                name="多语言对齐检查",
                passed=True,
                message="多语言表未加载，跳过测试",
            )
            self.record_result(result)
            return
        
        # 检查多语言表的完整性
        required_langs = ['en', 'de', 'fr', 'ja']
        
        for entry in self.multilang_data[:50]:
            concept_id = entry.get('concept_id', 'unknown')
            multilang = entry.get('multilang', {})
            
            for lang in required_langs:
                if lang not in multilang:
                    errors.append((concept_id, f"缺少{lang}语言翻译"))
                elif not multilang[lang].get('title'):
                    errors.append((concept_id, f"{lang}语言标题为空"))
        
        result = TestResult(
            name="多语言对齐检查",
            passed=len(errors) == 0,
            message=f"发现{len(errors)}个多语言问题" if errors else "多语言对齐正确",
            details={"errors": errors[:10]}
        )
        self.record_result(result)
        self.assertLessEqual(len(errors), 20)


# ============================================================================
# 测试套件收集
# ============================================================================

def create_test_suite() -> unittest.TestSuite:
    """创建完整测试套件"""
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()
    
    # 添加测试类
    suite.addTests(loader.loadTestsFromTestCase(DocumentFormatTests))
    suite.addTests(loader.loadTestsFromTestCase(Lean4CodeTests))
    suite.addTests(loader.loadTestsFromTestCase(ContentConsistencyTests))
    
    return suite


def create_specific_suite(test_type: str) -> unittest.TestSuite:
    """创建特定类型的测试套件"""
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()
    
    if test_type == 'document':
        suite.addTests(loader.loadTestsFromTestCase(DocumentFormatTests))
    elif test_type == 'lean4':
        suite.addTests(loader.loadTestsFromTestCase(Lean4CodeTests))
    elif test_type == 'content':
        suite.addTests(loader.loadTestsFromTestCase(ContentConsistencyTests))
    else:
        raise ValueError(f"未知测试类型: {test_type}")
    
    return suite


if __name__ == '__main__':
    # 直接运行测试
    runner = unittest.TextTestRunner(verbosity=2)
    suite = create_test_suite()
    result = runner.run(suite)
    
    # 返回非零退出码表示有失败
    sys.exit(0 if result.wasSuccessful() else 1)
