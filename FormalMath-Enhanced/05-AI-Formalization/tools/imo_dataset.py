"""
IMO题目数据集处理器
用于读取、解析和处理IMO竞赛题目
"""

import os
import re
import json
import logging
from typing import List, Dict, Any, Optional, Tuple
from dataclasses import dataclass, field, asdict
from pathlib import Path
from collections import defaultdict

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)


@dataclass
class IMOProblem:
    """IMO题目数据结构"""
    year: int
    problem_number: int
    title: str = ""
    statement: str = ""
    informal_proof: str = ""
    formal_proof_lean: str = ""
    concepts: List[str] = field(default_factory=list)
    keywords: List[str] = field(default_factory=list)
    difficulty: str = "unknown"  # easy, medium, hard, unknown
    category: str = "unknown"    # algebra, geometry, number_theory, combinatorics
    msc_codes: List[str] = field(default_factory=list)
    source_file: str = ""
    metadata: Dict[str, Any] = field(default_factory=dict)
    
    def to_dict(self) -> Dict[str, Any]:
        """转换为字典"""
        return asdict(self)
    
    def to_json(self, indent: int = 2) -> str:
        """转换为JSON字符串"""
        return json.dumps(self.to_dict(), indent=indent, ensure_ascii=False)
    
    @property
    def unique_id(self) -> str:
        """生成唯一标识符"""
        return f"IMO_{self.year}_{self.problem_number:02d}"


@dataclass
class DatasetConfig:
    """数据集配置"""
    base_path: str
    output_path: str = "./imo_dataset"
    min_year: int = 1959
    max_year: int = 2024
    include_proofs: bool = True
    include_concepts: bool = True


class IMODatasetProcessor:
    """
    IMO题目数据集处理器
    
    功能：
    - 读取IMO题目（从03-IMO-Competition/）
    - 提取数学概念和关键词
    - 生成训练数据集
    """
    
    # 数学领域关键词映射
    CONCEPT_PATTERNS = {
        "algebra": [
            r'\bequation\b', r'\bpolynomial\b', r'\bfunction\b', r'\binequality\b',
            r'\balgebraic\b', r'\bvariable\b', r'\bcoefficient\b', r'\broots\b',
            r'方程', r'多项式', r'函数', r'不等式', r'代数'
        ],
        "geometry": [
            r'\btriangle\b', r'\bcircle\b', r'\bangle\b', r'\bpoint\b', r'\bline\b',
            r'\bplane\b', r'\bconvex\b', r'\bpolygon\b', r'\bperpendicular\b',
            r'三角形', r'圆', r'角度', r'几何', r'平面', r'垂直'
        ],
        "number_theory": [
            r'\bprime\b', r'\bdivisor\b', r'\bdivisible\b', r'\binteger\b',
            r'\bmodular\b', r'\bcongruence\b', r'\bgcd\b', r'\blcm\b',
            r'质数', r'整除', r'约数', r'同余', r'数论', r'整数'
        ],
        "combinatorics": [
            r'\bcombinatorics\b', r'\bpermutation\b', r'\bcombination\b',
            r'\bgraph\b', r'\bcoloring\b', r'\bcounting\b', r'\barrangement\b',
            r'组合', r'排列', r'图论', r'染色', r'计数'
        ]
    }
    
    # MSC2020分类映射
    MSC_MAPPING = {
        "algebra": ["12-XX", "13-XX", "15-XX", "26-XX", "39-XX"],
        "geometry": ["51-XX", "52-XX", "53-XX"],
        "number_theory": ["11-XX"],
        "combinatorics": ["05-XX"]
    }
    
    def __init__(self, config: Optional[DatasetConfig] = None):
        """
        初始化处理器
        
        Args:
            config: 数据集配置
        """
        if config is None:
            # 默认配置，假设在项目根目录
            base_path = os.getenv("IMO_DATA_PATH", "../../03-IMO-Competition")
            config = DatasetConfig(base_path=base_path)
        
        self.config = config
        self.problems: List[IMOProblem] = []
    
    def _find_problem_files(self) -> List[Path]:
        """查找所有题目文件"""
        base_path = Path(self.config.base_path)
        
        if not base_path.exists():
            logger.error(f"Base path not found: {base_path}")
            return []
        
        problem_files = []
        
        # 查找年份目录
        for year_dir in base_path.iterdir():
            if year_dir.is_dir() and year_dir.name.isdigit():
                year = int(year_dir.name)
                if self.config.min_year <= year <= self.config.max_year:
                    # 查找题目文件
                    for problem_file in year_dir.glob("Problem-*.md"):
                        problem_files.append(problem_file)
        
        logger.info(f"Found {len(problem_files)} problem files")
        return sorted(problem_files)
    
    def _parse_problem_file(self, file_path: Path) -> Optional[IMOProblem]:
        """
        解析单个题目文件
        
        Args:
            file_path: 文件路径
            
        Returns:
            IMOProblem对象或None
        """
        try:
            content = file_path.read_text(encoding='utf-8')
            
            # 解析年份和题号
            match = re.search(r'(\d{4})[/\\]Problem-(\d{2})', str(file_path))
            if match:
                year = int(match.group(1))
                problem_num = int(match.group(2))
            else:
                # 尝试从文件名解析
                match = re.search(r'Problem-(\d{2})', file_path.name)
                if match:
                    problem_num = int(match.group(1))
                    year = int(file_path.parent.name) if file_path.parent.name.isdigit() else 0
                else:
                    return None
            
            # 解析标题
            title_match = re.search(r'^#\s*(.+)$', content, re.MULTILINE)
            title = title_match.group(1).strip() if title_match else f"Problem {problem_num}"
            
            # 解析题目陈述
            statement = self._extract_statement(content)
            
            # 解析证明（如果有）
            informal_proof = ""
            if self.config.include_proofs:
                informal_proof = self._extract_proof(content)
            
            # 提取概念和关键词
            concepts, keywords = self._extract_concepts(statement)
            
            # 确定类别
            category = self._determine_category(concepts, statement)
            
            # 生成MSC代码
            msc_codes = self.MSC_MAPPING.get(category, [])
            
            # 确定难度（如果有标记）
            difficulty = self._extract_difficulty(content)
            
            problem = IMOProblem(
                year=year,
                problem_number=problem_num,
                title=title,
                statement=statement,
                informal_proof=informal_proof,
                concepts=concepts,
                keywords=keywords,
                difficulty=difficulty,
                category=category,
                msc_codes=msc_codes,
                source_file=str(file_path),
                metadata={
                    "file_size": len(content),
                    "parse_time": logger.info("Parsing %s", file_path.name) or ""
                }
            )
            
            return problem
            
        except Exception as e:
            logger.error(f"Failed to parse {file_path}: {e}")
            return None
    
    def _extract_statement(self, content: str) -> str:
        """提取题目陈述"""
        # 尝试找到题目部分
        patterns = [
            r'##?\s*题目[:：]?\s*\n(.*?)(?=##?\s*(证明|解答|Proof|Solution)|\Z)',
            r'##?\s*Problem[:：]?\s*\n(.*?)(?=##?\s*(Proof|Solution)|\Z)',
            r'##?\s*Statement[:：]?\s*\n(.*?)(?=##?|\Z)'
        ]
        
        for pattern in patterns:
            match = re.search(pattern, content, re.DOTALL | re.IGNORECASE)
            if match:
                return match.group(1).strip()
        
        # 如果没有找到特定标记，返回前1000个字符
        return content[:1000].strip()
    
    def _extract_proof(self, content: str) -> str:
        """提取证明"""
        patterns = [
            r'##?\s*证明[:：]?\s*\n(.*?)(?=##?|\Z)',
            r'##?\s*Proof[:：]?\s*\n(.*?)(?=##?|\Z)',
            r'##?\s*解答[:：]?\s*\n(.*?)(?=##?|\Z)',
            r'##?\s*Solution[:：]?\s*\n(.*?)(?=##?|\Z)'
        ]
        
        for pattern in patterns:
            match = re.search(pattern, content, re.DOTALL | re.IGNORECASE)
            if match:
                return match.group(1).strip()
        
        return ""
    
    def _extract_concepts(self, text: str) -> Tuple[List[str], List[str]]:
        """
        提取数学概念和关键词
        
        Returns:
            (概念列表, 关键词列表)
        """
        concepts = []
        keywords = []
        
        text_lower = text.lower()
        
        # 基于模式匹配概念
        for category, patterns in self.CONCEPT_PATTERNS.items():
            for pattern in patterns:
                if re.search(pattern, text, re.IGNORECASE):
                    concept = pattern.replace(r'\b', '').replace('\\', '')
                    if concept not in concepts:
                        concepts.append(concept)
        
        # 提取通用数学关键词
        math_terms = re.findall(r'\b\w+(?: theorem| lemma| corollary| property)\b', text_lower)
        keywords.extend(list(set(math_terms)))
        
        # 提取数学符号
        symbols = re.findall(r'[∈∉∪∩⊂⊃⊆⊇∅∞∑∏∫√∂∆∇∀∃⇒⇔]', text)
        keywords.extend([f"symbol:{s}" for s in set(symbols)])
        
        return concepts, list(set(keywords))
    
    def _determine_category(self, concepts: List[str], text: str) -> str:
        """确定题目类别"""
        category_scores = defaultdict(int)
        text_lower = text.lower()
        
        for category, patterns in self.CONCEPT_PATTERNS.items():
            for pattern in patterns:
                if re.search(pattern, text, re.IGNORECASE):
                    category_scores[category] += 1
        
        if category_scores:
            return max(category_scores, key=category_scores.get)
        
        return "unknown"
    
    def _extract_difficulty(self, content: str) -> str:
        """提取难度信息"""
        patterns = [
            r'难度[:：]?\s*(\w+)',
            r'Difficulty[:：]?\s*(\w+)',
            r'\[(Easy|Medium|Hard|困难|中等|简单)\]'
        ]
        
        for pattern in patterns:
            match = re.search(pattern, content, re.IGNORECASE)
            if match:
                return match.group(1).lower()
        
        return "unknown"
    
    def load_problems(self) -> List[IMOProblem]:
        """
        加载所有题目
        
        Returns:
            题目列表
        """
        problem_files = self._find_problem_files()
        
        self.problems = []
        for file_path in problem_files:
            problem = self._parse_problem_file(file_path)
            if problem:
                self.problems.append(problem)
        
        logger.info(f"Loaded {len(self.problems)} problems")
        return self.problems
    
    def export_to_json(self, output_file: Optional[str] = None) -> str:
        """
        导出为JSON格式
        
        Args:
            output_file: 输出文件路径
            
        Returns:
            JSON字符串
        """
        if not self.problems:
            self.load_problems()
        
        data = {
            "metadata": {
                "total_problems": len(self.problems),
                "year_range": f"{self.config.min_year}-{self.config.max_year}",
                "categories": {}
            },
            "problems": [p.to_dict() for p in self.problems]
        }
        
        # 统计类别
        category_counts = defaultdict(int)
        for p in self.problems:
            category_counts[p.category] += 1
        data["metadata"]["categories"] = dict(category_counts)
        
        json_str = json.dumps(data, indent=2, ensure_ascii=False)
        
        if output_file:
            output_path = Path(self.config.output_path) / output_file
            output_path.parent.mkdir(parents=True, exist_ok=True)
            output_path.write_text(json_str, encoding='utf-8')
            logger.info(f"Exported to {output_path}")
        
        return json_str
    
    def export_training_data(self, output_file: str = "training_data.jsonl") -> str:
        """
        导出训练数据集（JSONL格式）
        
        格式：每行一个JSON对象，包含input/output
        """
        if not self.problems:
            self.load_problems()
        
        output_path = Path(self.config.output_path) / output_file
        output_path.parent.mkdir(parents=True, exist_ok=True)
        
        with open(output_path, 'w', encoding='utf-8') as f:
            for p in self.problems:
                # 自然语言到形式化的训练对
                training_example = {
                    "id": p.unique_id,
                    "instruction": "Convert the following mathematical problem to Lean 4:",
                    "input": p.statement,
                    "output": p.formal_proof_lean if p.formal_proof_lean else "# Formal proof pending",
                    "metadata": {
                        "category": p.category,
                        "concepts": p.concepts,
                        "difficulty": p.difficulty
                    }
                }
                f.write(json.dumps(training_example, ensure_ascii=False) + '\n')
        
        logger.info(f"Exported training data to {output_path}")
        return str(output_path)
    
    def get_problems_by_category(self, category: str) -> List[IMOProblem]:
        """按类别获取题目"""
        return [p for p in self.problems if p.category == category]
    
    def get_problems_by_year(self, year: int) -> List[IMOProblem]:
        """按年份获取题目"""
        return [p for p in self.problems if p.year == year]
    
    def get_problems_by_concept(self, concept: str) -> List[IMOProblem]:
        """按概念获取题目"""
        return [p for p in self.problems if concept in p.concepts]
    
    def generate_statistics(self) -> Dict[str, Any]:
        """生成统计信息"""
        if not self.problems:
            self.load_problems()
        
        stats = {
            "total_problems": len(self.problems),
            "by_year": defaultdict(int),
            "by_category": defaultdict(int),
            "by_difficulty": defaultdict(int),
            "concepts": defaultdict(int)
        }
        
        for p in self.problems:
            stats["by_year"][p.year] += 1
            stats["by_category"][p.category] += 1
            stats["by_difficulty"][p.difficulty] += 1
            for c in p.concepts:
                stats["concepts"][c] += 1
        
        # 转换为普通dict以便JSON序列化
        return {
            k: dict(v) if isinstance(v, defaultdict) else v
            for k, v in stats.items()
        }
    
    def search_problems(self, query: str) -> List[IMOProblem]:
        """
        搜索题目
        
        Args:
            query: 搜索关键词
            
        Returns:
            匹配的题目列表
        """
        if not self.problems:
            self.load_problems()
        
        query_lower = query.lower()
        results = []
        
        for p in self.problems:
            if (query_lower in p.statement.lower() or
                query_lower in p.title.lower() or
                any(query_lower in c.lower() for c in p.concepts) or
                any(query_lower in k.lower() for k in p.keywords)):
                results.append(p)
        
        return results


# 便捷函数
def load_imo_problems(base_path: str = "../../03-IMO-Competition") -> List[IMOProblem]:
    """
    快速加载IMO题目
    
    Args:
        base_path: 基础路径
        
    Returns:
        题目列表
    """
    config = DatasetConfig(base_path=base_path)
    processor = IMODatasetProcessor(config)
    return processor.load_problems()


def export_imo_dataset(output_path: str = "./imo_dataset") -> str:
    """
    导出IMO数据集
    
    Args:
        output_path: 输出路径
        
    Returns:
        输出文件路径
    """
    config = DatasetConfig(
        base_path="../../03-IMO-Competition",
        output_path=output_path
    )
    processor = IMODatasetProcessor(config)
    processor.load_problems()
    
    json_path = processor.export_to_json("imo_problems.json")
    training_path = processor.export_training_data("training_data.jsonl")
    
    # 导出统计信息
    stats = processor.generate_statistics()
    stats_path = Path(output_path) / "statistics.json"
    stats_path.write_text(json.dumps(stats, indent=2, ensure_ascii=False), encoding='utf-8')
    
    return output_path


if __name__ == "__main__":
    # 示例用法
    processor = IMODatasetProcessor()
    problems = processor.load_problems()
    
    print(f"Loaded {len(problems)} problems")
    
    if problems:
        print("\nExample problem:")
        print(problems[0].to_json())
    
    # 导出数据
    processor.export_to_json("imo_problems.json")
    processor.export_training_data("training_data.jsonl")
    
    # 打印统计
    stats = processor.generate_statistics()
    print("\nStatistics:")
    print(json.dumps(stats, indent=2, ensure_ascii=False))
