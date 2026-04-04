"""
公式搜索服务
支持LaTeX公式匹配、结构相似度、变量无关匹配
"""
import re
import hashlib
from typing import List, Dict, Optional, Tuple, Any, Set
from dataclasses import dataclass
from collections import defaultdict

from .embedding import FormulaEmbedder


@dataclass
class FormulaMatchResult:
    """公式匹配结果"""
    formula_id: str
    formula_latex: str
    similarity: float
    match_type: str  # 'exact', 'structural', 'variable_independent'
    matched_vars: Dict[str, str]  # 变量映射
    rank: int


class FormulaNormalizer:
    """公式标准化器"""
    
    # 变量命名模式
    VAR_PATTERNS = [
        r'(?<![\\a-zA-Z])[a-z](?![a-zA-Z])',  # 单字母
        r'(?<![\\a-zA-Z])[A-Z](?![a-zA-Z])',  # 单字母大写
        r'_[a-zA-Z0-9]',  # 下标
        r'\^[a-zA-Z0-9]',  # 上标
    ]
    
    # 结构关键字
    STRUCTURE_KEYWORDS = {
        'fraction': ['\\frac', '/'],
        'sum': ['\\sum', '\\Sigma'],
        'product': ['\\prod', '\\Pi'],
        'integral': ['\\int', '\\oint'],
        'limit': ['\\lim', '\\limit'],
        'sqrt': ['\\sqrt', '\\root'],
        'power': ['^', '**'],
        'subscript': ['_'],
        'matrix': ['\\matrix', '\\pmatrix', '\\bmatrix'],
        'cases': ['\\cases', '\\begin{cases}'],
    }
    
    def normalize(self, latex: str) -> str:
        """标准化LaTeX公式"""
        normalized = latex.strip()
        
        # 移除多余空格
        normalized = re.sub(r'\s+', ' ', normalized)
        
        # 标准化括号
        normalized = re.sub(r'\\left\(', '(', normalized)
        normalized = re.sub(r'\\right\)', ')', normalized)
        normalized = re.sub(r'\\left\[', '[', normalized)
        normalized = re.sub(r'\\right\]', ']', normalized)
        normalized = re.sub(r'\\\{', '{', normalized)
        normalized = re.sub(r'\\\}', '}', normalized)
        
        # 标准化空格命令
        normalized = re.sub(r'\\,|\\;|\\:|\\!', ' ', normalized)
        
        # 标准化分数
        normalized = re.sub(r'\\frac\s*\{', '\\frac{', normalized)
        
        return normalized
    
    def extract_variables(self, latex: str) -> Set[str]:
        """提取公式中的变量"""
        variables = set()
        
        # 单字母变量（排除LaTeX命令）
        vars_found = re.findall(r'(?<![\\a-zA-Z])[a-zA-Z](?![a-zA-Z])', latex)
        variables.update(vars_found)
        
        # 带下标的变量
        subscript_vars = re.findall(r'([a-zA-Z])_\{?([a-zA-Z0-9]+)\}?', latex)
        for base, sub in subscript_vars:
            variables.add(f"{base}_{sub}")
        
        return variables
    
    def replace_variables(self, latex: str, var_mapping: Dict[str, str]) -> str:
        """替换公式中的变量"""
        result = latex
        
        # 按长度降序排序，避免短变量名替换时影响长变量名
        sorted_vars = sorted(var_mapping.keys(), key=len, reverse=True)
        
        for old_var in sorted_vars:
            new_var = var_mapping[old_var]
            # 使用正则确保只替换完整变量
            pattern = r'(?<![a-zA-Z0-9_])' + re.escape(old_var) + r'(?![a-zA-Z0-9_])'
            result = re.sub(pattern, new_var, result)
        
        return result
    
    def to_variable_independent(self, latex: str) -> str:
        """转换为变量无关形式（用于结构匹配）"""
        normalized = self.normalize(latex)
        variables = sorted(self.extract_variables(normalized))
        
        # 替换变量为通用占位符
        var_mapping = {var: f'VAR_{i}' for i, var in enumerate(variables)}
        return self.replace_variables(normalized, var_mapping)


class FormulaStructureIndex:
    """公式结构索引"""
    
    def __init__(self):
        self.formulas: Dict[str, Dict] = {}  # id -> formula info
        self.structure_index: Dict[str, Set[str]] = defaultdict(set)  # structure hash -> ids
        self.operator_index: Dict[str, Set[str]] = defaultdict(set)  # operator -> ids
        self.normalizer = FormulaNormalizer()
        self.embedder = FormulaEmbedder()
    
    def add_formula(self, formula_id: str, latex: str, metadata: Dict = None):
        """添加公式到索引"""
        normalized = self.normalizer.normalize(latex)
        var_independent = self.normalizer.to_variable_independent(normalized)
        structure = self.embedder.extract_structure(normalized)
        
        self.formulas[formula_id] = {
            'id': formula_id,
            'latex': latex,
            'normalized': normalized,
            'var_independent': var_independent,
            'structure': structure,
            'metadata': metadata or {},
            'variables': self.normalizer.extract_variables(normalized)
        }
        
        # 添加到结构索引
        struct_hash = hashlib.md5(var_independent.encode()).hexdigest()[:16]
        self.structure_index[struct_hash].add(formula_id)
        
        # 添加到操作符索引
        for op in structure['operators']:
            self.operator_index[op].add(formula_id)
        for func in structure['functions']:
            self.operator_index[func].add(formula_id)
    
    def search_by_structure(self, latex: str, k: int = 10) -> List[FormulaMatchResult]:
        """基于结构的相似搜索"""
        normalized = self.normalizer.normalize(latex)
        var_independent = self.normalizer.to_variable_independent(normalized)
        query_structure = self.embedder.extract_structure(normalized)
        query_vars = self.normalizer.extract_variables(normalized)
        
        candidates = set()
        
        # 从结构索引获取候选
        struct_hash = hashlib.md5(var_independent.encode()).hexdigest()[:16]
        candidates.update(self.structure_index.get(struct_hash, set()))
        
        # 从操作符索引获取候选
        for op in query_structure['operators']:
            candidates.update(self.operator_index.get(op, set()))
        for func in query_structure['functions']:
            candidates.update(self.operator_index.get(func, set()))
        
        # 计算相似度
        results = []
        for formula_id in candidates:
            formula = self.formulas[formula_id]
            
            # 结构相似度
            struct_sim = self.embedder.structural_similarity(
                normalized, 
                formula['normalized']
            )
            
            # 计算变量映射
            var_mapping = self._compute_variable_mapping(
                query_vars,
                formula['variables'],
                normalized,
                formula['normalized']
            )
            
            # 确定匹配类型
            if struct_sim > 0.95:
                match_type = 'exact'
            elif struct_sim > 0.8:
                match_type = 'structural'
            else:
                match_type = 'variable_independent'
            
            results.append(FormulaMatchResult(
                formula_id=formula_id,
                formula_latex=formula['latex'],
                similarity=struct_sim,
                match_type=match_type,
                matched_vars=var_mapping,
                rank=0
            ))
        
        # 排序
        results.sort(key=lambda x: x.similarity, reverse=True)
        
        # 更新排名
        for i, result in enumerate(results[:k], 1):
            result.rank = i
        
        return results[:k]
    
    def _compute_variable_mapping(
        self,
        query_vars: Set[str],
        target_vars: Set[str],
        query_latex: str,
        target_latex: str
    ) -> Dict[str, str]:
        """计算变量映射（使用启发式方法）"""
        mapping = {}
        
        # 简单的贪心映射
        query_list = sorted(query_vars)
        target_list = sorted(target_vars)
        
        # 按顺序映射
        for i, qv in enumerate(query_list):
            if i < len(target_list):
                mapping[qv] = target_list[i]
        
        return mapping
    
    def get_formula(self, formula_id: str) -> Optional[Dict]:
        """获取公式信息"""
        return self.formulas.get(formula_id)
    
    def get_formulas_by_operator(self, operator: str) -> List[Dict]:
        """获取使用特定操作符的所有公式"""
        formula_ids = self.operator_index.get(operator, set())
        return [self.formulas[fid] for fid in formula_ids]


class LaTeXPatternMatcher:
    """LaTeX模式匹配器"""
    
    def __init__(self):
        self.patterns: Dict[str, re.Pattern] = {}
    
    def compile_pattern(self, pattern_name: str, pattern: str):
        """编译正则模式"""
        self.patterns[pattern_name] = re.compile(pattern, re.DOTALL)
    
    def match(self, latex: str, pattern_name: str) -> Optional[re.Match]:
        """匹配模式"""
        if pattern_name not in self.patterns:
            return None
        return self.patterns[pattern_name].match(latex)
    
    def search(self, latex: str, pattern_name: str) -> Optional[re.Match]:
        """搜索模式"""
        if pattern_name not in self.patterns:
            return None
        return self.patterns[pattern_name].search(latex)
    
    def findall(self, latex: str, pattern_name: str) -> List[str]:
        """查找所有匹配"""
        if pattern_name not in self.patterns:
            return []
        return self.patterns[pattern_name].findall(latex)


class FormulaSearchService:
    """公式搜索服务"""
    
    def __init__(self):
        self.structure_index = FormulaStructureIndex()
        self.pattern_matcher = LaTeXPatternMatcher()
        self.normalizer = FormulaNormalizer()
        self.embedder = FormulaEmbedder()
        
        # 初始化常用模式
        self._init_patterns()
    
    def _init_patterns(self):
        """初始化常用LaTeX模式"""
        patterns = {
            'fraction': r'\\frac\{([^}]+)\}\{([^}]+)\}',
            'sum': r'\\sum_\{([^}]+)\}\^\{([^}]+)\}',
            'integral': r'\\int_\{([^}]+)\}\^\{([^}]+)\}',
            'limit': r'\\lim_\{([^}]+)\}',
            'sqrt': r'\\sqrt(?:\[([^\]]+)\])?\{([^}]+)\}',
            'power': r'([^{}\s]+)\^\{([^}]+)\}',
            'subscript': r'([^{}\s]+)_\{([^}]+)\}',
            'matrix': r'\\begin\{(pmatrix|bmatrix|vmatrix|matrix)\}(.*?)\\end\{\1\}',
            'function': r'\\(sin|cos|tan|log|ln|exp|max|min|sup|inf|lim)\b',
        }
        
        for name, pattern in patterns.items():
            self.pattern_matcher.compile_pattern(name, pattern)
    
    def index_formula(
        self,
        formula_id: str,
        latex: str,
        metadata: Dict = None
    ):
        """索引公式"""
        self.structure_index.add_formula(formula_id, latex, metadata)
    
    def search(
        self,
        query: str,
        k: int = 10,
        match_type: str = 'all'  # 'all', 'exact', 'structural', 'variable_independent'
    ) -> List[FormulaMatchResult]:
        """
        搜索公式
        
        Args:
            query: LaTeX查询公式
            k: 返回结果数量
            match_type: 匹配类型过滤
        """
        results = self.structure_index.search_by_structure(query, k=k*2)
        
        # 过滤匹配类型
        if match_type != 'all':
            results = [r for r in results if r.match_type == match_type]
        
        return results[:k]
    
    def search_similar_by_example(
        self,
        example_latex: str,
        k: int = 10
    ) -> List[FormulaMatchResult]:
        """
        基于示例公式搜索相似公式
        """
        return self.search(example_latex, k=k)
    
    def search_by_pattern(
        self,
        pattern_name: str,
        k: int = 10
    ) -> List[Dict]:
        """
        搜索包含特定模式的公式
        """
        matching_formulas = []
        
        for formula_id, formula in self.structure_index.formulas.items():
            matches = self.pattern_matcher.findall(formula['latex'], pattern_name)
            if matches:
                formula_copy = formula.copy()
                formula_copy['matches'] = matches
                matching_formulas.append(formula_copy)
        
        return matching_formulas[:k]
    
    def compare_formulas(
        self,
        latex1: str,
        latex2: str
    ) -> Dict[str, any]:
        """
        比较两个公式的相似度
        """
        # 标准化
        norm1 = self.normalizer.normalize(latex1)
        norm2 = self.normalizer.normalize(latex2)
        
        # 结构相似度
        struct_sim = self.embedder.structural_similarity(norm1, norm2)
        
        # 变量无关相似度
        var_ind1 = self.normalizer.to_variable_independent(norm1)
        var_ind2 = self.normalizer.to_variable_independent(norm2)
        var_ind_sim = 1.0 if var_ind1 == var_ind2 else 0.0
        
        # 提取变量
        vars1 = self.normalizer.extract_variables(norm1)
        vars2 = self.normalizer.extract_variables(norm2)
        
        return {
            'structural_similarity': struct_sim,
            'variable_independent_match': var_ind_sim,
            'variables_1': list(vars1),
            'variables_2': list(vars2),
            'common_variables': list(vars1 & vars2),
            'is_equivalent': struct_sim > 0.95,
            'is_structurally_similar': struct_sim > 0.8
        }
    
    def extract_formula_from_text(self, text: str) -> List[Dict]:
        """
        从文本中提取LaTeX公式
        """
        formulas = []
        
        # 匹配$...$ 和 $$...$$
        inline_pattern = r'\$([^$]+)\$'
        display_pattern = r'\$\$([^$]+)\$\$'
        
        for match in re.finditer(inline_pattern, text):
            formulas.append({
                'type': 'inline',
                'content': match.group(1),
                'full_match': match.group(0),
                'start': match.start(),
                'end': match.end()
            })
        
        for match in re.finditer(display_pattern, text):
            formulas.append({
                'type': 'display',
                'content': match.group(1),
                'full_match': match.group(0),
                'start': match.start(),
                'end': match.end()
            })
        
        # 匹配\begin{equation}等环境
        env_pattern = r'\\begin\{(equation|align|align\*|gather|gather\*)\}(.*?)\\end\{\1\}'
        for match in re.finditer(env_pattern, text, re.DOTALL):
            formulas.append({
                'type': match.group(1),
                'content': match.group(2),
                'full_match': match.group(0),
                'start': match.start(),
                'end': match.end()
            })
        
        return formulas
    
    def get_formula_stats(self, formula_id: str) -> Optional[Dict]:
        """获取公式统计信息"""
        formula = self.structure_index.get_formula(formula_id)
        if not formula:
            return None
        
        structure = formula['structure']
        
        return {
            'formula_id': formula_id,
            'variable_count': len(formula['variables']),
            'operator_count': len(structure['operators']),
            'function_count': len(structure['functions']),
            'nesting_depth': structure['depth'],
            'operators': structure['operators'],
            'functions': structure['functions']
        }


# 全局公式搜索服务实例
_formula_search_service: Optional[FormulaSearchService] = None


def get_formula_search_service() -> FormulaSearchService:
    """获取全局公式搜索服务实例"""
    global _formula_search_service
    if _formula_search_service is None:
        _formula_search_service = FormulaSearchService()
    return _formula_search_service
