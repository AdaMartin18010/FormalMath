"""
公式搜索服务 - 优化版本
- 改进的变量映射算法
- 更快的结构匹配
- 缓存机制
"""
import re
import hashlib
from typing import List, Dict, Optional, Tuple, Any, Set
from dataclasses import dataclass
from collections import defaultdict
from functools import lru_cache
import numpy as np

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
    """公式标准化器 - 优化版本"""
    
    # 扩展的变量命名模式
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
    
    def __init__(self):
        self._cache = {}
    
    def normalize(self, latex: str) -> str:
        """标准化LaTeX公式 - 带缓存"""
        cache_key = hash(latex)
        if cache_key in self._cache:
            return self._cache[cache_key]
        
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
        
        # 移除多余的空格
        normalized = normalized.strip()
        
        self._cache[cache_key] = normalized
        return normalized
    
    def extract_variables(self, latex: str) -> Set[str]:
        """提取公式中的变量 - 优化版本"""
        variables = set()
        
        # 单字母变量（排除LaTeX命令）
        vars_found = re.findall(r'(?<![\\a-zA-Z])[a-zA-Z](?![a-zA-Z])', latex)
        variables.update(vars_found)
        
        # 带下标的变量
        subscript_vars = re.findall(r'([a-zA-Z])_\{?([a-zA-Z0-9]+)\}?', latex)
        for base, sub in subscript_vars:
            variables.add(f"{base}_{sub}")
        
        # 希腊字母
        greek_pattern = r'\\(alpha|beta|gamma|delta|epsilon|zeta|eta|theta|iota|kappa|lambda|mu|nu|xi|pi|rho|sigma|tau|upsilon|phi|chi|psi|omega)'
        greek_vars = re.findall(greek_pattern, latex, re.IGNORECASE)
        variables.update(f"\\{g}" for g in greek_vars)
        
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
    
    def get_structure_signature(self, latex: str) -> str:
        """获取结构签名（用于快速比较）"""
        var_indep = self.to_variable_independent(latex)
        # 移除所有VAR_标记，只保留结构
        return re.sub(r'VAR_\d+', 'VAR', var_indep)


class VariableMappingSolver:
    """
    变量映射求解器 - 使用编辑距离和约束求解
    """
    
    def __init__(self):
        self.max_combinations = 1000  # 限制组合数量
    
    def solve_mapping(
        self,
        query_vars: Set[str],
        target_vars: Set[str],
        query_latex: str,
        target_latex: str
    ) -> Tuple[Dict[str, str], float]:
        """
        求解最优变量映射
        
        Returns:
            (映射字典, 匹配分数)
        """
        if not query_vars or not target_vars:
            return {}, 0.0
        
        # 如果数量相同，尝试直接对应
        if len(query_vars) == len(target_vars):
            # 按字母顺序排序后一一对应
            mapping = dict(zip(sorted(query_vars), sorted(target_vars)))
            score = self._evaluate_mapping(mapping, query_latex, target_latex)
            return mapping, score
        
        # 变量数量不同，使用启发式匹配
        return self._heuristic_match(query_vars, target_vars, query_latex, target_latex)
    
    def _heuristic_match(
        self,
        query_vars: Set[str],
        target_vars: Set[str],
        query_latex: str,
        target_latex: str
    ) -> Tuple[Dict[str, str], float]:
        """启发式变量匹配"""
        query_list = sorted(query_vars)
        target_list = sorted(target_vars)
        
        # 基于变量位置信息进行匹配
        mapping = {}
        
        # 提取变量位置
        query_positions = self._extract_variable_positions(query_latex, query_vars)
        target_positions = self._extract_variable_positions(target_latex, target_vars)
        
        # 基于相对位置进行匹配
        for q_var in query_list:
            if q_var in query_positions:
                q_pos = query_positions[q_var]
                # 找到位置最接近的目标变量
                best_match = None
                best_score = float('inf')
                
                for t_var in target_list:
                    if t_var in target_positions:
                        t_pos = target_positions[t_var]
                        # 计算相对位置差异
                        score = abs(q_pos - t_pos)
                        if score < best_score:
                            best_score = score
                            best_match = t_var
                
                if best_match and best_match not in mapping.values():
                    mapping[q_var] = best_match
        
        # 为未匹配的变量分配剩余变量
        remaining_query = [v for v in query_list if v not in mapping]
        remaining_target = [v for v in target_list if v not in mapping.values()]
        
        for i, q_var in enumerate(remaining_query):
            if i < len(remaining_target):
                mapping[q_var] = remaining_target[i]
        
        score = self._evaluate_mapping(mapping, query_latex, target_latex)
        return mapping, score
    
    def _extract_variable_positions(self, latex: str, variables: Set[str]) -> Dict[str, float]:
        """提取变量在公式中的相对位置"""
        positions = {}
        latex_len = len(latex)
        
        for var in variables:
            # 找到变量首次出现的位置
            idx = latex.find(var)
            if idx >= 0:
                positions[var] = idx / latex_len  # 归一化位置
        
        return positions
    
    def _evaluate_mapping(
        self,
        mapping: Dict[str, str],
        query_latex: str,
        target_latex: str
    ) -> float:
        """评估映射质量"""
        if not mapping:
            return 0.0
        
        # 应用映射并比较
        normalizer = FormulaNormalizer()
        mapped_query = normalizer.replace_variables(query_latex, mapping)
        
        # 计算编辑距离相似度
        distance = self._levenshtein_distance(mapped_query, target_latex)
        max_len = max(len(mapped_query), len(target_latex))
        
        if max_len == 0:
            return 1.0
        
        return 1.0 - (distance / max_len)
    
    def _levenshtein_distance(self, s1: str, s2: str) -> int:
        """计算编辑距离"""
        if len(s1) < len(s2):
            return self._levenshtein_distance(s2, s1)
        
        if len(s2) == 0:
            return len(s1)
        
        previous_row = range(len(s2) + 1)
        for i, c1 in enumerate(s1):
            current_row = [i + 1]
            for j, c2 in enumerate(s2):
                insertions = previous_row[j + 1] + 1
                deletions = current_row[j] + 1
                substitutions = previous_row[j] + (c1 != c2)
                current_row.append(min(insertions, deletions, substitutions))
            previous_row = current_row
        
        return previous_row[-1]


class FormulaStructureIndex:
    """公式结构索引 - 优化版本"""
    
    def __init__(self):
        self.formulas: Dict[str, Dict] = {}
        self.structure_index: Dict[str, Set[str]] = defaultdict(set)
        self.operator_index: Dict[str, Set[str]] = defaultdict(set)
        self.signature_index: Dict[str, Set[str]] = defaultdict(set)  # 新增：结构签名索引
        self.normalizer = FormulaNormalizer()
        self.embedder = FormulaEmbedder()
        self.mapping_solver = VariableMappingSolver()
    
    def add_formula(self, formula_id: str, latex: str, metadata: Dict = None):
        """添加公式到索引"""
        normalized = self.normalizer.normalize(latex)
        var_independent = self.normalizer.to_variable_independent(normalized)
        structure = self.embedder.extract_structure(normalized)
        signature = self.normalizer.get_structure_signature(latex)
        
        self.formulas[formula_id] = {
            'id': formula_id,
            'latex': latex,
            'normalized': normalized,
            'var_independent': var_independent,
            'signature': signature,
            'structure': structure,
            'metadata': metadata or {},
            'variables': self.normalizer.extract_variables(normalized)
        }
        
        # 添加到结构索引
        struct_hash = hashlib.md5(var_independent.encode()).hexdigest()[:16]
        self.structure_index[struct_hash].add(formula_id)
        
        # 添加到签名索引
        sig_hash = hashlib.md5(signature.encode()).hexdigest()[:16]
        self.signature_index[sig_hash].add(formula_id)
        
        # 添加到操作符索引
        for op in structure['operators']:
            self.operator_index[op].add(formula_id)
        for func in structure['functions']:
            self.operator_index[func].add(formula_id)
    
    def search_by_structure(self, latex: str, k: int = 10) -> List[FormulaMatchResult]:
        """基于结构的相似搜索 - 优化版本"""
        normalized = self.normalizer.normalize(latex)
        var_independent = self.normalizer.to_variable_independent(normalized)
        signature = self.normalizer.get_structure_signature(latex)
        query_structure = self.embedder.extract_structure(normalized)
        query_vars = self.normalizer.extract_variables(normalized)
        
        candidates = set()
        
        # 从签名索引获取候选（快速过滤）
        sig_hash = hashlib.md5(signature.encode()).hexdigest()[:16]
        candidates.update(self.signature_index.get(sig_hash, set()))
        
        # 从结构索引获取候选
        struct_hash = hashlib.md5(var_independent.encode()).hexdigest()[:16]
        candidates.update(self.structure_index.get(struct_hash, set()))
        
        # 从操作符索引获取候选（限制数量）
        for op in list(query_structure['operators'])[:3]:  # 限制操作符数量
            candidates.update(self.operator_index.get(op, set()))
        for func in list(query_structure['functions'])[:2]:
            candidates.update(self.operator_index.get(func, set()))
        
        # 计算相似度（并行处理候选）
        results = []
        for formula_id in candidates:
            formula = self.formulas[formula_id]
            
            # 结构相似度
            struct_sim = self.embedder.structural_similarity(
                normalized,
                formula['normalized']
            )
            
            # 签名相似度（快速检查）
            signature_sim = 1.0 if formula['signature'] == signature else 0.0
            
            # 综合相似度
            combined_sim = 0.6 * struct_sim + 0.4 * signature_sim
            
            # 计算变量映射
            var_mapping, mapping_score = self.mapping_solver.solve_mapping(
                query_vars,
                formula['variables'],
                normalized,
                formula['normalized']
            )
            
            # 融合映射分数
            final_sim = 0.8 * combined_sim + 0.2 * mapping_score
            
            # 确定匹配类型
            if final_sim > 0.95:
                match_type = 'exact'
            elif final_sim > 0.8:
                match_type = 'structural'
            else:
                match_type = 'variable_independent'
            
            results.append(FormulaMatchResult(
                formula_id=formula_id,
                formula_latex=formula['latex'],
                similarity=final_sim,
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


class FormulaSearchServiceOptimized:
    """
    公式搜索服务 - 优化版本
    
    改进点：
    1. 改进的变量映射算法
    2. 结构签名索引加速
    3. 缓存机制
    4. 批处理支持
    """
    
    def __init__(self):
        self.structure_index = FormulaStructureIndex()
        self.normalizer = FormulaNormalizer()
        self.embedder = FormulaEmbedder()
        self.mapping_solver = VariableMappingSolver()
        self._search_cache = {}
        self._cache_size = 100
    
    def index_formula(
        self,
        formula_id: str,
        latex: str,
        metadata: Dict = None
    ):
        """索引公式"""
        self.structure_index.add_formula(formula_id, latex, metadata)
    
    @lru_cache(maxsize=128)
    def search(
        self,
        query: str,
        k: int = 10,
        match_type: str = 'all'
    ) -> List[FormulaMatchResult]:
        """
        搜索公式 - 带缓存
        
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
    
    def batch_search(
        self,
        queries: List[str],
        k: int = 10
    ) -> List[List[FormulaMatchResult]]:
        """批量搜索"""
        return [self.search(q, k=k) for q in queries]
    
    def compare_formulas(
        self,
        latex1: str,
        latex2: str
    ) -> Dict[str, any]:
        """比较两个公式的相似度 - 优化版本"""
        # 标准化
        norm1 = self.normalizer.normalize(latex1)
        norm2 = self.normalizer.normalize(latex2)
        
        # 结构相似度
        struct_sim = self.embedder.structural_similarity(norm1, norm2)
        
        # 变量无关相似度
        var_ind1 = self.normalizer.to_variable_independent(norm1)
        var_ind2 = self.normalizer.to_variable_independent(norm2)
        var_ind_sim = 1.0 if var_ind1 == var_ind2 else self._jaccard_similarity(var_ind1, var_ind2)
        
        # 签名相似度
        sig1 = self.normalizer.get_structure_signature(latex1)
        sig2 = self.normalizer.get_structure_signature(latex2)
        sig_sim = 1.0 if sig1 == sig2 else 0.0
        
        # 提取变量并计算映射
        vars1 = self.normalizer.extract_variables(norm1)
        vars2 = self.normalizer.extract_variables(norm2)
        mapping, mapping_score = self.mapping_solver.solve_mapping(
            vars1, vars2, norm1, norm2
        )
        
        return {
            'structural_similarity': struct_sim,
            'variable_independent_similarity': var_ind_sim,
            'signature_match': sig_sim,
            'mapping_score': mapping_score,
            'variables_1': list(vars1),
            'variables_2': list(vars2),
            'common_variables': list(vars1 & vars2),
            'variable_mapping': mapping,
            'is_equivalent': struct_sim > 0.95 and sig_sim == 1.0,
            'is_structurally_similar': struct_sim > 0.8,
            'overall_similarity': 0.4 * struct_sim + 0.3 * var_ind_sim + 0.2 * sig_sim + 0.1 * mapping_score
        }
    
    def _jaccard_similarity(self, s1: str, s2: str) -> float:
        """计算Jaccard相似度"""
        set1 = set(s1)
        set2 = set(s2)
        intersection = len(set1 & set2)
        union = len(set1 | set2)
        return intersection / union if union > 0 else 0.0


# 全局实例
_formula_search_service_optimized: Optional[FormulaSearchServiceOptimized] = None


def get_formula_search_service_optimized() -> FormulaSearchServiceOptimized:
    """获取优化的公式搜索服务实例"""
    global _formula_search_service_optimized
    if _formula_search_service_optimized is None:
        _formula_search_service_optimized = FormulaSearchServiceOptimized()
    return _formula_search_service_optimized
