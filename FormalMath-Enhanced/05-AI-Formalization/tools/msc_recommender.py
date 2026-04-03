"""
MSC (Mathematics Subject Classification) 编码推荐器
基于数学文本自动推荐MSC2020编码
"""

import os
import re
import json
import logging
from typing import List, Dict, Any, Tuple, Optional
from dataclasses import dataclass
from collections import defaultdict
from pathlib import Path

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)


@dataclass
class MSCRecommendation:
    """MSC推荐结果"""
    code: str
    description: str
    confidence: float  # 0-1
    matched_keywords: List[str]
    parent_category: str


@dataclass
class MSCCode:
    """MSC编码信息"""
    code: str
    description: str
    level: int  # 1=一级, 2=二级, 3=三级
    parent: Optional[str] = None
    examples: List[str] = None
    
    def __post_init__(self):
        if self.examples is None:
            self.examples = []


class MSCRecommender:
    """
    MSC2020编码推荐器
    
    功能：
    - 输入数学文本
    - 自动推荐MSC2020编码
    - 基于关键词匹配
    """
    
    # MSC2020主要分类（一级编码）
    PRIMARY_CATEGORIES = {
        "00": "General and overarching topics; collections",
        "01": "History and biography",
        "03": "Mathematical logic and foundations",
        "05": "Combinatorics",
        "06": "Order, lattices, ordered algebraic structures",
        "08": "General algebraic systems",
        "11": "Number theory",
        "12": "Field theory and polynomials",
        "13": "Commutative algebra",
        "14": "Algebraic geometry",
        "15": "Linear and multilinear algebra; matrix theory",
        "16": "Associative rings and algebras",
        "17": "Nonassociative rings and algebras",
        "18": "Category theory; homological algebra",
        "19": "K-theory",
        "20": "Group theory and generalizations",
        "22": "Topological groups, Lie groups",
        "26": "Real functions",
        "28": "Measure and integration",
        "30": "Functions of a complex variable",
        "31": "Potential theory",
        "32": "Several complex variables and analytic spaces",
        "33": "Special functions",
        "34": "Ordinary differential equations",
        "35": "Partial differential equations",
        "37": "Dynamical systems and ergodic theory",
        "39": "Difference and functional equations",
        "40": "Sequences, series, summability",
        "41": "Approximations and expansions",
        "42": "Harmonic analysis on Euclidean spaces",
        "43": "Abstract harmonic analysis",
        "44": "Integral transforms, operational calculus",
        "45": "Integral equations",
        "46": "Functional analysis",
        "47": "Operator theory",
        "49": "Calculus of variations and optimal control",
        "51": "Geometry",
        "52": "Convex and discrete geometry",
        "53": "Differential geometry",
        "54": "General topology",
        "55": "Algebraic topology",
        "57": "Manifolds and cell complexes",
        "58": "Global analysis, analysis on manifolds",
        "60": "Probability theory and stochastic processes",
        "62": "Statistics",
        "65": "Numerical analysis",
        "68": "Computer science",
        "70": "Mechanics of particles and systems",
        "74": "Mechanics of deformable solids",
        "76": "Fluid mechanics",
        "78": "Optics, electromagnetic theory",
        "80": "Classical thermodynamics, heat transfer",
        "81": "Quantum theory",
        "82": "Statistical mechanics, structure of matter",
        "83": "Relativity and gravitational theory",
        "85": "Astronomy and astrophysics",
        "86": "Geophysics",
        "90": "Operations research, mathematical programming",
        "91": "Game theory, economics, social and behavioral sciences",
        "92": "Biology and other natural sciences",
        "93": "Systems theory; control",
        "94": "Information and communication theory, circuits",
        "97": "Mathematics education"
    }
    
    # 关键词到MSC编码的映射
    KEYWORD_MAPPINGS = {
        # 数论 (11-XX)
        "prime": ("11A41", "Primes", 0.9),
        "primes": ("11A41", "Primes", 0.9),
        "divisible": ("11A05", "Multiplicative structure; Euclidean algorithm", 0.85),
        "divisor": ("11A05", "Multiplicative structure; Euclidean algorithm", 0.85),
        "gcd": ("11A05", "Multiplicative structure; Euclidean algorithm", 0.9),
        "lcm": ("11A05", "Multiplicative structure; Euclidean algorithm", 0.9),
        "congruence": ("11A07", "Congruences; primitive roots; residue systems", 0.9),
        "modular": ("11A07", "Congruences; primitive roots; residue systems", 0.85),
        "modulo": ("11A07", "Congruences; primitive roots; residue systems", 0.85),
        "fermat": ("11A15", "Power residues, reciprocity", 0.9),
        "euler": ("11A25", "Arithmetic functions; related numbers; inversion formulas", 0.85),
        "diophantine": ("11Dxx", "Diophantine equations", 0.95),
        "pell": ("11D09", "Quadratic and bilinear equations", 0.9),
        "quadratic": ("11E04", "Quadratic forms over general fields", 0.8),
        "number theory": ("11-XX", "Number theory", 1.0),
        
        # 代数 (12-XX, 13-XX, 15-XX, 16-XX, 20-XX)
        "polynomial": ("12E05", "Polynomials (irreducibility, etc.)", 0.85),
        "field": ("12Fxx", "Field extensions", 0.8),
        "group": ("20-XX", "Group theory and generalizations", 0.9),
        "groups": ("20-XX", "Group theory and generalizations", 0.9),
        "abelian": ("20Kxx", "Abelian groups", 0.9),
        "cyclic": ("20K01", "Finite abelian groups", 0.85),
        "symmetric": ("20B30", "Symmetric groups", 0.85),
        "permutation": ("20Bxx", "Permutation groups", 0.85),
        "ring": ("16-XX", "Associative rings and algebras", 0.85),
        "rings": ("16-XX", "Associative rings and algebras", 0.85),
        "ideal": ("13A15", "Ideals and multiplicative ideal theory in commutative rings", 0.9),
        "matrix": ("15Axx", "Basic linear algebra", 0.85),
        "matrices": ("15Axx", "Basic linear algebra", 0.85),
        "determinant": ("15A15", "Determinants, permanents, traces, other special matrix functions", 0.9),
        "eigenvalue": ("15A18", "Eigenvalues, singular values, and eigenvectors", 0.9),
        "linear": ("15-XX", "Linear and multilinear algebra; matrix theory", 0.8),
        "vector space": ("15A03", "Vector spaces, linear dependence, rank, lineability", 0.85),
        "algebra": ("12-XX", "Field theory and polynomials", 0.75),
        
        # 组合数学 (05-XX)
        "combinatorics": ("05-XX", "Combinatorics", 1.0),
        "combinatorial": ("05-XX", "Combinatorics", 0.95),
        "graph": ("05Cxx", "Graph theory", 0.9),
        "graphs": ("05Cxx", "Graph theory", 0.9),
        "tree": ("05C05", "Trees", 0.9),
        "trees": ("05C05", "Trees", 0.9),
        "coloring": ("05C15", "Coloring of graphs and hypergraphs", 0.95),
        "colorings": ("05C15", "Coloring of graphs and hypergraphs", 0.95),
        "cycle": ("05C38", "Paths and cycles", 0.9),
        "cycles": ("05C38", "Paths and cycles", 0.9),
        "path": ("05C38", "Paths and cycles", 0.85),
        "permutation": ("05A05", "Permutations, words, matrices", 0.85),
        "combination": ("05A10", "Factorials, binomial coefficients, combinatorial functions", 0.85),
        "binomial": ("05A10", "Factorials, binomial coefficients, combinatorial functions", 0.9),
        "partition": ("05A17", "Combinatorial aspects of partitions of integers", 0.9),
        "partitions": ("05A17", "Combinatorial aspects of partitions of integers", 0.9),
        "counting": ("05Axx", "Enumerative combinatorics", 0.8),
        "enumeration": ("05Axx", "Enumerative combinatorics", 0.85),
        
        # 几何 (51-XX, 52-XX, 53-XX)
        "geometry": ("51-XX", "Geometry", 0.9),
        "geometric": ("51-XX", "Geometry", 0.85),
        "triangle": ("51M04", "Elementary problems in Euclidean geometries", 0.9),
        "triangles": ("51M04", "Elementary problems in Euclidean geometries", 0.9),
        "circle": ("51M04", "Elementary problems in Euclidean geometries", 0.9),
        "circles": ("51M04", "Elementary problems in Euclidean geometries", 0.9),
        "angle": ("51M04", "Elementary problems in Euclidean geometries", 0.85),
        "angles": ("51M04", "Elementary problems in Euclidean geometries", 0.85),
        "convex": ("52Axx", "General convexity", 0.9),
        "convexity": ("52Axx", "General convexity", 0.9),
        "polygon": ("52A10", "Convex sets in 2 dimensions", 0.9),
        "polygons": ("52A10", "Convex sets in 2 dimensions", 0.9),
        "polyhedron": ("52A15", "Convex sets in 3 dimensions", 0.9),
        "polyhedra": ("52A15", "Convex sets in 3 dimensions", 0.9),
        "differential geometry": ("53-XX", "Differential geometry", 0.95),
        "curvature": ("53A04", "Curves in Euclidean and related spaces", 0.9),
        "surface": ("53A05", "Surfaces in Euclidean and related spaces", 0.85),
        "surfaces": ("53A05", "Surfaces in Euclidean and related spaces", 0.85),
        
        # 分析 (26-XX, 30-XX, 34-XX, 35-XX, 40-XX)
        "real analysis": ("26-XX", "Real functions", 0.95),
        "continuous": ("26A15", "Continuity and related questions", 0.85),
        "differentiable": ("26A24", "Differentiation (functions of one variable)", 0.85),
        "integral": ("26A42", "Integrals of Riemann, Stieltjes and Lebesgue type", 0.85),
        "integration": ("26A42", "Integrals of Riemann, Stieltjes and Lebesgue type", 0.85),
        "complex": ("30-XX", "Functions of a complex variable", 0.8),
        "analytic": ("30-XX", "Functions of a complex variable", 0.75),
        "holomorphic": ("30Cxx", "Geometric function theory", 0.9),
        "differential equation": ("34-XX", "Ordinary differential equations", 0.9),
        "differential equations": ("34-XX", "Ordinary differential equations", 0.9),
        "ode": ("34-XX", "Ordinary differential equations", 0.95),
        "pde": ("35-XX", "Partial differential equations", 0.95),
        "partial differential": ("35-XX", "Partial differential equations", 0.95),
        "series": ("40-XX", "Sequences, series, summability", 0.8),
        "convergence": ("40A05", "Convergence and divergence of series and sequences", 0.85),
        "sequence": ("40A05", "Convergence and divergence of series and sequences", 0.8),
        "sequences": ("40A05", "Convergence and divergence of series and sequences", 0.8),
        
        # 拓扑 (54-XX, 55-XX, 57-XX)
        "topology": ("54-XX", "General topology", 0.95),
        "topological": ("54-XX", "General topology", 0.9),
        "compact": ("54D30", "Compactness", 0.9),
        "compactness": ("54D30", "Compactness", 0.9),
        "connected": ("54D05", "Connected and locally connected spaces", 0.9),
        "continuity": ("54C05", "Continuous maps", 0.85),
        "metric space": ("54E35", "Metric spaces, metrizability", 0.9),
        "metric spaces": ("54E35", "Metric spaces, metrizability", 0.9),
        "algebraic topology": ("55-XX", "Algebraic topology", 0.95),
        "homology": ("55Nxx", "Homology and cohomology theories", 0.95),
        "homotopy": ("55Pxx", "Homotopy theory", 0.95),
        "manifold": ("57-XX", "Manifolds and cell complexes", 0.9),
        "manifolds": ("57-XX", "Manifolds and cell complexes", 0.9),
        
        # 概率统计 (60-XX, 62-XX)
        "probability": ("60-XX", "Probability theory and stochastic processes", 0.95),
        "stochastic": ("60-XX", "Probability theory and stochastic processes", 0.9),
        "random": ("60Gxx", "Stochastic processes", 0.85),
        "distribution": ("60E05", "Distributions: general theory", 0.85),
        "expectation": ("60A99", "None of the above, but in this section", 0.9),
        "variance": ("60A99", "None of the above, but in this section", 0.9),
        "statistics": ("62-XX", "Statistics", 0.95),
        "statistical": ("62-XX", "Statistics", 0.9),
        "estimation": ("62Fxx", "Parametric inference", 0.85),
        "hypothesis testing": ("62F03", "Hypothesis testing", 0.95),
        "regression": ("62Jxx", "Linear inference, regression", 0.95),
        
        # 数值分析 (65-XX)
        "numerical": ("65-XX", "Numerical analysis", 0.9),
        "numerical analysis": ("65-XX", "Numerical analysis", 1.0),
        "approximation": ("65Dxx", "Numerical approximation and computational geometry", 0.9),
        "interpolation": ("65D05", "Interpolation", 0.95),
        "optimization": ("65Kxx", "Mathematical programming, optimization and variational techniques", 0.9),
        "linear system": ("65Fxx", "Numerical linear algebra", 0.9),
        "eigenvalue computation": ("65F15", "Eigenvalues, eigenvectors", 0.95),
        
        # 逻辑与基础 (03-XX)
        "logic": ("03-XX", "Mathematical logic and foundations", 0.9),
        "mathematical logic": ("03-XX", "Mathematical logic and foundations", 1.0),
        "set theory": ("03Exx", "Set theory", 0.95),
        "axiom": ("03E30", "Axiomatics of classical set theory and its fragments", 0.85),
        "axioms": ("03E30", "Axiomatics of classical set theory and its fragments", 0.85),
        "proof": ("03Fxx", "Proof theory and constructive mathematics", 0.85),
        "formal": ("03Bxx", "General logic", 0.8),
        "formalization": ("03B35", "Mechanization of proofs and logical operations", 0.9),
        "theorem proving": ("03B35", "Mechanization of proofs and logical operations", 0.95),
        
        # 计算机科学 (68-XX)
        "computer science": ("68-XX", "Computer science", 0.95),
        "algorithm": ("68Wxx", "Algorithms in computer science", 0.9),
        "algorithms": ("68Wxx", "Algorithms in computer science", 0.9),
        "complexity": ("68Qxx", "Theory of computing", 0.9),
        "computational": ("68Qxx", "Theory of computing", 0.85),
        "automata": ("68Q45", "Formal languages and automata", 0.95),
        "cryptography": ("94A60", "Cryptography", 0.95),
        
        # 数学教育 (97-XX)
        "education": ("97-XX", "Mathematics education", 0.85),
        "mathematics education": ("97-XX", "Mathematics education", 1.0),
        "olympiad": ("97U40", "Olympiads", 0.95),
        "competition": ("97U40", "Olympiads", 0.9)
    }
    
    def __init__(self, keyword_mappings: Optional[Dict[str, Tuple[str, str, float]]] = None):
        """
        初始化推荐器
        
        Args:
            keyword_mappings: 自定义关键词映射
        """
        self.mappings = keyword_mappings or self.KEYWORD_MAPPINGS
        self._build_index()
    
    def _build_index(self) -> None:
        """构建搜索索引"""
        self.code_index = defaultdict(list)
        
        for keyword, (code, desc, confidence) in self.mappings.items():
            self.code_index[code].append((keyword, confidence))
    
    def recommend(self, text: str, top_k: int = 5, 
                 min_confidence: float = 0.5) -> List[MSCRecommendation]:
        """
        为数学文本推荐MSC编码
        
        Args:
            text: 数学文本
            top_k: 返回的最大推荐数量
            min_confidence: 最小置信度阈值
            
        Returns:
            推荐列表
        """
        text_lower = text.lower()
        
        # 计算每个编码的得分
        code_scores = defaultdict(lambda: {"score": 0.0, "matches": []})
        
        for keyword, (code, desc, base_confidence) in self.mappings.items():
            # 检查关键词是否出现在文本中
            if self._keyword_matches(keyword, text_lower):
                # 根据匹配方式调整置信度
                confidence = self._calculate_confidence(keyword, text_lower, base_confidence)
                
                code_scores[code]["score"] += confidence
                code_scores[code]["matches"].append((keyword, confidence))
        
        # 构建推荐结果
        recommendations = []
        for code, data in code_scores.items():
            if data["score"] >= min_confidence:
                # 获取描述
                desc = self._get_code_description(code)
                
                # 获取父类别
                parent = self._get_parent_category(code)
                
                # 归一化置信度
                confidence = min(data["score"], 1.0)
                
                rec = MSCRecommendation(
                    code=code,
                    description=desc,
                    confidence=confidence,
                    matched_keywords=[k for k, _ in data["matches"]],
                    parent_category=parent
                )
                recommendations.append(rec)
        
        # 按置信度排序
        recommendations.sort(key=lambda x: x.confidence, reverse=True)
        
        return recommendations[:top_k]
    
    def _keyword_matches(self, keyword: str, text: str) -> bool:
        """检查关键词是否匹配"""
        # 精确匹配
        if keyword in text:
            return True
        
        # 词边界匹配
        pattern = r'\b' + re.escape(keyword) + r'\b'
        if re.search(pattern, text, re.IGNORECASE):
            return True
        
        return False
    
    def _calculate_confidence(self, keyword: str, text: str, base_confidence: float) -> float:
        """计算置信度"""
        confidence = base_confidence
        
        # 如果在标题中（假设前100个字符是标题），增加权重
        if keyword in text[:100]:
            confidence *= 1.2
        
        # 如果出现多次，增加权重
        count = text.count(keyword)
        if count > 1:
            confidence *= (1 + 0.1 * min(count - 1, 5))
        
        return min(confidence, 1.0)
    
    def _get_code_description(self, code: str) -> str:
        """获取编码描述"""
        # 从映射中获取
        for keyword, (c, desc, _) in self.mappings.items():
            if c == code:
                return desc
        
        # 从一级分类推断
        primary = code[:2]
        if primary in self.PRIMARY_CATEGORIES:
            return f"{self.PRIMARY_CATEGORIES[primary]} ({code})"
        
        return "Unknown"
    
    def _get_parent_category(self, code: str) -> str:
        """获取父类别"""
        primary = code[:2]
        return self.PRIMARY_CATEGORIES.get(primary, "Unknown")
    
    def get_primary_categories(self) -> Dict[str, str]:
        """获取所有一级分类"""
        return self.PRIMARY_CATEGORIES.copy()
    
    def get_codes_by_category(self, category_code: str) -> List[str]:
        """
        获取某类别下的所有编码
        
        Args:
            category_code: 类别代码（如"11"）
            
        Returns:
            编码列表
        """
        codes = []
        for keyword, (code, _, _) in self.mappings.items():
            if code.startswith(category_code):
                if code not in codes:
                    codes.append(code)
        
        return sorted(codes)
    
    def add_keyword_mapping(self, keyword: str, code: str, 
                          description: str, confidence: float) -> None:
        """
        添加新的关键词映射
        
        Args:
            keyword: 关键词
            code: MSC编码
            description: 描述
            confidence: 基础置信度
        """
        self.mappings[keyword] = (code, description, confidence)
        self._build_index()
        logger.info(f"Added mapping: {keyword} -> {code}")
    
    def batch_recommend(self, texts: List[str], top_k: int = 5) -> List[List[MSCRecommendation]]:
        """批量推荐"""
        return [self.recommend(text, top_k) for text in texts]
    
    def export_mappings(self, output_file: str) -> None:
        """导出映射到JSON文件"""
        data = {
            keyword: {
                "code": code,
                "description": desc,
                "confidence": conf
            }
            for keyword, (code, desc, conf) in self.mappings.items()
        }
        
        with open(output_file, 'w', encoding='utf-8') as f:
            json.dump(data, f, indent=2, ensure_ascii=False)
        
        logger.info(f"Exported mappings to {output_file}")
    
    def import_mappings(self, input_file: str) -> None:
        """从JSON文件导入映射"""
        with open(input_file, 'r', encoding='utf-8') as f:
            data = json.load(f)
        
        for keyword, info in data.items():
            self.mappings[keyword] = (
                info["code"],
                info["description"],
                info["confidence"]
            )
        
        self._build_index()
        logger.info(f"Imported {len(data)} mappings from {input_file}")


# 便捷函数
def recommend_msc(text: str, top_k: int = 5) -> List[Dict[str, Any]]:
    """
    快速推荐MSC编码
    
    Args:
        text: 数学文本
        top_k: 推荐数量
        
    Returns:
        推荐结果列表
    """
    recommender = MSCRecommender()
    recommendations = recommender.recommend(text, top_k)
    
    return [
        {
            "code": r.code,
            "description": r.description,
            "confidence": r.confidence,
            "parent": r.parent_category
        }
        for r in recommendations
    ]


def get_category_name(code: str) -> str:
    """
    获取类别名称
    
    Args:
        code: MSC编码或类别代码
        
    Returns:
        类别名称
    """
    recommender = MSCRecommender()
    primary = code[:2]
    return recommender.PRIMARY_CATEGORIES.get(primary, "Unknown")


if __name__ == "__main__":
    # 示例用法
    recommender = MSCRecommender()
    
    # 测试文本
    test_texts = [
        "Prove that for any prime number p, the congruence x^2 ≡ -1 (mod p) has a solution if and only if p = 2 or p ≡ 1 (mod 4).",
        "Find all functions f: R -> R such that f(x+y) = f(x) + f(y) for all real numbers x, y.",
        "Let G be a finite group of order n. Prove that if p is a prime dividing n, then G has an element of order p.",
        "Find the number of ways to color the vertices of a regular hexagon with 3 colors such that adjacent vertices have different colors."
    ]
    
    for text in test_texts:
        print("=" * 60)
        print(f"Text: {text[:80]}...")
        print("-" * 60)
        
        recommendations = recommender.recommend(text, top_k=3)
        for rec in recommendations:
            print(f"  {rec.code}: {rec.description}")
            print(f"    Confidence: {rec.confidence:.2f}")
            print(f"    Matched: {', '.join(rec.matched_keywords)}")
            print()
