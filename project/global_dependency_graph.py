#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
FormalMath 全局依赖图与拓扑排序系统
=====================================

基于概念前置关系，构建100个节点的有向图，并实现拓扑排序算法。

作者: FormalMath Team
创建日期: 2026年4月4日
版本: 1.0.0

主要功能:
1. 构建有向图 - 基于数学概念的前置依赖关系
2. 拓扑排序算法 - Kahn算法实现带层次信息的排序
3. 学习路径生成器 - 个性化学习路径推荐
4. 可视化输出 - Mermaid图表生成

依赖:
- networkx: 图论算法库
- matplotlib: 可视化（可选）
- collections: 数据结构
"""

import json
from collections import defaultdict, deque
from typing import List, Dict, Set, Tuple, Optional, Any
from dataclasses import dataclass, field
from enum import Enum
import os


# ============================================================================
# 数据模型定义
# ============================================================================

class KnowledgeLevel(Enum):
    """知识层次枚举"""
    L0 = 0  # 基础层：直观理解、基本定义、简单例子
    L1 = 1  # 中级层：严格定义、基本定理、证明思路
    L2 = 2  # 高级层：深入定理、应用、前沿内容
    L3 = 3  # 研究层：开放问题、研究方向


class KnowledgeDomain(Enum):
    """知识领域枚举"""
    FOUNDATION = "基础数学"      # D1
    ALGEBRA = "代数"             # D2
    ANALYSIS = "分析"            # D3
    GEOMETRY = "几何"            # D4
    TOPOLOGY = "拓扑"            # D5
    NUMBER_THEORY = "数论"       # D6
    DISCRETE = "离散数学"        # D7
    INTERDISCIPLINARY = "交叉领域" # D8


class DifficultyLevel(Enum):
    """难度等级枚举"""
    BEGINNER = 1      # 初级
    ELEMENTARY = 2    # 入门
    INTERMEDIATE = 3  # 中级
    ADVANCED = 4      # 高级
    EXPERT = 5        # 专家


@dataclass
class Concept:
    """
    数学概念数据类
    
    Attributes:
        id: 概念唯一标识符
        name: 概念名称（中文）
        name_en: 概念名称（英文）
        level: 知识层次
        domain: 知识领域
        difficulty: 难度等级
        msc_code: MSC分类编码
        prerequisites: 前置概念ID列表
        description: 概念描述
        estimated_hours: 预计学习时长（小时）
    """
    id: str
    name: str
    name_en: str
    level: KnowledgeLevel
    domain: KnowledgeDomain
    difficulty: DifficultyLevel
    msc_code: str
    prerequisites: List[str] = field(default_factory=list)
    description: str = ""
    estimated_hours: float = 1.0
    
    def to_dict(self) -> Dict[str, Any]:
        """转换为字典格式"""
        return {
            'id': self.id,
            'name': self.name,
            'name_en': self.name_en,
            'level': self.level.name,
            'domain': self.domain.value,
            'difficulty': self.difficulty.value,
            'msc_code': self.msc_code,
            'prerequisites': self.prerequisites,
            'description': self.description,
            'estimated_hours': self.estimated_hours
        }


# ============================================================================
# 核心概念数据 - 100个节点
# ============================================================================

def get_core_concepts() -> List[Concept]:
    """
    获取100个核心数学概念数据
    
    基于FormalMath项目的33个核心概念扩展至100个节点，
    涵盖8大知识领域，4个知识层次。
    
    Returns:
        List[Concept]: 概念列表
    """
    concepts = []
    
    # ==================== D1: 基础数学 (15个概念) ====================
    foundation_concepts = [
        Concept("C001", "关系", "Relation", KnowledgeLevel.L0, 
                KnowledgeDomain.FOUNDATION, DifficultyLevel.BEGINNER, "04A05",
                [], "数学对象之间的基本联系", 2.0),
        Concept("C002", "集合", "Set", KnowledgeLevel.L0, 
                KnowledgeDomain.FOUNDATION, DifficultyLevel.BEGINNER, "03Exx",
                ["C001"], "数学对象的汇集", 3.0),
        Concept("C003", "函数", "Function", KnowledgeLevel.L0, 
                KnowledgeDomain.FOUNDATION, DifficultyLevel.BEGINNER, "26A09",
                ["C002"], "集合间的映射关系", 4.0),
        Concept("C004", "自然数", "Natural Number", KnowledgeLevel.L0, 
                KnowledgeDomain.FOUNDATION, DifficultyLevel.BEGINNER, "11A99",
                ["C002"], "计数的数学对象", 3.0),
        Concept("C005", "整数", "Integer", KnowledgeLevel.L0, 
                KnowledgeDomain.FOUNDATION, DifficultyLevel.BEGINNER, "11A99",
                ["C004"], "包含正负的自然数扩展", 2.0),
        Concept("C006", "有理数", "Rational Number", KnowledgeLevel.L0, 
                KnowledgeDomain.FOUNDATION, DifficultyLevel.ELEMENTARY, "11A99",
                ["C005"], "整数之比构成的数", 3.0),
        Concept("C007", "实数", "Real Number", KnowledgeLevel.L1, 
                KnowledgeDomain.FOUNDATION, DifficultyLevel.ELEMENTARY, "26A03",
                ["C006"], "完备的有理数扩张", 5.0),
        Concept("C008", "复数", "Complex Number", KnowledgeLevel.L1, 
                KnowledgeDomain.FOUNDATION, DifficultyLevel.ELEMENTARY, "30A99",
                ["C007"], "实数的代数闭包扩张", 4.0),
        Concept("C009", "逻辑", "Logic", KnowledgeLevel.L0, 
                KnowledgeDomain.FOUNDATION, DifficultyLevel.BEGINNER, "03B99",
                [], "数学推理的基础", 4.0),
        Concept("C010", "命题", "Proposition", KnowledgeLevel.L0, 
                KnowledgeDomain.FOUNDATION, DifficultyLevel.BEGINNER, "03B05",
                ["C009"], "可判断真假的陈述", 2.0),
        Concept("C011", "谓词", "Predicate", KnowledgeLevel.L0, 
                KnowledgeDomain.FOUNDATION, DifficultyLevel.ELEMENTARY, "03B10",
                ["C010"], "含变量的命题形式", 3.0),
        Concept("C012", "量词", "Quantifier", KnowledgeLevel.L0, 
                KnowledgeDomain.FOUNDATION, DifficultyLevel.ELEMENTARY, "03B10",
                ["C011"], "全称量词与存在量词", 2.0),
        Concept("C013", "等价关系", "Equivalence Relation", KnowledgeLevel.L1, 
                KnowledgeDomain.FOUNDATION, DifficultyLevel.ELEMENTARY, "04A05",
                ["C001", "C002"], "自反、对称、传递的关系", 3.0),
        Concept("C014", "序关系", "Order Relation", KnowledgeLevel.L1, 
                KnowledgeDomain.FOUNDATION, DifficultyLevel.ELEMENTARY, "06A05",
                ["C001", "C002"], "偏序与全序关系", 3.0),
        Concept("C015", "笛卡尔积", "Cartesian Product", KnowledgeLevel.L0, 
                KnowledgeDomain.FOUNDATION, DifficultyLevel.ELEMENTARY, "03E20",
                ["C002"], "集合的乘积构造", 2.0),
    ]
    concepts.extend(foundation_concepts)
    
    # ==================== D2: 代数 (15个概念) ====================
    algebra_concepts = [
        Concept("C016", "二元运算", "Binary Operation", KnowledgeLevel.L0, 
                KnowledgeDomain.ALGEBRA, DifficultyLevel.ELEMENTARY, "08A99",
                ["C002", "C003"], "集合上的二元函数", 3.0),
        Concept("C017", "群", "Group", KnowledgeLevel.L1, 
                KnowledgeDomain.ALGEBRA, DifficultyLevel.INTERMEDIATE, "20A05",
                ["C016", "C013"], "具有逆元的结合运算结构", 8.0),
        Concept("C018", "子群", "Subgroup", KnowledgeLevel.L1, 
                KnowledgeDomain.ALGEBRA, DifficultyLevel.INTERMEDIATE, "20A05",
                ["C017"], "群的子结构", 4.0),
        Concept("C019", "正规子群", "Normal Subgroup", KnowledgeLevel.L1, 
                KnowledgeDomain.ALGEBRA, DifficultyLevel.INTERMEDIATE, "20A05",
                ["C018"], "满足共轭封闭的子群", 5.0),
        Concept("C020", "商群", "Quotient Group", KnowledgeLevel.L2, 
                KnowledgeDomain.ALGEBRA, DifficultyLevel.ADVANCED, "20A05",
                ["C019", "C013"], "群模去正规子群", 6.0),
        Concept("C021", "群同态", "Group Homomorphism", KnowledgeLevel.L1, 
                KnowledgeDomain.ALGEBRA, DifficultyLevel.INTERMEDIATE, "20A99",
                ["C017", "C003"], "保持群结构的映射", 5.0),
        Concept("C022", "群同构", "Group Isomorphism", KnowledgeLevel.L1, 
                KnowledgeDomain.ALGEBRA, DifficultyLevel.INTERMEDIATE, "20A99",
                ["C021"], "双射的群同态", 3.0),
        Concept("C023", "环", "Ring", KnowledgeLevel.L1, 
                KnowledgeDomain.ALGEBRA, DifficultyLevel.INTERMEDIATE, "13A99",
                ["C017"], "具有加法和乘法的代数结构", 6.0),
        Concept("C024", "域", "Field", KnowledgeLevel.L1, 
                KnowledgeDomain.ALGEBRA, DifficultyLevel.INTERMEDIATE, "12E99",
                ["C023"], "非零元可逆的交换环", 5.0),
        Concept("C025", "向量空间", "Vector Space", KnowledgeLevel.L1, 
                KnowledgeDomain.ALGEBRA, DifficultyLevel.INTERMEDIATE, "15A03",
                ["C024", "C017"], "域上的模结构", 8.0),
        Concept("C026", "线性映射", "Linear Map", KnowledgeLevel.L1, 
                KnowledgeDomain.ALGEBRA, DifficultyLevel.INTERMEDIATE, "15A04",
                ["C025", "C003"], "保持线性结构的映射", 6.0),
        Concept("C027", "矩阵", "Matrix", KnowledgeLevel.L1, 
                KnowledgeDomain.ALGEBRA, DifficultyLevel.INTERMEDIATE, "15A99",
                ["C025", "C026"], "线性映射的表示", 8.0),
        Concept("C028", "行列式", "Determinant", KnowledgeLevel.L1, 
                KnowledgeDomain.ALGEBRA, DifficultyLevel.INTERMEDIATE, "15A15",
                ["C027"], "方阵的多重线性函数", 6.0),
        Concept("C029", "特征值", "Eigenvalue", KnowledgeLevel.L2, 
                KnowledgeDomain.ALGEBRA, DifficultyLevel.ADVANCED, "15A18",
                ["C027", "C028"], "线性算子的不变量", 7.0),
        Concept("C030", "模", "Module", KnowledgeLevel.L2, 
                KnowledgeDomain.ALGEBRA, DifficultyLevel.ADVANCED, "13C99",
                ["C023", "C025"], "环上的向量空间推广", 8.0),
    ]
    concepts.extend(algebra_concepts)
    
    # ==================== D3: 分析 (15个概念) ====================
    analysis_concepts = [
        Concept("C031", "序列", "Sequence", KnowledgeLevel.L0, 
                KnowledgeDomain.ANALYSIS, DifficultyLevel.ELEMENTARY, "40A99",
                ["C004", "C003"], "自然数集上的函数", 3.0),
        Concept("C032", "极限", "Limit", KnowledgeLevel.L1, 
                KnowledgeDomain.ANALYSIS, DifficultyLevel.INTERMEDIATE, "26A03",
                ["C031", "C007"], "序列或函数的趋近行为", 8.0),
        Concept("C033", "连续性", "Continuity", KnowledgeLevel.L1, 
                KnowledgeDomain.ANALYSIS, DifficultyLevel.INTERMEDIATE, "26A15",
                ["C032", "C003"], "映射的局部稳定性", 6.0),
        Concept("C034", "导数", "Derivative", KnowledgeLevel.L1, 
                KnowledgeDomain.ANALYSIS, DifficultyLevel.INTERMEDIATE, "26A24",
                ["C032"], "函数的瞬时变化率", 8.0),
        Concept("C035", "微分", "Differential", KnowledgeLevel.L1, 
                KnowledgeDomain.ANALYSIS, DifficultyLevel.INTERMEDIATE, "26A24",
                ["C034"], "函数的局部线性近似", 5.0),
        Concept("C036", "积分", "Integral", KnowledgeLevel.L1, 
                KnowledgeDomain.ANALYSIS, DifficultyLevel.INTERMEDIATE, "26A42",
                ["C034"], "函数的累积效应", 10.0),
        Concept("C037", "微积分基本定理", "Fundamental Theorem of Calculus", KnowledgeLevel.L2, 
                KnowledgeDomain.ANALYSIS, DifficultyLevel.ADVANCED, "26A42",
                ["C034", "C036"], "微分与积分的互逆关系", 5.0),
        Concept("C038", "级数", "Series", KnowledgeLevel.L1, 
                KnowledgeDomain.ANALYSIS, DifficultyLevel.INTERMEDIATE, "40A05",
                ["C031", "C032"], "无穷序列的和", 7.0),
        Concept("C039", "幂级数", "Power Series", KnowledgeLevel.L2, 
                KnowledgeDomain.ANALYSIS, DifficultyLevel.ADVANCED, "30B10",
                ["C038", "C008"], "以幂函数为基的级数", 6.0),
        Concept("C040", "一致收敛", "Uniform Convergence", KnowledgeLevel.L2, 
                KnowledgeDomain.ANALYSIS, DifficultyLevel.ADVANCED, "40A30",
                ["C032", "C033"], "函数序列的全局收敛性", 8.0),
        Concept("C041", "度量空间", "Metric Space", KnowledgeLevel.L1, 
                KnowledgeDomain.ANALYSIS, DifficultyLevel.INTERMEDIATE, "54E35",
                ["C007", "C032"], "具有距离函数的空间", 6.0),
        Concept("C042", "完备性", "Completeness", KnowledgeLevel.L2, 
                KnowledgeDomain.ANALYSIS, DifficultyLevel.ADVANCED, "54E50",
                ["C041", "C032"], "柯西序列收敛的空间", 5.0),
        Concept("C043", "紧致性", "Compactness", KnowledgeLevel.L2, 
                KnowledgeDomain.ANALYSIS, DifficultyLevel.ADVANCED, "54D30",
                ["C041"], "有限覆盖性质", 8.0),
        Concept("C044", "多元函数", "Multivariable Function", KnowledgeLevel.L1, 
                KnowledgeDomain.ANALYSIS, DifficultyLevel.INTERMEDIATE, "26B99",
                ["C003", "C015"], "多变量输入的函数", 5.0),
        Concept("C045", "偏导数", "Partial Derivative", KnowledgeLevel.L1, 
                KnowledgeDomain.ANALYSIS, DifficultyLevel.INTERMEDIATE, "26B05",
                ["C034", "C044"], "多元函数的单变量导数", 5.0),
    ]
    concepts.extend(analysis_concepts)
    
    # ==================== D4: 几何 (15个概念) ====================
    geometry_concepts = [
        Concept("C046", "欧几里得空间", "Euclidean Space", KnowledgeLevel.L1, 
                KnowledgeDomain.GEOMETRY, DifficultyLevel.INTERMEDIATE, "51M05",
                ["C025", "C041"], "具有内积的实向量空间", 6.0),
        Concept("C047", "内积", "Inner Product", KnowledgeLevel.L1, 
                KnowledgeDomain.GEOMETRY, DifficultyLevel.INTERMEDIATE, "15A63",
                ["C025"], "向量间的双线性形式", 5.0),
        Concept("C048", "范数", "Norm", KnowledgeLevel.L1, 
                KnowledgeDomain.GEOMETRY, DifficultyLevel.INTERMEDIATE, "46B20",
                ["C047"], "向量的长度度量", 4.0),
        Concept("C049", "距离", "Distance", KnowledgeLevel.L0, 
                KnowledgeDomain.GEOMETRY, DifficultyLevel.ELEMENTARY, "51K05",
                ["C048"], "点与点之间的度量", 3.0),
        Concept("C050", "角度", "Angle", KnowledgeLevel.L0, 
                KnowledgeDomain.GEOMETRY, DifficultyLevel.ELEMENTARY, "51N20",
                ["C047"], "向量间的夹角度量", 3.0),
        Concept("C051", "曲率", "Curvature", KnowledgeLevel.L2, 
                KnowledgeDomain.GEOMETRY, DifficultyLevel.ADVANCED, "53A04",
                ["C034", "C050"], "曲线或曲面的弯曲程度", 8.0),
        Concept("C052", "流形", "Manifold", KnowledgeLevel.L2, 
                KnowledgeDomain.GEOMETRY, DifficultyLevel.ADVANCED, "57N99",
                ["C041", "C042", "C033"], "局部类似于欧氏空间的空间", 12.0),
        Concept("C053", "切空间", "Tangent Space", KnowledgeLevel.L2, 
                KnowledgeDomain.GEOMETRY, DifficultyLevel.ADVANCED, "53A99",
                ["C052", "C025"], "流形上某点的线性近似空间", 7.0),
        Concept("C054", "黎曼度量", "Riemannian Metric", KnowledgeLevel.L2, 
                KnowledgeDomain.GEOMETRY, DifficultyLevel.ADVANCED, "53B20",
                ["C052", "C047"], "流形上的光滑内积场", 10.0),
        Concept("C055", "黎曼流形", "Riemannian Manifold", KnowledgeLevel.L2, 
                KnowledgeDomain.GEOMETRY, DifficultyLevel.ADVANCED, "53B20",
                ["C054", "C052"], "配备黎曼度量的流形", 8.0),
        Concept("C056", "测地线", "Geodesic", KnowledgeLevel.L2, 
                KnowledgeDomain.GEOMETRY, DifficultyLevel.ADVANCED, "53C22",
                ["C055", "C051"], "局部最短路径曲线", 7.0),
        Concept("C057", "代数曲线", "Algebraic Curve", KnowledgeLevel.L2, 
                KnowledgeDomain.GEOMETRY, DifficultyLevel.ADVANCED, "14H99",
                ["C023", "C008"], "多项式零点集定义的曲线", 8.0),
        Concept("C058", "概形", "Scheme", KnowledgeLevel.L3, 
                KnowledgeDomain.GEOMETRY, DifficultyLevel.EXPERT, "14A15",
                ["C057", "C030"], "代数几何的基本对象", 15.0),
        Concept("C059", "层", "Sheaf", KnowledgeLevel.L3, 
                KnowledgeDomain.GEOMETRY, DifficultyLevel.EXPERT, "14F05",
                ["C058"], "局部到整体的粘合结构", 12.0),
        Concept("C060", "上同调", "Cohomology", KnowledgeLevel.L3, 
                KnowledgeDomain.GEOMETRY, DifficultyLevel.EXPERT, "14F43",
                ["C059"], "层的全局截面障碍度量", 15.0),
    ]
    concepts.extend(geometry_concepts)
    
    # ==================== D5: 拓扑 (10个概念) ====================
    topology_concepts = [
        Concept("C061", "拓扑空间", "Topological Space", KnowledgeLevel.L1, 
                KnowledgeDomain.TOPOLOGY, DifficultyLevel.INTERMEDIATE, "54A99",
                ["C002", "C033"], "具有开集族结构的集合", 8.0),
        Concept("C062", "开集", "Open Set", KnowledgeLevel.L1, 
                KnowledgeDomain.TOPOLOGY, DifficultyLevel.INTERMEDIATE, "54A99",
                ["C061"], "拓扑的基本构成元素", 4.0),
        Concept("C063", "闭集", "Closed Set", KnowledgeLevel.L1, 
                KnowledgeDomain.TOPOLOGY, DifficultyLevel.INTERMEDIATE, "54A99",
                ["C062"], "开集的补集", 3.0),
        Concept("C064", "连续映射", "Continuous Map", KnowledgeLevel.L1, 
                KnowledgeDomain.TOPOLOGY, DifficultyLevel.INTERMEDIATE, "54C05",
                ["C061", "C033"], "拓扑空间间的结构保持映射", 5.0),
        Concept("C065", "同胚", "Homeomorphism", KnowledgeLevel.L1, 
                KnowledgeDomain.TOPOLOGY, DifficultyLevel.INTERMEDIATE, "54C05",
                ["C064"], "拓扑空间的等价关系", 4.0),
        Concept("C066", "连通性", "Connectedness", KnowledgeLevel.L1, 
                KnowledgeDomain.TOPOLOGY, DifficultyLevel.INTERMEDIATE, "54D05",
                ["C061"], "空间不能被分割为不交开集", 5.0),
        Concept("C067", "道路连通", "Path Connectedness", KnowledgeLevel.L1, 
                KnowledgeDomain.TOPOLOGY, DifficultyLevel.INTERMEDIATE, "54D05",
                ["C066"], "任意两点可由道路连接", 4.0),
        Concept("C068", "同伦", "Homotopy", KnowledgeLevel.L2, 
                KnowledgeDomain.TOPOLOGY, DifficultyLevel.ADVANCED, "55P99",
                ["C067", "C064"], "映射间的连续变形", 10.0),
        Concept("C069", "基本群", "Fundamental Group", KnowledgeLevel.L2, 
                KnowledgeDomain.TOPOLOGY, DifficultyLevel.ADVANCED, "55Q05",
                ["C068", "C017"], "环路等价类的群结构", 10.0),
        Concept("C070", "同调", "Homology", KnowledgeLevel.L2, 
                KnowledgeDomain.TOPOLOGY, DifficultyLevel.ADVANCED, "55N99",
                ["C069", "C060"], "空间的代数不变量", 12.0),
    ]
    concepts.extend(topology_concepts)
    
    # ==================== D6: 数论 (10个概念) ====================
    number_theory_concepts = [
        Concept("C071", "素数", "Prime Number", KnowledgeLevel.L0, 
                KnowledgeDomain.NUMBER_THEORY, DifficultyLevel.ELEMENTARY, "11A41",
                ["C004", "C005"], "大于1的最小正因子为自身的数", 4.0),
        Concept("C072", "整除", "Divisibility", KnowledgeLevel.L0, 
                KnowledgeDomain.NUMBER_THEORY, DifficultyLevel.ELEMENTARY, "11A05",
                ["C005"], "一个整数被另一个整数除尽", 2.0),
        Concept("C073", "最大公因子", "GCD", KnowledgeLevel.L0, 
                KnowledgeDomain.NUMBER_THEORY, DifficultyLevel.ELEMENTARY, "11A05",
                ["C072"], "能整除多个整数的最大正整数", 3.0),
        Concept("C074", "同余", "Congruence", KnowledgeLevel.L1, 
                KnowledgeDomain.NUMBER_THEORY, DifficultyLevel.INTERMEDIATE, "11A07",
                ["C072", "C013"], "模意义下的等价关系", 5.0),
        Concept("C075", "欧拉函数", "Euler's Totient Function", KnowledgeLevel.L1, 
                KnowledgeDomain.NUMBER_THEORY, DifficultyLevel.INTERMEDIATE, "11A25",
                ["C074"], "与n互素的剩余类个数", 5.0),
        Concept("C076", "费马小定理", "Fermat's Little Theorem", KnowledgeLevel.L1, 
                KnowledgeDomain.NUMBER_THEORY, DifficultyLevel.INTERMEDIATE, "11A07",
                ["C074", "C017"], "模素数的幂同余定理", 4.0),
        Concept("C077", "中国剩余定理", "Chinese Remainder Theorem", KnowledgeLevel.L1, 
                KnowledgeDomain.NUMBER_THEORY, DifficultyLevel.INTERMEDIATE, "11A07",
                ["C074", "C020"], "同余方程组的解结构", 5.0),
        Concept("C078", "二次剩余", "Quadratic Residue", KnowledgeLevel.L2, 
                KnowledgeDomain.NUMBER_THEORY, DifficultyLevel.ADVANCED, "11A15",
                ["C074"], "模意义下的平方数", 6.0),
        Concept("C079", "狄利克雷特征", "Dirichlet Character", KnowledgeLevel.L2, 
                KnowledgeDomain.NUMBER_THEORY, DifficultyLevel.ADVANCED, "11A25",
                ["C074", "C075"], "模q的群特征", 8.0),
        Concept("C080", "L函数", "L-function", KnowledgeLevel.L3, 
                KnowledgeDomain.NUMBER_THEORY, DifficultyLevel.EXPERT, "11M06",
                ["C079", "C039"], "解析数论的核心对象", 15.0),
    ]
    concepts.extend(number_theory_concepts)
    
    # ==================== D7: 离散数学 (10个概念) ====================
    discrete_concepts = [
        Concept("C081", "图", "Graph", KnowledgeLevel.L0, 
                KnowledgeDomain.DISCRETE, DifficultyLevel.ELEMENTARY, "05C99",
                ["C002", "C001"], "顶点和边的组合结构", 5.0),
        Concept("C082", "路径", "Path", KnowledgeLevel.L0, 
                KnowledgeDomain.DISCRETE, DifficultyLevel.ELEMENTARY, "05C38",
                ["C081"], "图中顶点的序列连接", 3.0),
        Concept("C083", "树", "Tree", KnowledgeLevel.L1, 
                KnowledgeDomain.DISCRETE, DifficultyLevel.ELEMENTARY, "05C05",
                ["C082"], "无环连通图", 4.0),
        Concept("C084", "连通图", "Connected Graph", KnowledgeLevel.L0, 
                KnowledgeDomain.DISCRETE, DifficultyLevel.ELEMENTARY, "05C40",
                ["C081", "C082"], "任意两点间存在路径的图", 3.0),
        Concept("C085", "组合数", "Combination", KnowledgeLevel.L0, 
                KnowledgeDomain.DISCRETE, DifficultyLevel.ELEMENTARY, "05A10",
                ["C004"], "从n个元素中选k个的方法数", 4.0),
        Concept("C086", "排列", "Permutation", KnowledgeLevel.L0, 
                KnowledgeDomain.DISCRETE, DifficultyLevel.ELEMENTARY, "05A05",
                ["C004"], "元素的重新排列", 3.0),
        Concept("C087", "二项式定理", "Binomial Theorem", KnowledgeLevel.L1, 
                KnowledgeDomain.DISCRETE, DifficultyLevel.ELEMENTARY, "11B65",
                ["C085"], "(a+b)^n的展开公式", 4.0),
        Concept("C088", "算法", "Algorithm", KnowledgeLevel.L1, 
                KnowledgeDomain.DISCRETE, DifficultyLevel.INTERMEDIATE, "68W01",
                ["C031", "C009"], "解决问题的明确步骤序列", 8.0),
        Concept("C089", "复杂度", "Complexity", KnowledgeLevel.L2, 
                KnowledgeDomain.DISCRETE, DifficultyLevel.ADVANCED, "68Q15",
                ["C088"], "算法资源消耗的度量", 8.0),
        Concept("C090", "图灵机", "Turing Machine", KnowledgeLevel.L2, 
                KnowledgeDomain.DISCRETE, DifficultyLevel.ADVANCED, "68Q05",
                ["C088", "C009"], "计算的抽象模型", 10.0),
    ]
    concepts.extend(discrete_concepts)
    
    # ==================== D8: 交叉领域 (10个概念) ====================
    interdisciplinary_concepts = [
        Concept("C091", "表示", "Representation", KnowledgeLevel.L2, 
                KnowledgeDomain.INTERDISCIPLINARY, DifficultyLevel.ADVANCED, "20C99",
                ["C017", "C025", "C026"], "抽象结构的线性实现", 10.0),
        Concept("C092", "群表示", "Group Representation", KnowledgeLevel.L2, 
                KnowledgeDomain.INTERDISCIPLINARY, DifficultyLevel.ADVANCED, "20C99",
                ["C091", "C017"], "群的线性表示", 8.0),
        Concept("C093", "李群", "Lie Group", KnowledgeLevel.L3, 
                KnowledgeDomain.INTERDISCIPLINARY, DifficultyLevel.EXPERT, "22E99",
                ["C017", "C052", "C034"], "光滑流形上的群", 15.0),
        Concept("C094", "李代数", "Lie Algebra", KnowledgeLevel.L3, 
                KnowledgeDomain.INTERDISCIPLINARY, DifficultyLevel.EXPERT, "17B99",
                ["C093", "C025"], "李群的无穷小生成元", 12.0),
        Concept("C095", "自守形式", "Automorphic Form", KnowledgeLevel.L3, 
                KnowledgeDomain.INTERDISCIPLINARY, DifficultyLevel.EXPERT, "11F99",
                ["C080", "C093"], "对称函数的推广", 15.0),
        Concept("C096", "朗兰兹纲领", "Langlands Program", KnowledgeLevel.L3, 
                KnowledgeDomain.INTERDISCIPLINARY, DifficultyLevel.EXPERT, "11R39",
                ["C092", "C080", "C095"], "数论与表示论的统一框架", 20.0),
        Concept("C097", "范畴", "Category", KnowledgeLevel.L2, 
                KnowledgeDomain.INTERDISCIPLINARY, DifficultyLevel.ADVANCED, "18A05",
                ["C002", "C003", "C016"], "对象与态射的结构", 10.0),
        Concept("C098", "函子", "Functor", KnowledgeLevel.L2, 
                KnowledgeDomain.INTERDISCIPLINARY, DifficultyLevel.ADVANCED, "18A99",
                ["C097"], "范畴间的结构保持映射", 8.0),
        Concept("C099", "泛性质", "Universal Property", KnowledgeLevel.L2, 
                KnowledgeDomain.INTERDISCIPLINARY, DifficultyLevel.ADVANCED, "18A40",
                ["C097"], "通过映射性质定义构造", 8.0),
        Concept("C100", "导出范畴", "Derived Category", KnowledgeLevel.L3, 
                KnowledgeDomain.INTERDISCIPLINARY, DifficultyLevel.EXPERT, "18E30",
                ["C097", "C060", "C098"], "复形的局部化范畴", 18.0),
    ]
    concepts.extend(interdisciplinary_concepts)
    
    return concepts


# ============================================================================
# 有向图构建
# ============================================================================

class ConceptDependencyGraph:
    """
    概念依赖图类
    
    基于数学概念的前置依赖关系构建有向图，
    支持拓扑排序、路径生成、可视化等功能。
    """
    
    def __init__(self):
        """初始化概念依赖图"""
        self.nodes: Dict[str, Concept] = {}  # 节点字典
        self.edges: Dict[str, List[str]] = defaultdict(list)  # 出边邻接表
        self.in_degree: Dict[str, int] = defaultdict(int)  # 入度
        self.reverse_edges: Dict[str, List[str]] = defaultdict(list)  # 反向边（用于查找前置）
        
    def add_concept(self, concept: Concept) -> None:
        """
        添加概念节点
        
        Args:
            concept: 概念对象
        """
        self.nodes[concept.id] = concept
        if concept.id not in self.in_degree:
            self.in_degree[concept.id] = 0
            
    def add_dependency(self, from_id: str, to_id: str) -> None:
        """
        添加依赖边（前置关系）
        
        from_id 是 to_id 的前置概念
        
        Args:
            from_id: 前置概念ID
            to_id: 目标概念ID
        """
        if from_id in self.edges and to_id in self.edges[from_id]:
            return  # 边已存在
        
        self.edges[from_id].append(to_id)
        self.reverse_edges[to_id].append(from_id)
        self.in_degree[to_id] += 1
        
    def build_from_concepts(self, concepts: List[Concept]) -> None:
        """
        从概念列表构建依赖图
        
        Args:
            concepts: 概念列表
        """
        # 添加所有节点
        for concept in concepts:
            self.add_concept(concept)
        
        # 根据prerequisites添加边
        for concept in concepts:
            for prereq_id in concept.prerequisites:
                if prereq_id in self.nodes:
                    self.add_dependency(prereq_id, concept.id)
                    
    def get_prerequisites(self, concept_id: str, recursive: bool = False) -> Set[str]:
        """
        获取概念的前置概念
        
        Args:
            concept_id: 概念ID
            recursive: 是否递归获取所有间接前置
            
        Returns:
            Set[str]: 前置概念ID集合
        """
        if not recursive:
            return set(self.reverse_edges[concept_id])
        
        # BFS获取所有前置
        prerequisites = set()
        queue = deque([concept_id])
        visited = {concept_id}
        
        while queue:
            current = queue.popleft()
            for prereq in self.reverse_edges[current]:
                if prereq not in visited:
                    visited.add(prereq)
                    prerequisites.add(prereq)
                    queue.append(prereq)
                    
        return prerequisites
    
    def get_successors(self, concept_id: str, recursive: bool = False) -> Set[str]:
        """
        获取概念的后继概念
        
        Args:
            concept_id: 概念ID
            recursive: 是否递归获取所有间接后继
            
        Returns:
            Set[str]: 后继概念ID集合
        """
        if not recursive:
            return set(self.edges[concept_id])
        
        # BFS获取所有后继
        successors = set()
        queue = deque([concept_id])
        visited = {concept_id}
        
        while queue:
            current = queue.popleft()
            for succ in self.edges[current]:
                if succ not in visited:
                    visited.add(succ)
                    successors.add(succ)
                    queue.append(succ)
                    
        return successors


# ============================================================================
# 拓扑排序算法
# ============================================================================

def topological_sort_kahn(graph: ConceptDependencyGraph) -> List[str]:
    """
    Kahn算法拓扑排序
    
    基于入度的拓扑排序算法，时间复杂度O(V+E)。
    
    Args:
        graph: 概念依赖图
        
    Returns:
        List[str]: 拓扑排序后的概念ID列表
        
    Raises:
        ValueError: 如果图中存在环
    """
    # 复制入度字典
    in_degree = graph.in_degree.copy()
    
    # 初始化队列：所有入度为0的节点
    queue = deque([node_id for node_id, degree in in_degree.items() if degree == 0])
    result = []
    
    while queue:
        # 按难度排序，先学简单的
        queue = deque(sorted(queue, key=lambda x: graph.nodes[x].difficulty.value))
        node = queue.popleft()
        result.append(node)
        
        # 更新后继节点的入度
        for successor in graph.edges[node]:
            in_degree[successor] -= 1
            if in_degree[successor] == 0:
                queue.append(successor)
    
    # 检查是否有环
    if len(result) != len(graph.nodes):
        # 找出环中的节点
        unprocessed = [node_id for node_id in graph.nodes if node_id not in result]
        raise ValueError(f"图中存在环，无法完成拓扑排序。环中节点: {unprocessed}")
    
    return result


def topological_sort_with_levels(graph: ConceptDependencyGraph) -> Dict[KnowledgeLevel, List[str]]:
    """
    带层次信息的拓扑排序
    
    将概念按知识层次分组进行拓扑排序。
    
    Args:
        graph: 概念依赖图
        
    Returns:
        Dict[KnowledgeLevel, List[str]]: 按层次分组的排序结果
    """
    # 获取完整的拓扑排序
    full_order = topological_sort_kahn(graph)
    
    # 按层次分组
    result = {
        KnowledgeLevel.L0: [],
        KnowledgeLevel.L1: [],
        KnowledgeLevel.L2: [],
        KnowledgeLevel.L3: []
    }
    
    for concept_id in full_order:
        level = graph.nodes[concept_id].level
        result[level].append(concept_id)
        
    return result


def topological_sort_dfs(graph: ConceptDependencyGraph) -> List[str]:
    """
    DFS拓扑排序
    
    基于深度优先搜索的拓扑排序，用于验证Kahn算法结果。
    
    Args:
        graph: 概念依赖图
        
    Returns:
        List[str]: 拓扑排序后的概念ID列表
    """
    WHITE, GRAY, BLACK = 0, 1, 2
    color = {node_id: WHITE for node_id in graph.nodes}
    result = []
    
    def dfs(node_id: str) -> None:
        color[node_id] = GRAY
        
        for successor in graph.edges[node_id]:
            if color[successor] == GRAY:
                raise ValueError(f"检测到环，节点: {node_id} -> {successor}")
            if color[successor] == WHITE:
                dfs(successor)
        
        color[node_id] = BLACK
        result.append(node_id)
    
    for node_id in graph.nodes:
        if color[node_id] == WHITE:
            dfs(node_id)
    
    return result[::-1]  # 反转得到正确顺序


# ============================================================================
# 学习路径生成器
# ============================================================================

class LearningPathGenerator:
    """
    学习路径生成器
    
    根据用户水平和目标生成个性化学习路径。
    """
    
    def __init__(self, graph: ConceptDependencyGraph):
        """
        初始化学习路径生成器
        
        Args:
            graph: 概念依赖图
        """
        self.graph = graph
        
    def generate_path(self, 
                     target_concepts: List[str], 
                     user_level: DifficultyLevel,
                     mastered_concepts: Optional[Set[str]] = None) -> List[Concept]:
        """
        生成个性化学习路径
        
        Args:
            target_concepts: 目标概念ID列表
            user_level: 用户当前水平
            mastered_concepts: 已掌握的概念ID集合
            
        Returns:
            List[Concept]: 按学习顺序排列的概念列表
        """
        if mastered_concepts is None:
            mastered_concepts = set()
        
        # 找出所有必需的前置概念
        required = set()
        for target in target_concepts:
            if target in self.graph.nodes:
                required.update(self.graph.get_prerequisites(target, recursive=True))
                required.add(target)
        
        # 过滤掉已掌握的概念
        required = required - mastered_concepts
        
        if not required:
            return []
        
        # 构建子图
        sub_graph = ConceptDependencyGraph()
        for concept_id in required:
            sub_graph.add_concept(self.graph.nodes[concept_id])
        
        for concept_id in required:
            for prereq in self.graph.reverse_edges[concept_id]:
                if prereq in required:
                    sub_graph.add_dependency(prereq, concept_id)
        
        # 拓扑排序
        path_ids = topological_sort_kahn(sub_graph)
        
        # 过滤难度过高的概念（用户水平+1以上）
        max_difficulty = user_level.value + 1
        path_ids = [cid for cid in path_ids 
                   if self.graph.nodes[cid].difficulty.value <= max_difficulty]
        
        # 转换为概念对象
        return [self.graph.nodes[cid] for cid in path_ids]
    
    def generate_full_curriculum(self, 
                                 start_level: KnowledgeLevel = KnowledgeLevel.L0,
                                 max_difficulty: Optional[DifficultyLevel] = None) -> Dict[KnowledgeLevel, List[Concept]]:
        """
        生成完整课程大纲
        
        Args:
            start_level: 起始知识层次
            max_difficulty: 最大难度限制
            
        Returns:
            Dict[KnowledgeLevel, List[Concept]]: 按层次组织的课程
        """
        result = {}
        
        for level in KnowledgeLevel:
            if level.value < start_level.value:
                continue
                
            concepts = [c for c in self.graph.nodes.values() 
                       if c.level == level]
            
            if max_difficulty:
                concepts = [c for c in concepts 
                          if c.difficulty.value <= max_difficulty.value]
            
            # 按难度排序
            concepts.sort(key=lambda x: (x.difficulty.value, x.id))
            result[level] = concepts
            
        return result
    
    def estimate_learning_time(self, path: List[Concept]) -> Dict[str, Any]:
        """
        估计学习时长
        
        Args:
            path: 学习路径
            
        Returns:
            Dict: 包含总时长、各层次时长的统计信息
        """
        total_hours = sum(c.estimated_hours for c in path)
        
        by_domain = defaultdict(float)
        by_level = defaultdict(float)
        
        for concept in path:
            by_domain[concept.domain.value] += concept.estimated_hours
            by_level[concept.level.name] += concept.estimated_hours
        
        return {
            'total_hours': total_hours,
            'total_days': total_hours / 4,  # 假设每天学习4小时
            'by_domain': dict(by_domain),
            'by_level': dict(by_level),
            'concept_count': len(path)
        }


# ============================================================================
# 可视化输出
# ============================================================================

def generate_mermaid_graph(graph: ConceptDependencyGraph, 
                           highlight_path: Optional[List[str]] = None) -> str:
    """
    生成Mermaid图表示
    
    Args:
        graph: 概念依赖图
        highlight_path: 需要高亮的路径
        
    Returns:
        str: Mermaid图表代码
    """
    if highlight_path is None:
        highlight_path = []
    highlight_set = set(highlight_path)
    
    # 颜色映射
    domain_colors = {
        KnowledgeDomain.FOUNDATION: "#E1F5FE",      # 浅蓝
        KnowledgeDomain.ALGEBRA: "#F3E5F5",         # 浅紫
        KnowledgeDomain.ANALYSIS: "#E8F5E9",        # 浅绿
        KnowledgeDomain.GEOMETRY: "#FFF3E0",        # 浅橙
        KnowledgeDomain.TOPOLOGY: "#ECEFF1",        # 浅灰蓝
        KnowledgeDomain.NUMBER_THEORY: "#FBE9E7",   # 浅红
        KnowledgeDomain.DISCRETE: "#E0F2F1",        # 浅青
        KnowledgeDomain.INTERDISCIPLINARY: "#FFF8E1" # 浅黄
    }
    
    lines = ["```mermaid", "graph TD"]
    
    # 添加节点定义
    for concept_id, concept in graph.nodes.items():
        color = domain_colors.get(concept.domain, "#FFFFFF")
        style = ":::highlight" if concept_id in highlight_set else ""
        
        # 节点标签：ID + 名称
        label = f"{concept.name}<br/><small>{concept_id}</small>"
        
        lines.append(f'    {concept_id}["{label}"]{style}')
        lines.append(f'    style {concept_id} fill:{color}')
    
    # 添加边
    for from_id, to_ids in graph.edges.items():
        for to_id in to_ids:
            # 根据依赖强度设置线条粗细
            from_concept = graph.nodes[from_id]
            to_concept = graph.nodes[to_id]
            
            # 同领域直接依赖用粗线
            if from_concept.domain == to_concept.domain:
                line = f"    {from_id} ==> {to_id}"
            else:
                line = f"    {from_id} --> {to_id}"
            
            if from_id in highlight_set and to_id in highlight_set:
                line += "::highlighted"
            
            lines.append(line)
    
    # 添加图例
    lines.append("")
    lines.append("    subgraph Legend[图例]")
    lines.append("        direction LR")
    lines.append("        L1[基础数学]:::foundation")
    lines.append("        L2[代数]:::algebra")
    lines.append("        L3[分析]:::analysis")
    lines.append("        L4[几何]:::geometry")
    lines.append("        L5[拓扑]:::topology")
    lines.append("        L6[数论]:::numbertheory")
    lines.append("        L7[离散]:::discrete")
    lines.append("        L8[交叉]:::interdisciplinary")
    lines.append("    end")
    
    lines.append("")
    lines.append("    classDef foundation fill:#E1F5FE")
    lines.append("    classDef algebra fill:#F3E5F5")
    lines.append("    classDef analysis fill:#E8F5E9")
    lines.append("    classDef geometry fill:#FFF3E0")
    lines.append("    classDef topology fill:#ECEFF1")
    lines.append("    classDef numbertheory fill:#FBE9E7")
    lines.append("    classDef discrete fill:#E0F2F1")
    lines.append("    classDef interdisciplinary fill:#FFF8E1")
    lines.append("    classDef highlight stroke:#FF5722,stroke-width:3px")
    
    lines.append("```")
    
    return "\n".join(lines)


def generate_domain_subgraph(graph: ConceptDependencyGraph, 
                             domain: KnowledgeDomain) -> str:
    """
    生成特定领域的Mermaid子图
    
    Args:
        graph: 概念依赖图
        domain: 知识领域
        
    Returns:
        str: Mermaid子图代码
    """
    # 筛选该领域的概念
    domain_concepts = {cid: c for cid, c in graph.nodes.items() 
                      if c.domain == domain}
    
    if not domain_concepts:
        return ""
    
    lines = ["```mermaid", f"graph TD"]
    lines.append(f"    subgraph {domain.value}[{domain.value} 领域依赖图]")
    lines.append("        direction TB")
    
    # 添加节点
    for concept_id, concept in domain_concepts.items():
        label = f"{concept.name}"
        lines.append(f'        {concept_id}["{label}"]')
    
    # 添加内部边
    for from_id, to_ids in graph.edges.items():
        if from_id in domain_concepts:
            for to_id in to_ids:
                if to_id in domain_concepts:
                    lines.append(f"        {from_id} --> {to_id}")
    
    lines.append("    end")
    lines.append("```")
    
    return "\n".join(lines)


# ============================================================================
# 统计与分析
# ============================================================================

def analyze_graph(graph: ConceptDependencyGraph) -> Dict[str, Any]:
    """
    分析依赖图的结构特征
    
    Args:
        graph: 概念依赖图
        
    Returns:
        Dict: 统计分析结果
    """
    stats = {
        'total_concepts': len(graph.nodes),
        'total_dependencies': sum(len(edges) for edges in graph.edges.values()),
        'by_domain': defaultdict(int),
        'by_level': defaultdict(int),
        'by_difficulty': defaultdict(int),
        'avg_prerequisites': 0,
        'max_prerequisites': 0,
        'root_concepts': [],  # 无前置的概念
        'leaf_concepts': [],  # 无后继的概念
    }
    
    for concept_id, concept in graph.nodes.items():
        stats['by_domain'][concept.domain.value] += 1
        stats['by_level'][concept.level.name] += 1
        stats['by_difficulty'][concept.difficulty.name] += 1
        
        prereq_count = len(graph.reverse_edges[concept_id])
        if prereq_count == 0:
            stats['root_concepts'].append(concept_id)
        if prereq_count > stats['max_prerequisites']:
            stats['max_prerequisites'] = prereq_count
        
        if len(graph.edges[concept_id]) == 0:
            stats['leaf_concepts'].append(concept_id)
    
    stats['avg_prerequisites'] = stats['total_dependencies'] / len(graph.nodes) if graph.nodes else 0
    stats['by_domain'] = dict(stats['by_domain'])
    stats['by_level'] = dict(stats['by_level'])
    stats['by_difficulty'] = dict(stats['by_difficulty'])
    
    return stats


def detect_cycles(graph: ConceptDependencyGraph) -> List[List[str]]:
    """
    检测图中的所有环
    
    Args:
        graph: 概念依赖图
        
    Returns:
        List[List[str]]: 环列表
    """
    WHITE, GRAY, BLACK = 0, 1, 2
    color = {node_id: WHITE for node_id in graph.nodes}
    cycles = []
    path = []
    
    def dfs(node_id: str) -> None:
        color[node_id] = GRAY
        path.append(node_id)
        
        for successor in graph.edges[node_id]:
            if color[successor] == GRAY:
                # 发现环
                cycle_start = path.index(successor)
                cycle = path[cycle_start:] + [successor]
                cycles.append(cycle)
            elif color[successor] == WHITE:
                dfs(successor)
        
        path.pop()
        color[node_id] = BLACK
    
    for node_id in graph.nodes:
        if color[node_id] == WHITE:
            dfs(node_id)
    
    return cycles


# ============================================================================
# 导出功能
# ============================================================================

def export_to_json(graph: ConceptDependencyGraph, filepath: str) -> None:
    """
    导出图为JSON格式
    
    Args:
        graph: 概念依赖图
        filepath: 输出文件路径
    """
    data = {
        'nodes': [concept.to_dict() for concept in graph.nodes.values()],
        'edges': [
            {'from': from_id, 'to': to_id}
            for from_id, to_ids in graph.edges.items()
            for to_id in to_ids
        ]
    }
    
    with open(filepath, 'w', encoding='utf-8') as f:
        json.dump(data, f, ensure_ascii=False, indent=2)


def export_learning_path(path: List[Concept], filepath: str) -> None:
    """
    导出学习路径为JSON格式
    
    Args:
        path: 学习路径
        filepath: 输出文件路径
    """
    data = {
        'path': [concept.to_dict() for concept in path],
        'summary': {
            'total_concepts': len(path),
            'total_hours': sum(c.estimated_hours for c in path),
            'by_domain': {}
        }
    }
    
    for concept in path:
        domain = concept.domain.value
        if domain not in data['summary']['by_domain']:
            data['summary']['by_domain'][domain] = 0
        data['summary']['by_domain'][domain] += 1
    
    with open(filepath, 'w', encoding='utf-8') as f:
        json.dump(data, f, ensure_ascii=False, indent=2)


# ============================================================================
# 主函数
# ============================================================================

def main():
    """
    主函数：构建全局依赖图并生成所有输出
    """
    print("=" * 60)
    print("FormalMath 全局依赖图构建系统")
    print("=" * 60)
    
    # 1. 获取100个核心概念
    print("\n[1/6] 加载100个核心概念...")
    concepts = get_core_concepts()
    print(f"      ✓ 已加载 {len(concepts)} 个概念")
    
    # 统计各领域的概念数
    domain_counts = defaultdict(int)
    for c in concepts:
        domain_counts[c.domain.value] += 1
    for domain, count in sorted(domain_counts.items()):
        print(f"        - {domain}: {count}个")
    
    # 2. 构建依赖图
    print("\n[2/6] 构建概念依赖图...")
    graph = ConceptDependencyGraph()
    graph.build_from_concepts(concepts)
    
    stats = analyze_graph(graph)
    print(f"      ✓ 节点数: {stats['total_concepts']}")
    print(f"      ✓ 依赖边数: {stats['total_dependencies']}")
    print(f"      ✓ 平均前置数: {stats['avg_prerequisites']:.2f}")
    print(f"      ✓ 根概念数: {len(stats['root_concepts'])}")
    print(f"      ✓ 叶概念数: {len(stats['leaf_concepts'])}")
    
    # 3. 拓扑排序
    print("\n[3/6] 执行拓扑排序...")
    try:
        sorted_ids = topological_sort_kahn(graph)
        print(f"      ✓ Kahn算法成功，生成 {len(sorted_ids)} 个节点的排序")
        
        # 验证
        sorted_ids_dfs = topological_sort_dfs(graph)
        if set(sorted_ids) == set(sorted_ids_dfs):
            print(f"      ✓ DFS算法验证通过")
        
        # 按层次分组
        by_level = topological_sort_with_levels(graph)
        for level, ids in by_level.items():
            print(f"        - {level.name}: {len(ids)}个概念")
            
    except ValueError as e:
        print(f"      ✗ 错误: {e}")
        cycles = detect_cycles(graph)
        print(f"      检测到 {len(cycles)} 个环")
        return
    
    # 4. 生成学习路径示例
    print("\n[4/6] 生成示例学习路径...")
    generator = LearningPathGenerator(graph)
    
    # 示例1: 学习"群"的路径
    path1 = generator.generate_path(["C017"], DifficultyLevel.ELEMENTARY)
    time1 = generator.estimate_learning_time(path1)
    print(f"      示例1 - 学习'群'的路径:")
    print(f"        概念数: {time1['concept_count']}")
    print(f"        预计时长: {time1['total_hours']:.1f}小时 ({time1['total_days']:.1f}天)")
    
    # 示例2: 学习"黎曼流形"的路径
    path2 = generator.generate_path(["C055"], DifficultyLevel.INTERMEDIATE)
    time2 = generator.estimate_learning_time(path2)
    print(f"      示例2 - 学习'黎曼流形'的路径:")
    print(f"        概念数: {time2['concept_count']}")
    print(f"        预计时长: {time2['total_hours']:.1f}小时 ({time2['total_days']:.1f}天)")
    
    # 5. 生成Mermaid图表
    print("\n[5/6] 生成Mermaid可视化图表...")
    mermaid_code = generate_mermaid_graph(graph)
    print(f"      ✓ 全局依赖图已生成")
    
    # 6. 导出数据
    print("\n[6/6] 导出数据文件...")
    os.makedirs("output", exist_ok=True)
    
    export_to_json(graph, "output/concept_dependency_graph.json")
    print(f"      ✓ 导出: output/concept_dependency_graph.json")
    
    export_learning_path(path1, "output/learning_path_group.json")
    print(f"      ✓ 导出: output/learning_path_group.json")
    
    with open("output/mermaid_graph.md", "w", encoding="utf-8") as f:
        f.write("# 全局概念依赖图\n\n")
        f.write(mermaid_code)
    print(f"      ✓ 导出: output/mermaid_graph.md")
    
    # 生成各领域的子图
    for domain in KnowledgeDomain:
        subgraph = generate_domain_subgraph(graph, domain)
        if subgraph:
            with open(f"output/mermaid_{domain.name.lower()}.md", "w", encoding="utf-8") as f:
                f.write(f"# {domain.value} 领域依赖图\n\n")
                f.write(subgraph)
    print(f"      ✓ 导出: 8个领域子图")
    
    print("\n" + "=" * 60)
    print("全局依赖图构建完成！")
    print("=" * 60)
    
    return graph, generator


if __name__ == "__main__":
    graph, generator = main()
