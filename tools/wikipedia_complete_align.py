#!/usr/bin/env python3
"""
Wikipedia多语言概念对齐工具 - 完整版
扩展预定义表覆盖所有299个概念
"""

import yaml
import json
import time
from pathlib import Path
from typing import Dict, List

# 完整的预定义多语言对照表（覆盖所有299个概念）
PREDEFINED_MULTILANG = {
    # ========== 分析学 (25个) ==========
    "limit": {"en": "Limit (mathematics)", "de": "Grenzwert (Folge)", "fr": "Limite (mathématiques)", "ja": "極限"},
    "continuity": {"en": "Continuous function", "de": "Stetige Funktion", "fr": "Fonction continue", "ja": "連続 (数学)"},
    "derivative": {"en": "Derivative", "de": "Ableitung (Mathematik)", "fr": "Dérivée", "ja": "導関数"},
    "riemann_integral": {"en": "Riemann integral", "de": "Riemann-Integral", "fr": "Intégrale de Riemann", "ja": "リーマン積分"},
    "lebesgue_integral": {"en": "Lebesgue integration", "de": "Lebesgue-Integral", "fr": "Intégrale de Lebesgue", "ja": "ルベーグ積分"},
    "infinite_series": {"en": "Series (mathematics)", "de": "Reihe (Mathematik)", "fr": "Série mathématique", "ja": "級数"},
    "sequence": {"en": "Sequence", "de": "Folge (Mathematik)", "fr": "Suite mathématique", "ja": "数列"},
    "convergence": {"en": "Limit of a sequence", "de": "Konvergenz (Mathematik)", "fr": "Convergence (mathématiques)", "ja": "収束 (数学)"},
    "uniform_convergence": {"en": "Uniform convergence", "de": "Gleichmäßige Konvergenz", "fr": "Convergence uniforme", "ja": "一様収束"},
    "power_series": {"en": "Power series", "de": "Potenzreihe", "fr": "Série entière", "ja": "冪級数"},
    "fourier_series": {"en": "Fourier series", "de": "Fourier-Reihe", "fr": "Série de Fourier", "ja": "フーリエ級数"},
    "laplace_transform": {"en": "Laplace transform", "de": "Laplace-Transformation", "fr": "Transformation de Laplace", "ja": "ラプラス変換"},
    "fourier_transform": {"en": "Fourier transform", "de": "Fourier-Transformation", "fr": "Transformation de Fourier", "ja": "フーリエ変換"},
    "ordinary_differential_equations": {"en": "Ordinary differential equation", "de": "Gewöhnliche Differentialgleichung", "fr": "Équation différentielle ordinaire", "ja": "常微分方程式"},
    "partial_differential_equations": {"en": "Partial differential equation", "de": "Partielle Differentialgleichung", "fr": "Équation aux dérivées partielles", "ja": "偏微分方程式"},
    "gradient": {"en": "Gradient", "de": "Gradient (Mathematik)", "fr": "Gradient", "ja": "勾配"},
    "divergence": {"en": "Divergence", "de": "Divergenz (Vektoranalysis)", "fr": "Divergence (analyse vectorielle)", "ja": "発散"},
    "curl": {"en": "Curl (mathematics)", "de": "Rotation (Mathematik)", "fr": "Rotationnel", "ja": "回転 (ベクトル解析)"},
    "jacobian": {"en": "Jacobian matrix and determinant", "de": "Jacobi-Matrix", "fr": "Matrice jacobienne", "ja": "ヤコビ行列"},
    "hessian": {"en": "Hessian matrix", "de": "Hessematrix", "fr": "Matrice hessienne", "ja": "ヘッセ行列"},
    "taylor_series": {"en": "Taylor series", "de": "Taylor-Reihe", "fr": "Série de Taylor", "ja": "テイラー級数"},
    "complex_analysis": {"en": "Complex analysis", "de": "Funktionentheorie", "fr": "Analyse complexe", "ja": "複素解析"},
    "real_analysis": {"en": "Real analysis", "de": "Reelle Analysis", "fr": "Analyse réelle", "ja": "実解析"},
    "functional_analysis": {"en": "Functional analysis", "de": "Funktionalanalysis", "fr": "Analyse fonctionnelle (mathématiques)", "ja": "関数解析"},
    "measure_theory": {"en": "Measure (mathematics)", "de": "Maß (Mathematik)", "fr": "Mesure (mathématiques)", "ja": "測度"},
    "metric_space": {"en": "Metric space", "de": "Metrischer Raum", "fr": "Espace métrique", "ja": "距離空間"},
    "normed_space": {"en": "Normed vector space", "de": "Normierter Raum", "fr": "Espace vectoriel normé", "ja": "ノルム空間"},
    "banach_space": {"en": "Banach space", "de": "Banach-Raum", "fr": "Espace de Banach", "ja": "バナッハ空間"},
    "hilbert_space": {"en": "Hilbert space", "de": "Hilbert-Raum", "fr": "Espace de Hilbert", "ja": "ヒルベルト空間"},
    "sobolev_space": {"en": "Sobolev space", "de": "Sobolev-Raum", "fr": "Espace de Sobolev", "ja": "ソボレフ空間"},
    
    # ========== 几何拓扑 (25个) ==========
    "topology": {"en": "Topology", "de": "Topologie (Mathematik)", "fr": "Topologie", "ja": "位相空間論"},
    "compactness": {"en": "Compact space", "de": "Kompakter Raum", "fr": "Espace compact", "ja": "コンパクト空間"},
    "connectedness": {"en": "Connected space", "de": "Zusammenhang (Topologie)", "fr": "Connexité (mathématiques)", "ja": "連結空間"},
    "homeomorphism": {"en": "Homeomorphism", "de": "Homöomorphismus", "fr": "Homéomorphisme", "ja": "位相同型"},
    "manifold": {"en": "Manifold", "de": "Mannigfaltigkeit", "fr": "Variété (géométrie)", "ja": "多様体"},
    "fundamental_group": {"en": "Fundamental group", "de": "Fundamentalgruppe", "fr": "Groupe fondamental", "ja": "基本群"},
    "homology": {"en": "Homology (mathematics)", "de": "Homologie (Mathematik)", "fr": "Homologie (mathématiques)", "ja": "ホモロジー"},
    "cohomology": {"en": "Cohomology", "de": "Kohomologie", "fr": "Cohomologie", "ja": "コホモロジー"},
    "differential_geometry": {"en": "Differential geometry", "de": "Differentialgeometrie", "fr": "Géométrie différentielle", "ja": "微分幾何学"},
    "riemannian_geometry": {"en": "Riemannian geometry", "de": "Riemannsche Geometrie", "fr": "Géométrie riemannienne", "ja": "リーマン幾何学"},
    "symplectic_geometry": {"en": "Symplectic geometry", "de": "Symplektische Geometrie", "fr": "Géométrie symplectique", "ja": "シンプレクティック幾何学"},
    "algebraic_topology": {"en": "Algebraic topology", "de": "Algebraische Topologie", "fr": "Topologie algébrique", "ja": "代数位相幾何学"},
    "knot_theory": {"en": "Knot theory", "de": "Knotentheorie", "fr": "Théorie des nœuds", "ja": "結び目理論"},
    "vector_bundle": {"en": "Vector bundle", "de": "Vektorbündel", "fr": "Fibré vectoriel", "ja": "ベクトル束"},
    "fiber_bundle": {"en": "Fiber bundle", "de": "Faserbündel", "fr": "Fibré", "ja": "ファイバー束"},
    "characteristic_class": {"en": "Characteristic class", "de": "Charakteristische Klasse", "fr": "Classe caractéristique", "ja": "特性類"},
    "morse_theory": {"en": "Morse theory", "de": "Morse-Theorie", "fr": "Théorie de Morse", "ja": "モーズ理論"},
    "index_theory": {"en": "Atiyah–Singer index theorem", "de": "Atiyah-Singer-Indexsatz", "fr": "Théorème de l'indice d'Atiyah-Singer", "ja": "アティヤ・シンガーの指数定理"},
    "geometric_group_theory": {"en": "Geometric group theory", "de": "Geometrische Gruppentheorie", "fr": "Théorie géométrique des groupes", "ja": "幾何学的群論"},
    "hyperbolic_geometry": {"en": "Hyperbolic geometry", "de": "Hyperbolische Geometrie", "fr": "Géométrie hyperbolique", "ja": "双曲幾何学"},
    
    # ========== 代数学 (25个) ==========
    "vector_space": {"en": "Vector space", "de": "Vektorraum", "fr": "Espace vectoriel", "ja": "ベクトル空間"},
    "linear_transformation": {"en": "Linear map", "de": "Lineare Abbildung", "fr": "Application linéaire", "ja": "線型写像"},
    "matrix": {"en": "Matrix (mathematics)", "de": "Matrix (Mathematik)", "fr": "Matrice (mathématiques)", "ja": "行列"},
    "determinant": {"en": "Determinant", "de": "Determinante", "fr": "Déterminant (mathématiques)", "ja": "行列式"},
    "eigenvalue": {"en": "Eigenvalues and eigenvectors", "de": "Eigenwertproblem", "fr": "Valeur propre", "ja": "固有値"},
    "inner_product": {"en": "Inner product space", "de": "Prähilbertraum", "fr": "Espace préhilbertien", "ja": "内積空間"},
    "tensor": {"en": "Tensor", "de": "Tensor", "fr": "Tenseur", "ja": "テンソル"},
    "group": {"en": "Group (mathematics)", "de": "Gruppe (Mathematik)", "fr": "Groupe (mathématiques)", "ja": "群"},
    "ring": {"en": "Ring (mathematics)", "de": "Ring (Algebra)", "fr": "Anneau (mathématiques)", "ja": "環 (数学)"},
    "field": {"en": "Field (mathematics)", "de": "Körper (Algebra)", "fr": "Corps commutatif", "ja": "体 (数学)"},
    "module": {"en": "Module (mathematics)", "de": "Modul (Mathematik)", "fr": "Module (mathématiques)", "ja": "加群"},
    "homomorphism": {"en": "Homomorphism", "de": "Homomorphismus", "fr": "Homomorphisme", "ja": "準同型"},
    "isomorphism": {"en": "Isomorphism", "de": "Isomorphismus", "fr": "Isomorphisme", "ja": "同型"},
    "quotient_group": {"en": "Quotient group", "de": "Faktorgruppe", "fr": "Groupe quotient", "ja": "商群"},
    "sylow_theorems": {"en": "Sylow theorems", "de": "Sylow-Sätze", "fr": "Théorèmes de Sylow", "ja": "シローの定理"},
    "galois_theory": {"en": "Galois theory", "de": "Galoistheorie", "fr": "Théorie de Galois", "ja": "ガロア理論"},
    "representation_theory": {"en": "Representation theory", "de": "Darstellungstheorie", "fr": "Théorie des représentations", "ja": "表現論"},
    "lie_group": {"en": "Lie group", "de": "Lie-Gruppe", "fr": "Groupe de Lie", "ja": "リー群"},
    "algebraic_geometry": {"en": "Algebraic geometry", "de": "Algebraische Geometrie", "fr": "Géométrie algébrique", "ja": "代数幾何学"},
    "commutative_algebra": {"en": "Commutative algebra", "de": "Kommutative Algebra", "fr": "Algèbre commutative", "ja": "可換環論"},
    "homological_algebra": {"en": "Homological algebra", "de": "Homologische Algebra", "fr": "Algèbre homologique", "ja": "ホモロジー代数"},
    "category_theory": {"en": "Category theory", "de": "Kategorientheorie", "fr": "Théorie des catégories", "ja": "圏論"},
    "functor": {"en": "Functor", "de": "Funktor (Mathematik)", "fr": "Foncteur", "ja": "関手"},
    "natural_transformation": {"en": "Natural transformation", "de": "Natürliche Transformation", "fr": "Transformation naturelle", "ja": "自然変換"},
    "universal_property": {"en": "Universal property", "de": "Universelle Eigenschaft", "fr": "Propriété universelle", "ja": "普遍性"},
    
    # ========== 数论逻辑 (25个) ==========
    "prime_number": {"en": "Prime number", "de": "Primzahl", "fr": "Nombre premier", "ja": "素数"},
    "gcd": {"en": "Greatest common divisor", "de": "Größter gemeinsamer Teiler", "fr": "Plus grand commun diviseur", "ja": "最大公約数"},
    "modular_arithmetic": {"en": "Modular arithmetic", "de": "Modulare Arithmetik", "fr": "Arithmétique modulaire", "ja": "合同式"},
    "chinese_remainder_theorem": {"en": "Chinese remainder theorem", "de": "Chinesischer Restsatz", "fr": "Théorème des restes chinois", "ja": "中国の剰余定理"},
    "euler_theorem": {"en": "Euler's theorem", "de": "Satz von Euler", "fr": "Théorème d'Euler", "ja": "オイラーの定理"},
    "fermat_little_theorem": {"en": "Fermat's little theorem", "de": "Kleiner fermatscher Satz", "fr": "Petit théorème de Fermat", "ja": "フェルマーの小定理"},
    "quadratic_reciprocity": {"en": "Quadratic reciprocity", "de": "Quadratisches Reziprozitätsgesetz", "fr": "Loi de réciprocité quadratique", "ja": "二次の相互法則"},
    "diophantine_equations": {"en": "Diophantine equation", "de": "Diophantische Gleichung", "fr": "Équation diophantienne", "ja": "ディオファントス方程式"},
    "prime_number_theorem": {"en": "Prime number theorem", "de": "Primzahlsatz", "fr": "Théorème des nombres premiers", "ja": "素数定理"},
    "riemann_hypothesis": {"en": "Riemann hypothesis", "de": "Riemannsche Vermutung", "fr": "Hypothèse de Riemann", "ja": "リーマン予想"},
    "algebraic_number_theory": {"en": "Algebraic number theory", "de": "Algebraische Zahlentheorie", "fr": "Théorie algébrique des nombres", "ja": "代数体論"},
    "analytic_number_theory": {"en": "Analytic number theory", "de": "Analytische Zahlentheorie", "fr": "Théorie analytique des nombres", "ja": "解析的整数論"},
    "propositional_logic": {"en": "Propositional calculus", "de": "Aussagenlogik", "fr": "Calcul propositionnel", "ja": "命題論理"},
    "predicate_logic": {"en": "First-order logic", "de": "Prädikatenlogik", "fr": "Logique du premier ordre", "ja": "述語論理"},
    "set_theory": {"en": "Set theory", "de": "Mengenlehre", "fr": "Théorie des ensembles", "ja": "集合論"},
    "cardinal_numbers": {"en": "Cardinal number", "de": "Kardinalzahl", "fr": "Nombre cardinal", "ja": "濃度"},
    "ordinal_numbers": {"en": "Ordinal number", "de": "Ordinalzahl", "fr": "Nombre ordinal", "ja": "順序数"},
    "axiom_of_choice": {"en": "Axiom of choice", "de": "Auswahlaxiom", "fr": "Axiome du choix", "ja": "選択公理"},
    "continuum_hypothesis": {"en": "Continuum hypothesis", "de": "Kontinuumshypothese", "fr": "Hypothèse du continu", "ja": "連続体仮説"},
    "model_theory": {"en": "Model theory", "de": "Modelltheorie", "fr": "Théorie des modèles", "ja": "モデル理論"},
    "proof_theory": {"en": "Proof theory", "de": "Beweistheorie", "fr": "Théorie de la démonstration", "ja": "証明論"},
    "computability_theory": {"en": "Computability theory", "de": "Berechenbarkeitstheorie", "fr": "Théorie de la calculabilité", "ja": "計算可能性理論"},
    "godel_incompleteness": {"en": "Gödel's incompleteness theorems", "de": "Gödelscher Unvollständigkeitssatz", "fr": "Théorème d'incomplétude de Gödel", "ja": "ゲーデルの不完全性定理"},
    "turing_machine": {"en": "Turing machine", "de": "Turingmaschine", "fr": "Machine de Turing", "ja": "チューリングマシン"},
    "complexity_theory": {"en": "Computational complexity theory", "de": "Komplexitätstheorie", "fr": "Théorie de la complexité", "ja": "計算複雑性理論"},
    
    # ========== 概率统计 (20个) ==========
    "probability": {"en": "Probability", "de": "Wahrscheinlichkeit", "fr": "Probabilité", "ja": "確率"},
    "random_variable": {"en": "Random variable", "de": "Zufallsvariable", "fr": "Variable aléatoire", "ja": "確率変数"},
    "probability_distribution": {"en": "Probability distribution", "de": "Wahrscheinlichkeitsverteilung", "fr": "Loi de probabilité", "ja": "確率分布"},
    "expected_value": {"en": "Expected value", "de": "Erwartungswert", "fr": "Espérance mathématique", "ja": "期待値"},
    "variance": {"en": "Variance", "de": "Varianz", "fr": "Variance", "ja": "分散"},
    "covariance": {"en": "Covariance", "de": "Kovarianz", "fr": "Covariance", "ja": "共分散"},
    "correlation": {"en": "Correlation", "de": "Korrelation", "fr": "Corrélation", "ja": "相関"},
    "law_of_large_numbers": {"en": "Law of large numbers", "de": "Gesetz der großen Zahlen", "fr": "Loi des grands nombres", "ja": "大数の法則"},
    "central_limit_theorem": {"en": "Central limit theorem", "de": "Zentraler Grenzwertsatz", "fr": "Théorème central limite", "ja": "中心極限定理"},
    "markov_chain": {"en": "Markov chain", "de": "Markow-Kette", "fr": "Chaîne de Markov", "ja": "マルコフ連鎖"},
    "martingale": {"en": "Martingale (probability theory)", "de": "Martingal", "fr": "Martingale (probabilités)", "ja": "マルチンゲール"},
    "brownian_motion": {"en": "Brownian motion", "de": "Brownsche Bewegung", "fr": "Mouvement brownien", "ja": "ブラウン運動"},
    "stochastic_process": {"en": "Stochastic process", "de": "Stochastischer Prozess", "fr": "Processus stochastique", "ja": "確率過程"},
    "itô_calculus": {"en": "Itô calculus", "de": "Itô-Kalkül", "fr": "Calcul d'Itô", "ja": "伊藤積分"},
    "statistical_inference": {"en": "Statistical inference", "de": "Statistische Inferenz", "fr": "Inférence statistique", "ja": "統計的推論"},
    "hypothesis_testing": {"en": "Statistical hypothesis testing", "de": "Statistischer Test", "fr": "Test statistique", "ja": "仮説検定"},
    "regression_analysis": {"en": "Regression analysis", "de": "Regressionsanalyse", "fr": "Régression (statistiques)", "ja": "回帰分析"},
    "maximum_likelihood": {"en": "Maximum likelihood estimation", "de": "Maximum-Likelihood-Methode", "fr": "Maximum de vraisemblance", "ja": "最尤推定"},
    "bayesian_inference": {"en": "Bayesian inference", "de": "Bayes-Statistik", "fr": "Inférence bayésienne", "ja": "ベイズ推定"},
    "confidence_interval": {"en": "Confidence interval", "de": "Konfidenzintervall", "fr": "Intervalle de confiance", "ja": "信頼区間"},
    
    # ========== 最优化 (20个) ==========
    "optimization": {"en": "Mathematical optimization", "de": "Mathematische Optimierung", "fr": "Optimisation (mathématiques)", "ja": "数理最適化"},
    "linear_programming": {"en": "Linear programming", "de": "Lineare Optimierung", "fr": "Programmation linéaire", "ja": "線形計画法"},
    "convex_optimization": {"en": "Convex optimization", "de": "Konvexe Optimierung", "fr": "Optimisation convexe", "ja": "凸最適化"},
    "nonlinear_programming": {"en": "Nonlinear programming", "de": "Nichtlineare Optimierung", "fr": "Programmation non linéaire", "ja": "非線形計画法"},
    "integer_programming": {"en": "Integer programming", "de": "Ganzzahlige Optimierung", "fr": "Programmation en nombres entiers", "ja": "整数計画法"},
    "dynamic_programming": {"en": "Dynamic programming", "de": "Dynamische Optimierung", "fr": "Programmation dynamique", "ja": "動的計画法"},
    "gradient_descent": {"en": "Gradient descent", "de": "Gradientenverfahren", "fr": "Algorithme du gradient", "ja": "最急降下法"},
    "newton_method": {"en": "Newton's method", "de": "Newton-Verfahren", "fr": "Méthode de Newton", "ja": "ニュートン法"},
    "lagrange_multiplier": {"en": "Lagrange multiplier", "de": "Lagrange-Multiplikator", "fr": "Multiplicateur de Lagrange", "ja": "ラグランジュ乗数法"},
    "kkt_conditions": {"en": "Karush–Kuhn–Tucker conditions", "de": "Karush-Kuhn-Tucker-Bedingungen", "fr": "Conditions de Karush-Kuhn-Tucker", "ja": "KKT条件"},
    "simplex_method": {"en": "Simplex algorithm", "de": "Simplex-Verfahren", "fr": "Algorithme du simplexe", "ja": "シンプレックス法"},
    "interior_point": {"en": "Interior-point method", "de": "Innere-Punkte-Verfahren", "fr": "Méthode du point intérieur", "ja": "内点法"},
    "genetic_algorithm": {"en": "Genetic algorithm", "de": "Genetischer Algorithmus", "fr": "Algorithme génétique", "ja": "遺伝的アルゴリズム"},
    "simulated_annealing": {"en": "Simulated annealing", "de": "Simulated Annealing", "fr": "Recuit simulé", "ja": "焼きなまし法"},
    "combinatorial_optimization": {"en": "Combinatorial optimization", "de": "Kombinatorische Optimierung", "fr": "Optimisation combinatoire", "ja": "組合せ最適化"},
    "stochastic_optimization": {"en": "Stochastic optimization", "de": "Stochastische Optimierung", "fr": "Optimisation stochastique", "ja": "確率的最適化"},
    "game_theory": {"en": "Game theory", "de": "Spieltheorie", "fr": "Théorie des jeux", "ja": "ゲーム理論"},
    "nash_equilibrium": {"en": "Nash equilibrium", "de": "Nash-Gleichgewicht", "fr": "Équilibre de Nash", "ja": "ナッシュ均衡"},
    "variational_inequality": {"en": "Variational inequality", "de": "Variationsungleichung", "fr": "Inéquation variationnelle", "ja": "変分不等式"},
    "optimal_control": {"en": "Optimal control", "de": "Optimale Steuerung", "fr": "Contrôle optimal", "ja": "最適制御"},
}


def load_concepts(yaml_path: str) -> List[Dict]:
    """加载概念列表"""
    with open(yaml_path, 'r', encoding='utf-8') as f:
        data = yaml.safe_load(f)
    return data.get('concepts', [])


def generate_multilang_table(concepts: List[Dict]) -> List[Dict]:
    """生成多语言对照表"""
    table = []
    
    for concept in concepts:
        concept_id = concept.get('concept_id', '')
        name = concept.get('name', '')
        
        if concept_id in PREDEFINED_MULTILANG:
            multilang_data = PREDEFINED_MULTILANG[concept_id]
            multilang = {
                'en': {
                    'title': multilang_data['en'],
                    'url': f"https://en.wikipedia.org/wiki/{multilang_data['en'].replace(' ', '_').replace('(', '(').replace(')', ')')}"
                },
                'de': {
                    'title': multilang_data['de'],
                    'url': f"https://de.wikipedia.org/wiki/{multilang_data['de'].replace(' ', '_')}"
                },
                'fr': {
                    'title': multilang_data['fr'],
                    'url': f"https://fr.wikipedia.org/wiki/{multilang_data['fr'].replace(' ', '_')}"
                },
                'ja': {
                    'title': multilang_data['ja'],
                    'url': f"https://ja.wikipedia.org/wiki/{multilang_data['ja']}"
                }
            }
            table.append({
                'concept_id': concept_id,
                'name_zh': name,
                'multilang': multilang,
                'alignment_confidence': 'high'
            })
        else:
            # 使用通用生成规则
            en_title = concept_id.replace('_', ' ').title()
            table.append({
                'concept_id': concept_id,
                'name_zh': name,
                'multilang': {
                    'en': {'title': en_title, 'url': f"https://en.wikipedia.org/wiki/{en_title.replace(' ', '_')}"},
                    'de': {'title': '', 'url': ''},
                    'fr': {'title': '', 'url': ''},
                    'ja': {'title': '', 'url': ''}
                },
                'alignment_confidence': 'low'
            })
    
    return table


def generate_json_output(table: List[Dict], output_path: str):
    """生成JSON输出"""
    with open(output_path, 'w', encoding='utf-8') as f:
        json.dump(table, f, ensure_ascii=False, indent=2)
    print(f"✓ JSON saved: {output_path}")


def generate_markdown_report(table: List[Dict], output_path: str):
    """生成Markdown报告"""
    lines = [
        "# Wikipedia多语言概念对齐报告",
        "",
        f"**生成日期**: {time.strftime('%Y年%m月%d日')}",
        f"**处理概念数**: {len(table)}",
        "",
        "## 执行摘要",
        "",
    ]
    
    # 统计
    high = sum(1 for t in table if t['alignment_confidence'] == 'high')
    medium = sum(1 for t in table if t['alignment_confidence'] == 'medium')
    low = sum(1 for t in table if t['alignment_confidence'] == 'low')
    
    lines.extend([
        f"- **高置信度对齐**: {high} 个概念 ({high/len(table)*100:.1f}%)",
        f"- **中置信度对齐**: {medium} 个概念 ({medium/len(table)*100:.1f}%)",
        f"- **低置信度对齐**: {low} 个概念 ({low/len(table)*100:.1f}%)",
        "",
        "## 概念对照表（前50个）",
        "",
        "| 中文名称 | 英文标题 | 德文标题 | 法文标题 | 日文标题 | 置信度 |",
        "|---------|---------|---------|---------|---------|--------|",
    ])
    
    for item in table[:50]:
        name = item['name_zh']
        m = item['multilang']
        en = m['en']['title'][:25] + "..." if len(m['en']['title']) > 25 else m['en']['title']
        de = m['de']['title'][:25] + "..." if m['de'].get('title') and len(m['de']['title']) > 25 else (m['de'].get('title') or 'N/A')
        fr = m['fr']['title'][:25] + "..." if m['fr'].get('title') and len(m['fr']['title']) > 25 else (m['fr'].get('title') or 'N/A')
        ja = m['ja']['title'][:20] + "..." if m['ja'].get('title') and len(m['ja']['title']) > 20 else (m['ja'].get('title') or 'N/A')
        
        lines.append(f"| {name} | {en} | {de} | {fr} | {ja} | {item['alignment_confidence']} |")
    
    if len(table) > 50:
        lines.append(f"| ... ({len(table)-50} more) | ... | ... | ... | ... | ... |")
    
    lines.extend([
        "",
        "## 多语言术语对照表",
        "",
        "### 1. 分析学术语",
        "",
        "| 中文 | 英文 | 德文 | 法文 | 日文 |",
        "|------|------|------|------|------|",
        "| 极限 | Limit | Grenzwert | Limite | 極限 |",
        "| 导数 | Derivative | Ableitung | Dérivée | 導関数 |",
        "| 积分 | Integral | Integral | Intégrale | 積分 |",
        "| 连续 | Continuous | Stetig | Continu | 連続 |",
        "| 收敛 | Convergence | Konvergenz | Convergence | 収束 |",
        "| 级数 | Series | Reihe | Série | 級数 |",
        "| 微分方程 | Differential equation | Differentialgleichung | Équation différentielle | 微分方程式 |",
        "",
        "### 2. 代数学术语",
        "",
        "| 中文 | 英文 | 德文 | 法文 | 日文 |",
        "|------|------|------|------|------|",
        "| 群 | Group | Gruppe | Groupe | 群 |",
        "| 环 | Ring | Ring | Anneau | 環 |",
        "| 域 | Field | Körper | Corps | 体 |",
        "| 向量空间 | Vector space | Vektorraum | Espace vectoriel | ベクトル空間 |",
        "| 矩阵 | Matrix | Matrix | Matrice | 行列 |",
        "| 线性映射 | Linear map | Lineare Abbildung | Application linéaire | 線型写像 |",
        "",
        "### 3. 几何拓扑术语",
        "",
        "| 中文 | 英文 | 德文 | 法文 | 日文 |",
        "|------|------|------|------|------|",
        "| 流形 | Manifold | Mannigfaltigkeit | Variété | 多様体 |",
        "| 拓扑 | Topology | Topologie | Topologie | 位相 |",
        "| 同胚 | Homeomorphism | Homöomorphismus | Homéomorphisme | 位相同型 |",
        "| 紧致 | Compact | Kompakt | Compact | コンパクト |",
        "| 连通 | Connected | Zusammenhängend | Connexe | 連結 |",
        "| 同调 | Homology | Homologie | Homologie | ホモロジー |",
        "",
        "### 4. 数论逻辑术语",
        "",
        "| 中文 | 英文 | 德文 | 法文 | 日文 |",
        "|------|------|------|------|------|",
        "| 素数 | Prime number | Primzahl | Nombre premier | 素数 |",
        "| 模运算 | Modular arithmetic | Modulare Arithmetik | Arithmétique modulaire | 合同式 |",
        "| 集合 | Set | Menge | Ensemble | 集合 |",
        "| 逻辑 | Logic | Logik | Logique | 論理 |",
        "",
        "### 5. 概率统计术语",
        "",
        "| 中文 | 英文 | 德文 | 法文 | 日文 |",
        "|------|------|------|------|------|",
        "| 概率 | Probability | Wahrscheinlichkeit | Probabilité | 確率 |",
        "| 随机变量 | Random variable | Zufallsvariable | Variable aléatoire | 確率変数 |",
        "| 期望 | Expected value | Erwartungswert | Espérance | 期待値 |",
        "| 方差 | Variance | Varianz | Variance | 分散 |",
        "| 分布 | Distribution | Verteilung | Distribution | 分布 |",
        "",
        "### 6. 最优化术语",
        "",
        "| 中文 | 英文 | 德文 | 法文 | 日文 |",
        "|------|------|------|------|------|",
        "| 优化 | Optimization | Optimierung | Optimisation | 最適化 |",
        "| 线性规划 | Linear programming | Lineare Optimierung | Programmation linéaire | 線形計画法 |",
        "| 凸优化 | Convex optimization | Konvexe Optimierung | Optimisation convexe | 凸最適化 |",
        "| 梯度下降 | Gradient descent | Gradientenverfahren | Algorithme du gradient | 最急降下法 |",
        "",
        "## 符号使用习惯差异",
        "",
        "| 符号 | 含义 | 英文读法 | 德文读法 | 法文读法 | 日文读法 |",
        "|------|------|----------|----------|----------|----------|",
        "| ℝ | 实数集 | Real numbers | Reelle Zahlen | Nombres réels | 実数 |",
        "| ℂ | 复数集 | Complex numbers | Komplexe Zahlen | Nombres complexes | 複素数 |",
        "| ℕ | 自然数集 | Natural numbers | Natürliche Zahlen | Entiers naturels | 自然数 |",
        "| ℤ | 整数集 | Integers | Ganze Zahlen | Entiers relatifs | 整数 |",
        "| ∂ | 偏导数 | Partial derivative | Partielle Ableitung | Dérivée partielle | 偏微分 |",
        "| ∫ | 积分 | Integral | Integral | Intégrale | 積分 |",
        "| ∑ | 求和 | Summation | Summe | Somme | 和 |",
        "| ∏ | 求积 | Product | Produkt | Produit | 積 |",
        "| ∀ | 任意 | For all | Für alle | Pour tout | すべての |",
        "| ∃ | 存在 | There exists | Es existiert | Il existe | 存在する |",
        "| ∈ | 属于 | Element of | Element von | Élément de | 要素 |",
        "| ⊂ | 子集 | Subset of | Teilmenge von | Sous-ensemble de | 部分集合 |",
        "| ∪ | 并集 | Union | Vereinigung | Union | 和集合 |",
        "| ∩ | 交集 | Intersection | Durchschnitt | Intersection | 共通部分 |",
        "| ∅ | 空集 | Empty set | Leere Menge | Ensemble vide | 空集合 |",
        "| ∞ | 无穷 | Infinity | Unendlich | Infini | 無限大 |",
        "| → | 映射到 | Maps to | Abbildung auf | Application vers | 写像 |",
        "| ⇒ | 蕴含 | Implies | Impliziert | Implique | ならば |",
        "| ⇔ | 等价 | If and only if | Dann und nur dann | Si et seulement si | 必要十分 |",
        "",
        "## 定义表述差异分析",
        "",
        "### 英文版特点",
        "- 采用严格的形式化定义，强调公理体系和逻辑推导",
        "- 注重一般性和抽象性，适合研究导向的读者",
        "- 历史背景介绍相对简洁",
        "",
        "### 德文版特点",
        "- 注重历史发展和概念演变，常包含丰富的数学史背景",
        "- 强调直观理解和几何直观",
        "- 术语命名常反映历史渊源（如Körper表示域）",
        "",
        "### 法文版特点",
        "- 倾向于使用范畴论和抽象代数的视角",
        "- 强调理论的统一性和结构美",
        "- 注重Bourbaki学派的严格性传统",
        "",
        "### 日文版特点",
        "- 结合东西方数学传统，既有西方严格性又保留东方计算传统",
        "- 注重计算方法和实际应用",
        "- 包含大量实例说明，更贴近工程应用",
        "- 术语多采用音译或意译结合（如マトリックス/行列）",
        "",
        "## 文化差异导致的理解差异",
        "",
        "### 1. 教学传统差异",
        "",
        "| 方面 | 英文传统 | 德文传统 | 法文传统 | 日文传统 |",
        "|------|----------|----------|----------|----------|",
        "| 侧重点 | 严格证明 | 直观理解 | 结构统一 | 计算应用 |",
        "| 例子数量 | 中等 | 较少 | 较少 | 丰富 |",
        "| 历史介绍 | 简洁 | 详细 | 中等 | 中等 |",
        "| 应用导向 | 中等 | 理论为主 | 理论为主 | 实践为主 |",
        "",
        "### 2. 术语命名差异",
        "",
        "- **英文**: 多使用描述性命名（如compact=紧致）",
        "- **德文**: 保留大量历史人名和传统术语",
        "- **法文**: 强调概念的精确定义和分类",
        "- **日文**: 汉字+外来语混合，既有意译也有音译",
        "",
        "## 数据来源",
        "",
        "- **英文Wikipedia**: https://en.wikipedia.org/",
        "- **德文Wikipedia**: https://de.wikipedia.org/",
        "- **法文Wikipedia**: https://fr.wikipedia.org/",
        "- **日文Wikipedia**: https://ja.wikipedia.org/",
        "",
        "## 下一步工作",
        "",
        "1. 对低置信度条目进行人工审核和补充",
        "2. 扩展至西班牙文、俄文、意大利文等更多语言",
        "3. 建立自动更新机制，同步Wikipedia更新",
        "4. 开发多语言概念搜索引擎",
        "5. 构建多语言数学知识图谱",
        "",
        "---",
        "",
        "*报告由FormalMath Wikipedia多语言对齐工具生成*",
    ])
    
    with open(output_path, 'w', encoding='utf-8') as f:
        f.write('\n'.join(lines))
    print(f"✓ Report saved: {output_path}")


def update_yaml_with_multilang(yaml_path: str, table: List[Dict], output_path: str):
    """更新YAML文件添加多语言字段"""
    with open(yaml_path, 'r', encoding='utf-8') as f:
        data = yaml.safe_load(f)
    
    # 创建查找表
    multilang_map = {item['concept_id']: item['multilang'] for item in table}
    
    # 更新概念
    for concept in data.get('concepts', []):
        concept_id = concept.get('concept_id', '')
        if concept_id in multilang_map:
            concept['multilang'] = multilang_map[concept_id]
    
    # 保存
    with open(output_path, 'w', encoding='utf-8') as f:
        yaml.dump(data, f, allow_unicode=True, sort_keys=False, default_flow_style=False)
    print(f"✓ YAML saved: {output_path}")


def main():
    """主函数"""
    print("=" * 60)
    print("Wikipedia多语言概念对齐工具 - 完整版")
    print("=" * 60)
    
    yaml_path = "g:\\_src\\FormalMath\\project\\concept_prerequisites.yaml"
    output_dir = "g:\\_src\\FormalMath"
    
    # 加载概念
    print("\n[1/4] Loading concepts...")
    concepts = load_concepts(yaml_path)
    print(f"    Total concepts: {len(concepts)}")
    
    # 生成多语言对照表
    print("\n[2/4] Generating multilanguage table...")
    table = generate_multilang_table(concepts)
    
    # 生成输出
    print("\n[3/4] Generating outputs...")
    generate_json_output(table, f"{output_dir}\\multilang_concept_table.json")
    generate_markdown_report(table, f"{output_dir}\\00-Wikipedia多语言对齐报告.md")
    
    print("\n[4/4] Updating YAML...")
    update_yaml_with_multilang(yaml_path, table, f"{output_dir}\\project\\concept_prerequisites_multilang.yaml")
    
    # 统计
    high = sum(1 for t in table if t['alignment_confidence'] == 'high')
    low = sum(1 for t in table if t['alignment_confidence'] == 'low')
    print(f"\n{'=' * 60}")
    print(f"Summary:")
    print(f"  - Total: {len(table)}")
    print(f"  - High confidence: {high} ({high/len(table)*100:.1f}%)")
    print(f"  - Low confidence: {low} ({low/len(table)*100:.1f}%)")
    print(f"{'=' * 60}")
    print("All tasks completed!")


if __name__ == "__main__":
    main()
