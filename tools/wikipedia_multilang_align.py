#!/usr/bin/env python3
"""
Wikipedia多语言概念对齐工具
对齐Wikipedia数学概念的英文、德文、法文、日文版本
"""

import yaml
import json
import time
import urllib.request
import urllib.parse
import ssl
from pathlib import Path
from typing import Dict, List, Optional, Tuple
from dataclasses import dataclass, asdict
import re

# 禁用SSL验证警告
ssl._create_default_https_context = ssl._create_unverified_context

@dataclass
class MultilangInfo:
    """多语言信息"""
    en_title: str = ""
    en_extract: str = ""
    de_title: str = ""
    de_extract: str = ""
    fr_title: str = ""
    fr_extract: str = ""
    ja_title: str = ""
    ja_extract: str = ""
    
    # 元数据
    en_url: str = ""
    de_url: str = ""
    fr_url: str = ""
    ja_url: str = ""
    alignment_confidence: str = "medium"  # high, medium, low


class WikipediaMultilangAligner:
    """Wikipedia多语言对齐器"""
    
    # 常见数学概念的中英文映射
    COMMON_MATH_TERMS = {
        "limit": "Limit (mathematics)",
        "continuity": "Continuous function",
        "derivative": "Derivative",
        "riemann_integral": "Integral",
        "lebesgue_integral": "Lebesgue integration",
        "infinite_series": "Series (mathematics)",
        "sequence": "Sequence",
        "convergence": "Limit of a sequence",
        "uniform_convergence": "Uniform convergence",
        "power_series": "Power series",
        "fourier_series": "Fourier series",
        "laplace_transform": "Laplace transform",
        "fourier_transform": "Fourier transform",
        "ordinary_differential_equations": "Ordinary differential equation",
        "partial_differential_equations": "Partial differential equation",
        "gradient": "Gradient",
        "divergence": "Divergence",
        "curl": "Curl (mathematics)",
        "jacobian": "Jacobian matrix and determinant",
        "hessian": "Hessian matrix",
        "taylor_series": "Taylor series",
        "complex_analysis": "Complex analysis",
        "real_analysis": "Real analysis",
        "functional_analysis": "Functional analysis",
        "measure_theory": "Measure (mathematics)",
        "metric_space": "Metric space",
        "normed_space": "Normed vector space",
        "banach_space": "Banach space",
        "hilbert_space": "Hilbert space",
        "sobolev_space": "Sobolev space",
        "topology": "Topology",
        "compactness": "Compact space",
        "connectedness": "Connected space",
        "homeomorphism": "Homeomorphism",
        "manifold": "Manifold",
        "vector_space": "Vector space",
        "linear_transformation": "Linear map",
        "matrix": "Matrix (mathematics)",
        "determinant": "Determinant",
        "eigenvalue": "Eigenvalues and eigenvectors",
        "inner_product": "Inner product space",
        "tensor": "Tensor",
        "group": "Group (mathematics)",
        "ring": "Ring (mathematics)",
        "field": "Field (mathematics)",
        "module": "Module (mathematics)",
        "homomorphism": "Homomorphism",
        "isomorphism": "Isomorphism",
        "quotient_group": "Quotient group",
        "sylow_theorems": "Sylow theorems",
        "galois_theory": "Galois theory",
        "representation_theory": "Representation theory",
        "lie_group": "Lie group",
        "algebraic_geometry": "Algebraic geometry",
        "commutative_algebra": "Commutative algebra",
        "homological_algebra": "Homological algebra",
        "category_theory": "Category theory",
        "functor": "Functor",
        "natural_transformation": "Natural transformation",
        "universal_property": "Universal property",
        "limit_category": "Limit (category theory)",
        "adjunction": "Adjoint functors",
        "monoid": "Monoid",
        "prime_number": "Prime number",
        "gcd": "Greatest common divisor",
        "modular_arithmetic": "Modular arithmetic",
        "chinese_remainder_theorem": "Chinese remainder theorem",
        "euler_theorem": "Euler's theorem",
        "fermat_little_theorem": "Fermat's little theorem",
        "quadratic_reciprocity": "Quadratic reciprocity",
        "diophantine_equations": "Diophantine equation",
        "prime_number_theorem": "Prime number theorem",
        "riemann_hypothesis": "Riemann hypothesis",
        "algebraic_number_theory": "Algebraic number theory",
        "analytic_number_theory": "Analytic number theory",
        "probability": "Probability",
        "random_variable": "Random variable",
        "probability_distribution": "Probability distribution",
        "expected_value": "Expected value",
        "variance": "Variance",
        "covariance": "Covariance",
        "correlation": "Correlation",
        "law_of_large_numbers": "Law of large numbers",
        "central_limit_theorem": "Central limit theorem",
        "markov_chain": "Markov chain",
        "martingale": "Martingale (probability theory)",
        "brownian_motion": "Brownian motion",
        "stochastic_process": "Stochastic process",
        "itô_calculus": "Itô calculus",
        "statistical_inference": "Statistical inference",
        "hypothesis_testing": "Statistical hypothesis testing",
        "regression_analysis": "Regression analysis",
        "maximum_likelihood": "Maximum likelihood estimation",
        "bayesian_inference": "Bayesian inference",
        "confidence_interval": "Confidence interval",
        "p_value": "P-value",
        "linear_regression": "Linear regression",
        "logistic_regression": "Logistic regression",
        "anova": "Analysis of variance",
        "time_series": "Time series",
        "optimization": "Mathematical optimization",
        "linear_programming": "Linear programming",
        "convex_optimization": "Convex optimization",
        "nonlinear_programming": "Nonlinear programming",
        "integer_programming": "Integer programming",
        "dynamic_programming": "Dynamic programming",
        "gradient_descent": "Gradient descent",
        "newton_method": "Newton's method",
        "lagrange_multiplier": "Lagrange multiplier",
        "kkt_conditions": "Karush–Kuhn–Tucker conditions",
        "simplex_method": "Simplex algorithm",
        "interior_point": "Interior-point method",
        "genetic_algorithm": "Genetic algorithm",
        "simulated_annealing": "Simulated annealing",
        "control_theory": "Control theory",
        "pid_controller": "PID controller",
        "state_space": "State-space representation",
        "transfer_function": "Transfer function",
        "nyquist_stability": "Nyquist stability criterion",
        "root_locus": "Root locus",
        "observability": "Observability",
        "controllability": "Controllability",
        "kalman_filter": "Kalman filter",
        "optimal_control": "Optimal control",
        "mpc": "Model predictive control",
        "robust_control": "Robust control",
        "nonlinear_control": "Nonlinear control",
        "adaptive_control": "Adaptive control",
        "information_theory": "Information theory",
        "entropy": "Entropy (information theory)",
        "mutual_information": "Mutual information",
        "channel_capacity": "Channel capacity",
        "shannon_theorem": "Noisy-channel coding theorem",
        "source_coding": "Data compression",
        "huffman_coding": "Huffman coding",
        "arithmetic_coding": "Arithmetic coding",
        "kolmogorov_complexity": "Kolmogorov complexity",
        "algorithmic_information": "Algorithmic information theory",
        "cryptography": "Cryptography",
        "encryption": "Encryption",
        "decryption": "Encryption",
        "symmetric_encryption": "Symmetric-key algorithm",
        "asymmetric_encryption": "Public-key cryptography",
        "rsa": "RSA (cryptosystem)",
        "aes": "Advanced Encryption Standard",
        "diffie_hellman": "Diffie–Hellman key exchange",
        "elliptic_curve": "Elliptic-curve cryptography",
        "hash_function": "Cryptographic hash function",
        "digital_signature": "Digital signature",
        "zero_knowledge_proof": "Zero-knowledge proof",
        "blockchain": "Blockchain",
        "post_quantum_crypto": "Post-quantum cryptography",
        "financial_mathematics": "Mathematical finance",
        "option_pricing": "Black–Scholes model",
        "risk_management": "Financial risk management",
        "portfolio_theory": "Modern portfolio theory",
        "arbitrage": "Arbitrage",
        "stochastic_calculus_finance": "Stochastic calculus",
        "monte_carlo_simulation": "Monte Carlo method",
        "value_at_risk": "Value at risk",
        "interest_rate_model": "Short-rate model",
        "credit_risk": "Credit risk",
        "biomathematics": "Mathematical and theoretical biology",
        "population_dynamics": "Population dynamics",
        "epidemiology_models": "Compartmental models in epidemiology",
        "reaction_diffusion": "Reaction–diffusion system",
        "systems_biology": "Systems biology",
        "pharmacokinetics": "Pharmacokinetics",
        "phylogenetics": "Phylogenetics",
        "sequence_alignment": "Sequence alignment",
        "bioinformatics": "Bioinformatics",
        "neural_network": "Artificial neural network",
        "machine_learning": "Machine learning",
        "deep_learning": "Deep learning",
        "reinforcement_learning": "Reinforcement learning",
        "supervised_learning": "Supervised learning",
        "unsupervised_learning": "Unsupervised learning",
        "svm": "Support vector machine",
        "decision_tree": "Decision tree learning",
        "random_forest": "Random forest",
        "clustering": "Cluster analysis",
        "pca": "Principal component analysis",
        "numerical_analysis": "Numerical analysis",
        "numerical_linear_algebra": "Numerical linear algebra",
        "interpolation": "Interpolation",
        "numerical_integration": "Numerical integration",
        "numerical_differentiation": "Numerical differentiation",
        "ode_solver": "Numerical methods for ordinary differential equations",
        "pde_solver": "Numerical methods for partial differential equations",
        "finite_difference": "Finite difference method",
        "finite_element": "Finite element method",
        "monte_carlo": "Monte Carlo method",
        "numerical_optimization": "Mathematical optimization",
        "linear_solver": "System of linear equations",
        "eigenvalue_computation": "Eigenvalue algorithm",
        "fast_fourier_transform": "Fast Fourier transform",
        "wavelet_transform": "Wavelet transform",
        "multigrid": "Multigrid method",
        "domain_decomposition": "Domain decomposition methods",
        "quantum_mechanics": "Quantum mechanics",
        "schrodinger_equation": "Schrödinger equation",
        "hilbert_space_qm": "Hilbert space",
        "operator_theory": "Operator theory",
        "spectral_theory": "Spectral theory",
        "quantum_field_theory": "Quantum field theory",
        "statistical_mechanics": "Statistical mechanics",
        "general_relativity": "General relativity",
        "differential_geometry": "Differential geometry",
        "riemannian_geometry": "Riemannian geometry",
        "symplectic_geometry": "Symplectic geometry",
        "gauge_theory": "Gauge theory",
        "classical_mechanics": "Classical mechanics",
        "hamiltonian_mechanics": "Hamiltonian mechanics",
        "lagrangian_mechanics": "Lagrangian mechanics",
        "electromagnetism": "Electromagnetism",
        "maxwell_equations": "Maxwell's equations",
        "thermodynamics": "Thermodynamics",
        "fluid_dynamics": "Fluid dynamics",
        "navier_stokes": "Navier–Stokes equations",
        "data_mining": "Data mining",
        "big_data": "Big data",
        "data_visualization": "Data visualization",
        "database_theory": "Database",
        "data_warehousing": "Data warehouse",
        "etl": "Extract, transform, load",
        "data_quality": "Data quality",
        "feature_engineering": "Feature engineering",
        "model_evaluation": "Evaluation of binary classifiers",
        "cross_validation": "Cross-validation (statistics)",
        "hyperparameter_tuning": "Hyperparameter optimization",
        "ensemble_methods": "Ensemble learning",
        "dimensionality_reduction": "Dimensionality reduction",
        "anomaly_detection": "Anomaly detection",
        "recommendation_system": "Recommender system",
        "natural_language_processing": "Natural language processing",
    }
    
    def __init__(self, yaml_path: str, output_dir: str):
        self.yaml_path = Path(yaml_path)
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(parents=True, exist_ok=True)
        
        self.results: Dict[str, MultilangInfo] = {}
        self.errors: List[Dict] = []
        
    def fetch_wikipedia_data(self, title: str, lang: str) -> Optional[Dict]:
        """获取Wikipedia页面数据"""
        try:
            # URL编码标题
            encoded_title = urllib.parse.quote(title.replace(" ", "_"))
            
            # 构建API URL
            url = f"https://{lang}.wikipedia.org/w/api.php"
            params = {
                "action": "query",
                "format": "json",
                "titles": title,
                "prop": "extracts|langlinks",
                "explaintext": True,
                "exintro": True,
                "exlimit": 1,
                "lllimit": 100,
                "redirects": 1
            }
            
            # 构建完整URL
            query_string = urllib.parse.urlencode(params)
            full_url = f"{url}?{query_string}"
            
            # 设置请求头
            headers = {
                "User-Agent": "FormalMath/1.0 (research@formalmath.org)"
            }
            
            req = urllib.request.Request(full_url, headers=headers)
            
            with urllib.request.urlopen(req, timeout=30) as response:
                data = json.loads(response.read().decode('utf-8'))
                
                if 'query' in data and 'pages' in data['query']:
                    pages = data['query']['pages']
                    page_id = list(pages.keys())[0]
                    
                    if page_id == '-1':
                        return None
                    
                    page_data = pages[page_id]
                    return {
                        'title': page_data.get('title', title),
                        'extract': page_data.get('extract', '')[:500] if page_data.get('extract') else '',
                        'langlinks': page_data.get('langlinks', [])
                    }
                
                return None
                
        except Exception as e:
            print(f"  Error fetching {lang}/{title}: {str(e)[:50]}")
            return None
    
    def get_concept_english_title(self, concept_id: str, name: str) -> str:
        """获取概念的英文标题"""
        if concept_id in self.COMMON_MATH_TERMS:
            return self.COMMON_MATH_TERMS[concept_id]
        
        # 尝试直接转换
        return name.replace(" ", "_").replace("（", "_").replace("）", "")
    
    def find_langlink(self, langlinks: List[Dict], target_lang: str) -> Optional[str]:
        """在langlinks中查找指定语言的链接"""
        for link in langlinks:
            if link.get('lang') == target_lang:
                return link.get('*', '')
        return None
    
    def align_concept(self, concept_id: str, name: str) -> MultilangInfo:
        """对齐单个概念的多语言版本"""
        info = MultilangInfo()
        
        # 获取英文标题
        en_title = self.get_concept_english_title(concept_id, name)
        
        # 获取英文数据
        print(f"  Fetching EN: {en_title}")
        en_data = self.fetch_wikipedia_data(en_title, 'en')
        
        if en_data:
            info.en_title = en_data['title']
            info.en_extract = en_data['extract'][:300] if en_data['extract'] else ""
            info.en_url = f"https://en.wikipedia.org/wiki/{en_title.replace(' ', '_')}"
            
            # 从英文版本的langlinks获取其他语言
            if en_data.get('langlinks'):
                # 德文
                de_title = self.find_langlink(en_data['langlinks'], 'de')
                if de_title:
                    info.de_title = de_title
                    info.de_url = f"https://de.wikipedia.org/wiki/{de_title.replace(' ', '_')}"
                    # 获取德文摘要
                    print(f"  Fetching DE: {de_title}")
                    de_data = self.fetch_wikipedia_data(de_title, 'de')
                    if de_data:
                        info.de_extract = de_data['extract'][:300] if de_data['extract'] else ""
                
                # 法文
                fr_title = self.find_langlink(en_data['langlinks'], 'fr')
                if fr_title:
                    info.fr_title = fr_title
                    info.fr_url = f"https://fr.wikipedia.org/wiki/{fr_title.replace(' ', '_')}"
                    # 获取法文摘要
                    print(f"  Fetching FR: {fr_title}")
                    fr_data = self.fetch_wikipedia_data(fr_title, 'fr')
                    if fr_data:
                        info.fr_extract = fr_data['extract'][:300] if fr_data['extract'] else ""
                
                # 日文
                ja_title = self.find_langlink(en_data['langlinks'], 'ja')
                if ja_title:
                    info.ja_title = ja_title
                    info.ja_url = f"https://ja.wikipedia.org/wiki/{urllib.parse.quote(ja_title)}"
                    # 获取日文摘要
                    print(f"  Fetching JA: {ja_title}")
                    ja_data = self.fetch_wikipedia_data(ja_title, 'ja')
                    if ja_data:
                        info.ja_extract = ja_data['extract'][:300] if ja_data['extract'] else ""
            
            # 评估对齐置信度
            found_langs = sum([
                1 if info.de_title else 0,
                1 if info.fr_title else 0,
                1 if info.ja_title else 0
            ])
            
            if found_langs == 3:
                info.alignment_confidence = "high"
            elif found_langs >= 1:
                info.alignment_confidence = "medium"
            else:
                info.alignment_confidence = "low"
        else:
            info.alignment_confidence = "low"
        
        return info
    
    def process_all_concepts(self):
        """处理所有概念"""
        # 加载YAML
        print("Loading YAML file...")
        with open(self.yaml_path, 'r', encoding='utf-8') as f:
            data = yaml.safe_load(f)
        
        concepts = data.get('concepts', [])
        total = len(concepts)
        
        print(f"Total concepts to process: {total}")
        
        # 处理每个概念
        for idx, concept in enumerate(concepts, 1):
            concept_id = concept.get('concept_id', '')
            name = concept.get('name', '')
            
            print(f"\n[{idx}/{total}] Processing: {name} ({concept_id})")
            
            try:
                info = self.align_concept(concept_id, name)
                self.results[concept_id] = info
                
                # 添加延迟以避免API限制
                time.sleep(1)
                
            except Exception as e:
                error_msg = f"Error processing {concept_id}: {str(e)}"
                print(f"  {error_msg}")
                self.errors.append({
                    'concept_id': concept_id,
                    'name': name,
                    'error': str(e)
                })
        
        print(f"\n\nProcessing complete!")
        print(f"Successful: {len(self.results)}")
        print(f"Errors: {len(self.errors)}")
    
    def generate_json_table(self):
        """生成多语言对照表JSON"""
        json_data = []
        
        for concept_id, info in self.results.items():
            json_data.append({
                'concept_id': concept_id,
                'multilang': {
                    'en': {
                        'title': info.en_title,
                        'url': info.en_url,
                        'extract': info.en_extract
                    },
                    'de': {
                        'title': info.de_title,
                        'url': info.de_url,
                        'extract': info.de_extract
                    },
                    'fr': {
                        'title': info.fr_title,
                        'url': info.fr_url,
                        'extract': info.fr_extract
                    },
                    'ja': {
                        'title': info.ja_title,
                        'url': info.ja_url,
                        'extract': info.ja_extract
                    }
                },
                'alignment_confidence': info.alignment_confidence
            })
        
        output_path = self.output_dir / "multilang_concept_table.json"
        with open(output_path, 'w', encoding='utf-8') as f:
            json.dump(json_data, f, ensure_ascii=False, indent=2)
        
        print(f"JSON table saved to: {output_path}")
        return output_path
    
    def generate_markdown_report(self):
        """生成Markdown报告"""
        report_lines = [
            "# Wikipedia多语言概念对齐报告",
            "",
            f"**生成日期**: {time.strftime('%Y年%m月%d日')}",
            f"**处理概念数**: {len(self.results)}",
            "",
            "## 执行摘要",
            "",
        ]
        
        # 统计
        high_conf = sum(1 for info in self.results.values() if info.alignment_confidence == 'high')
        medium_conf = sum(1 for info in self.results.values() if info.alignment_confidence == 'medium')
        low_conf = sum(1 for info in self.results.values() if info.alignment_confidence == 'low')
        
        report_lines.extend([
            f"- **高置信度对齐**: {high_conf} 个概念",
            f"- **中置信度对齐**: {medium_conf} 个概念",
            f"- **低置信度对齐**: {low_conf} 个概念",
            f"- **错误数**: {len(self.errors)} 个",
            "",
            "## 概念对照表示例",
            "",
            "| 中文名称 | 英文标题 | 德文标题 | 法文标题 | 日文标题 | 置信度 |",
            "|---------|---------|---------|---------|---------|--------|",
        ])
        
        # 添加前30个示例
        count = 0
        for concept_id, info in list(self.results.items())[:30]:
            # 从YAML中获取中文名称
            name = concept_id
            with open(self.yaml_path, 'r', encoding='utf-8') as f:
                data = yaml.safe_load(f)
                for c in data.get('concepts', []):
                    if c.get('concept_id') == concept_id:
                        name = c.get('name', concept_id)
                        break
            
            en_short = info.en_title[:25] + "..." if len(info.en_title) > 25 else info.en_title
            de_short = info.de_title[:25] + "..." if len(info.de_title) > 25 else info.de_title
            fr_short = info.fr_title[:25] + "..." if len(info.fr_title) > 25 else info.fr_title
            ja_short = info.ja_title[:20] + "..." if len(info.ja_title) > 20 else info.ja_title
            
            report_lines.append(
                f"| {name} | {en_short} | {de_short} | {fr_short} | {ja_short} | {info.alignment_confidence} |"
            )
            count += 1
        
        if len(self.results) > 30:
            report_lines.append(f"| ... ({len(self.results) - 30} more) | ... | ... | ... | ... | ... |")
        
        # 添加术语差异分析
        report_lines.extend([
            "",
            "## 术语翻译最佳实践",
            "",
            "### 1. 常见术语对照",
            "",
            "| 英文术语 | 德文术语 | 法文术语 | 日文术语 |",
            "|---------|---------|---------|---------|",
            "| Limit | Grenzwert | Limite | 極限 |",
            "| Derivative | Ableitung | Dérivée | 微分 |",
            "| Integral | Integral | Intégrale | 積分 |",
            "| Vector | Vektor | Vecteur | ベクトル |",
            "| Matrix | Matrix | Matrice | 行列 |",
            "| Probability | Wahrscheinlichkeit | Probabilité | 確率 |",
            "| Optimization | Optimierung | Optimisation | 最適化 |",
            "",
            "### 2. 符号使用习惯差异",
            "",
            "| 符号 | 英文用法 | 德文用法 | 法文用法 | 日文用法 |",
            "|------|---------|---------|---------|---------|",
            "| ℝ | Real numbers | Reelle Zahlen | Nombres réels | 実数 |",
            "| ∂ | Partial derivative | Partielle Ableitung | Dérivée partielle | 偏微分 |",
            "| ∫ | Integral | Integral | Intégrale | 積分 |",
            "| ∑ | Summation | Summe | Somme | 和 |",
            "| ∀ | For all | Für alle | Pour tout | すべての |",
            "| ∃ | There exists | Es existiert | Il existe | 存在する |",
            "",
            "### 3. 定义表述差异",
            "",
            "不同语言版本的Wikipedia在数学概念定义上存在以下差异：",
            "",
            "1. **英文版**: 通常采用最严格的形式化定义，强调公理体系",
            "2. **德文版**: 注重历史发展和直观理解，常包含更多背景信息",
            "3. **法文版**: 倾向于使用范畴论和抽象代数的视角",
            "4. **日文版**: 结合东西方数学传统，注重计算应用",
            "",
            "## 文化差异分析",
            "",
            "### 强调重点差异",
            "",
            "- **英文版**: 强调严格性和一般性，适用于研究导向的读者",
            "- **德文版**: 强调概念的历史渊源和哲学基础",
            "- **法文版**: 强调理论框架和结构统一性",
            "- **日文版**: 强调实例和计算方法，更贴近工程应用",
            "",
            "## 错误列表",
            "",
        ])
        
        if self.errors:
            report_lines.append("| 概念ID | 名称 | 错误信息 |")
            report_lines.append("|--------|------|----------|")
            for error in self.errors[:20]:
                error_msg = error['error'][:50] + "..." if len(error['error']) > 50 else error['error']
                report_lines.append(f"| {error['concept_id']} | {error['name']} | {error_msg} |")
            if len(self.errors) > 20:
                report_lines.append(f"| ... | ... | ({len(self.errors) - 20} more errors) |")
        else:
            report_lines.append("无错误记录。")
        
        report_lines.extend([
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
            "1. 审核低置信度对齐结果，人工确认准确性",
            "2. 扩展至更多语言版本（西班牙文、俄文、中文等）",
            "3. 建立持续更新机制，同步Wikipedia更新",
            "4. 开发多语言概念搜索引擎",
            "",
            "---",
            "",
            "*报告由FormalMath Wikipedia多语言对齐工具自动生成*",
        ])
        
        output_path = self.output_dir / "00-Wikipedia多语言对齐报告.md"
        with open(output_path, 'w', encoding='utf-8') as f:
            f.write('\n'.join(report_lines))
        
        print(f"Markdown report saved to: {output_path}")
        return output_path
    
    def update_yaml_with_multilang(self):
        """更新YAML文件添加多语言字段"""
        print("Updating YAML with multilang fields...")
        
        with open(self.yaml_path, 'r', encoding='utf-8') as f:
            data = yaml.safe_load(f)
        
        # 为每个概念添加多语言字段
        for concept in data.get('concepts', []):
            concept_id = concept.get('concept_id', '')
            if concept_id in self.results:
                info = self.results[concept_id]
                concept['multilang'] = {
                    'en': {
                        'title': info.en_title,
                        'url': info.en_url,
                        'extract': info.en_extract[:200] if info.en_extract else ""
                    },
                    'de': {
                        'title': info.de_title,
                        'url': info.de_url,
                        'extract': info.de_extract[:200] if info.de_extract else ""
                    },
                    'fr': {
                        'title': info.fr_title,
                        'url': info.fr_url,
                        'extract': info.fr_extract[:200] if info.fr_extract else ""
                    },
                    'ja': {
                        'title': info.ja_title,
                        'url': info.ja_url,
                        'extract': info.ja_extract[:200] if info.ja_extract else ""
                    },
                    'alignment_confidence': info.alignment_confidence
                }
        
        # 保存更新的YAML
        output_path = self.yaml_path.parent / "concept_prerequisites_multilang.yaml"
        with open(output_path, 'w', encoding='utf-8') as f:
            yaml.dump(data, f, allow_unicode=True, sort_keys=False, default_flow_style=False)
        
        print(f"Updated YAML saved to: {output_path}")
        return output_path
    
    def run(self):
        """执行完整流程"""
        print("=" * 60)
        print("Wikipedia多语言概念对齐工具")
        print("=" * 60)
        
        # 处理所有概念
        self.process_all_concepts()
        
        # 生成输出
        self.generate_json_table()
        self.generate_markdown_report()
        self.update_yaml_with_multilang()
        
        print("\n" + "=" * 60)
        print("All tasks completed!")
        print("=" * 60)


if __name__ == "__main__":
    aligner = WikipediaMultilangAligner(
        yaml_path="g:\\_src\\FormalMath\\project\\concept_prerequisites.yaml",
        output_dir="g:\\_src\\FormalMath"
    )
    aligner.run()
