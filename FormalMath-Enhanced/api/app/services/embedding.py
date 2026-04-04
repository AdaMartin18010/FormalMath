"""
文本嵌入服务
支持LaTeX感知分词、数学公式嵌入、多语言支持
"""
import re
import hashlib
from typing import List, Dict, Optional, Tuple, Union
from dataclasses import dataclass
import numpy as np

# 尝试导入sentence-transformers，如果不可用则使用fallback
try:
    from sentence_transformers import SentenceTransformer
    SENTENCE_TRANSFORMERS_AVAILABLE = True
except ImportError:
    SENTENCE_TRANSFORMERS_AVAILABLE = False

try:
    import faiss
    FAISS_AVAILABLE = True
except ImportError:
    FAISS_AVAILABLE = False


@dataclass
class EmbeddingConfig:
    """嵌入配置"""
    model_name: str = "sentence-transformers/all-MiniLM-L6-v2"
    dimension: int = 384
    max_length: int = 512
    normalize: bool = True
    # LaTeX处理配置
    latex_weight: float = 1.5  # 数学公式的权重
    text_weight: float = 1.0   # 普通文本的权重
    # 多语言配置
    multilingual: bool = True
    # 缓存配置
    enable_cache: bool = True


class LaTeXTokenizer:
    """LaTeX感知分词器"""
    
    # LaTeX数学环境正则
    LATEX_PATTERNS = {
        'inline_math': r'\$([^$]+)\$',
        'display_math': r'\$\$([^$]+)\$\$',
        'equation': r'\\begin\{equation\}(.*?)\\end\{equation\}',
        'align': r'\\begin\{align\}(.*?)\\end\{align\}',
        'align_star': r'\\begin\{align\*\}(.*?)\\end\{align\*\}',
        'gather': r'\\begin\{gather\}(.*?)\\end\{gather\}',
        'subscript': r'_(\{[^}]+\}|\w)',
        'superscript': r'\^(\{[^}]+\}|\w)',
        'fraction': r'\\frac\{([^}]+)\}\{([^}]+)\}',
        'sqrt': r'\\sqrt\{([^}]+)\}',
        'sum': r'\\sum_\{([^}]+)\}\^\{([^}]+)\}',
        'integral': r'\\int_\{([^}]+)\}\^\{([^}]+)\}',
        'limit': r'\\lim_\{([^}]+)\}',
    }
    
    # 数学符号映射（用于标准化）
    MATH_SYMBOLS = {
        'α': 'alpha', 'β': 'beta', 'γ': 'gamma', 'δ': 'delta',
        'ε': 'epsilon', 'ζ': 'zeta', 'η': 'eta', 'θ': 'theta',
        'ι': 'iota', 'κ': 'kappa', 'λ': 'lambda', 'μ': 'mu',
        'ν': 'nu', 'ξ': 'xi', 'ο': 'omicron', 'π': 'pi',
        'ρ': 'rho', 'σ': 'sigma', 'τ': 'tau', 'υ': 'upsilon',
        'φ': 'phi', 'χ': 'chi', 'ψ': 'psi', 'ω': 'omega',
        'Γ': 'Gamma', 'Δ': 'Delta', 'Θ': 'Theta', 'Λ': 'Lambda',
        'Ξ': 'Xi', 'Π': 'Pi', 'Σ': 'Sigma', 'Φ': 'Phi',
        'Ψ': 'Psi', 'Ω': 'Omega', '∞': 'infinity',
        '∈': 'in', '∉': 'notin', '⊂': 'subset', '⊃': 'supset',
        '∪': 'cup', '∩': 'cap', '∅': 'emptyset', '∀': 'forall',
        '∃': 'exists', '∧': 'land', '∨': 'lor', '¬': 'neg',
        '→': 'to', '⇒': 'Rightarrow', '⇔': 'Leftrightarrow',
        '≤': 'leq', '≥': 'geq', '≠': 'neq', '≈': 'approx',
        '×': 'times', '÷': 'div', '±': 'pm', '∂': 'partial',
        '∇': 'nabla', '∫': 'int', '∑': 'sum', '∏': 'prod',
        '√': 'sqrt', '²': '^2', '³': '^3', 'ⁿ': '^n',
    }
    
    def __init__(self):
        self.compiled_patterns = {
            name: re.compile(pattern, re.DOTALL)
            for name, pattern in self.LATEX_PATTERNS.items()
        }
    
    def extract_latex_expressions(self, text: str) -> List[Dict[str, any]]:
        """提取文本中的LaTeX表达式"""
        expressions = []
        
        for pattern_name, pattern in self.compiled_patterns.items():
            for match in pattern.finditer(text):
                expressions.append({
                    'type': pattern_name,
                    'content': match.group(0),
                    'groups': match.groups(),
                    'start': match.start(),
                    'end': match.end()
                })
        
        # 按位置排序
        expressions.sort(key=lambda x: x['start'])
        return expressions
    
    def normalize_latex(self, latex: str) -> str:
        """标准化LaTeX表达式"""
        # 移除多余空格
        normalized = re.sub(r'\s+', ' ', latex.strip())
        
        # 标准化数学符号
        for symbol, replacement in self.MATH_SYMBOLS.items():
            normalized = normalized.replace(symbol, replacement)
        
        # 标准化命令（移除不必要的括号）
        normalized = re.sub(r'\\left\(', '(', normalized)
        normalized = re.sub(r'\\right\)', ')', normalized)
        normalized = re.sub(r'\\left\[', '[', normalized)
        normalized = re.sub(r'\\right\]', ']', normalized)
        normalized = re.sub(r'\\\{', '{', normalized)
        normalized = re.sub(r'\\\}', '}', normalized)
        
        return normalized
    
    def tokenize(self, text: str) -> Dict[str, List[str]]:
        """分词：分离文本和数学公式"""
        latex_exprs = self.extract_latex_expressions(text)
        
        text_tokens = []
        latex_tokens = []
        
        last_end = 0
        for expr in latex_exprs:
            # 提取文本部分
            if expr['start'] > last_end:
                text_part = text[last_end:expr['start']].strip()
                if text_part:
                    text_tokens.extend(self._tokenize_text(text_part))
            
            # 提取LaTeX部分
            normalized = self.normalize_latex(expr['content'])
            latex_tokens.append(normalized)
            
            last_end = expr['end']
        
        # 处理剩余文本
        if last_end < len(text):
            text_part = text[last_end:].strip()
            if text_part:
                text_tokens.extend(self._tokenize_text(text_part))
        
        return {
            'text': text_tokens,
            'latex': latex_tokens,
            'latex_raw': [expr['content'] for expr in latex_exprs]
        }
    
    def _tokenize_text(self, text: str) -> List[str]:
        """对普通文本进行分词"""
        # 简单的分词：按空格和标点分割
        tokens = re.findall(r'\b\w+\b|[\u4e00-\u9fff]', text)
        return [t for t in tokens if t]


class FormulaEmbedder:
    """数学公式嵌入器"""
    
    def __init__(self, config: EmbeddingConfig = None):
        self.config = config or EmbeddingConfig()
        self.tokenizer = LaTeXTokenizer()
    
    def structural_hash(self, latex: str) -> str:
        """生成公式的结构哈希（变量无关）"""
        normalized = self.tokenizer.normalize_latex(latex)
        
        # 替换变量为占位符
        # 单字母变量
        normalized = re.sub(r'(?<![\\a-zA-Z])[a-zA-Z](?![a-zA-Z])', 'VAR', normalized)
        # 数字
        normalized = re.sub(r'\d+', 'NUM', normalized)
        
        return hashlib.md5(normalized.encode()).hexdigest()[:16]
    
    def extract_structure(self, latex: str) -> Dict[str, any]:
        """提取公式的结构特征"""
        normalized = self.tokenizer.normalize_latex(latex)
        
        structure = {
            'operators': [],
            'functions': [],
            'variables': [],
            'constants': [],
            'depth': 0
        }
        
        # 提取运算符
        operators = re.findall(r'[+-/*=<>^_%]', normalized)
        structure['operators'] = list(set(operators))
        
        # 提取函数
        functions = re.findall(r'\\[a-zA-Z]+', normalized)
        structure['functions'] = list(set(functions))
        
        # 提取变量（单字母）
        variables = re.findall(r'(?<![\\a-zA-Z])[a-zA-Z](?![a-zA-Z])', normalized)
        structure['variables'] = list(set(variables))
        
        # 提取数字常量
        constants = re.findall(r'\d+\.?\d*', normalized)
        structure['constants'] = list(set(constants))
        
        # 计算嵌套深度
        depth = 0
        max_depth = 0
        for char in normalized:
            if char == '{':
                depth += 1
                max_depth = max(max_depth, depth)
            elif char == '}':
                depth -= 1
        structure['depth'] = max_depth
        
        return structure
    
    def structural_similarity(self, latex1: str, latex2: str) -> float:
        """计算两个公式的结构相似度（变量无关）"""
        struct1 = self.extract_structure(latex1)
        struct2 = self.extract_structure(latex2)
        
        # 计算Jaccard相似度
        def jaccard(set1, set2):
            if not set1 and not set2:
                return 1.0
            intersection = len(set(set1) & set(set2))
            union = len(set(set1) | set(set2))
            return intersection / union if union > 0 else 0.0
        
        # 综合相似度
        op_sim = jaccard(struct1['operators'], struct2['operators'])
        func_sim = jaccard(struct1['functions'], struct2['functions'])
        depth_sim = 1.0 - abs(struct1['depth'] - struct2['depth']) / max(struct1['depth'], struct2['depth'], 1)
        
        # 加权平均
        similarity = (op_sim * 0.4 + func_sim * 0.4 + depth_sim * 0.2)
        
        return similarity


class EmbeddingService:
    """嵌入服务主类"""
    
    def __init__(self, config: EmbeddingConfig = None):
        self.config = config or EmbeddingConfig()
        self.tokenizer = LaTeXTokenizer()
        self.formula_embedder = FormulaEmbedder(self.config)
        
        # 初始化模型
        self.model = None
        if SENTENCE_TRANSFORMERS_AVAILABLE:
            try:
                self.model = SentenceTransformer(self.config.model_name)
                print(f"Loaded embedding model: {self.config.model_name}")
            except Exception as e:
                print(f"Failed to load model: {e}")
        
        # 简单缓存
        self._cache: Dict[str, np.ndarray] = {}
    
    def embed_text(self, text: str) -> np.ndarray:
        """嵌入单个文本"""
        if not text or not text.strip():
            return np.zeros(self.config.dimension)
        
        # 检查缓存
        cache_key = hashlib.md5(text.encode()).hexdigest()
        if self.config.enable_cache and cache_key in self._cache:
            return self._cache[cache_key]
        
        if self.model is not None:
            # 使用sentence-transformers
            embedding = self.model.encode(text, normalize_embeddings=self.config.normalize)
        else:
            # Fallback：使用简单的词频向量
            embedding = self._fallback_embed(text)
        
        # 缓存结果
        if self.config.enable_cache:
            self._cache[cache_key] = embedding
        
        return embedding
    
    def embed_texts(self, texts: List[str]) -> np.ndarray:
        """批量嵌入文本"""
        if not texts:
            return np.array([])
        
        if self.model is not None:
            embeddings = self.model.encode(
                texts, 
                normalize_embeddings=self.config.normalize,
                show_progress_bar=len(texts) > 100
            )
            return embeddings
        else:
            # Fallback
            embeddings = [self._fallback_embed(text) for text in texts]
            return np.array(embeddings)
    
    def embed_math_content(self, text: str) -> np.ndarray:
        """嵌入包含数学公式的内容"""
        tokens = self.tokenizer.tokenize(text)
        
        # 分别嵌入文本和公式
        text_embedding = None
        latex_embedding = None
        
        if tokens['text']:
            text_str = ' '.join(tokens['text'])
            text_embedding = self.embed_text(text_str) * self.config.text_weight
        
        if tokens['latex']:
            # 将LaTeX转换为可读的文本描述
            latex_texts = []
            for latex in tokens['latex']:
                # 简单的LaTeX到文本转换
                text_desc = self._latex_to_description(latex)
                latex_texts.append(text_desc)
            
            latex_str = ' '.join(latex_texts)
            latex_embedding = self.embed_text(latex_str) * self.config.latex_weight
        
        # 合并嵌入
        if text_embedding is not None and latex_embedding is not None:
            # 加权平均
            combined = (text_embedding * self.config.text_weight + 
                       latex_embedding * self.config.latex_weight) / \
                      (self.config.text_weight + self.config.latex_weight)
            return combined
        elif text_embedding is not None:
            return text_embedding
        elif latex_embedding is not None:
            return latex_embedding
        else:
            return np.zeros(self.config.dimension)
    
    def _latex_to_description(self, latex: str) -> str:
        """将LaTeX转换为文本描述（用于嵌入）"""
        # 简单的规则转换
        desc = latex
        
        # 替换常见命令
        replacements = {
            r'\\frac\{([^}]+)\}\{([^}]+)\}': r'fraction of \1 over \2',
            r'\\sum': 'summation',
            r'\\int': 'integral',
            r'\\lim': 'limit',
            r'\\sqrt\{([^}]+)\}': r'square root of \1',
            r'\\alpha': 'alpha',
            r'\\beta': 'beta',
            r'\\gamma': 'gamma',
            r'\\delta': 'delta',
            r'\\theta': 'theta',
            r'\\lambda': 'lambda',
            r'\\pi': 'pi',
            r'\\sigma': 'sigma',
            r'\\phi': 'phi',
            r'\\omega': 'omega',
            r'\\infty': 'infinity',
            r'\\to': 'to',
            r'\\Rightarrow': 'implies',
            r'\\Leftrightarrow': 'equivalent to',
            r'\\in': 'in',
            r'\\subset': 'subset of',
            r'\\cup': 'union',
            r'\\cap': 'intersection',
        }
        
        for pattern, replacement in replacements.items():
            try:
                desc = re.sub(pattern, replacement, desc)
            except:
                pass
        
        # 移除剩余的控制序列
        desc = re.sub(r'\\[a-zA-Z]+', '', desc)
        # 移除特殊字符
        desc = re.sub(r'[{}\[\]$]', '', desc)
        
        return desc.strip()
    
    def _fallback_embed(self, text: str) -> np.ndarray:
        """Fallback嵌入方法（当模型不可用时）"""
        # 使用简单的哈希向量
        np.random.seed(hash(text) % 2**32)
        vec = np.random.randn(self.config.dimension)
        if self.config.normalize:
            vec = vec / np.linalg.norm(vec)
        return vec
    
    def compute_similarity(self, embedding1: np.ndarray, embedding2: np.ndarray) -> float:
        """计算两个嵌入向量的余弦相似度"""
        if embedding1 is None or embedding2 is None:
            return 0.0
        
        norm1 = np.linalg.norm(embedding1)
        norm2 = np.linalg.norm(embedding2)
        
        if norm1 == 0 or norm2 == 0:
            return 0.0
        
        return float(np.dot(embedding1, embedding2) / (norm1 * norm2))


# 全局嵌入服务实例
_embedding_service: Optional[EmbeddingService] = None


def get_embedding_service() -> EmbeddingService:
    """获取全局嵌入服务实例"""
    global _embedding_service
    if _embedding_service is None:
        _embedding_service = EmbeddingService()
    return _embedding_service
