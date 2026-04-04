"""
优化的嵌入模型服务
- 多模型选择与自动切换
- 模型量化与缓存
- 动态批处理
- LaTeX感知嵌入
"""
import re
import hashlib
import time
from typing import List, Dict, Optional, Tuple, Union, Callable
from dataclasses import dataclass, field
from enum import Enum
from functools import lru_cache
import numpy as np

# 尝试导入sentence-transformers
try:
    from sentence_transformers import SentenceTransformer
    SENTENCE_TRANSFORMERS_AVAILABLE = True
except ImportError:
    SENTENCE_TRANSFORMERS_AVAILABLE = False

# 尝试导入transformers用于更高级的模型
try:
    from transformers import AutoTokenizer, AutoModel
    TRANSFORMERS_AVAILABLE = True
except ImportError:
    TRANSFORMERS_AVAILABLE = False


class ModelType(Enum):
    """嵌入模型类型"""
    MINILM = "sentence-transformers/all-MiniLM-L6-v2"  # 快速、轻量
    MPNET = "sentence-transformers/all-mpnet-base-v2"  # 高质量
    MATH_BERT = "tbs17/MathBERT"  # 数学专用
    MULTILINGUAL = "sentence-transformers/paraphrase-multilingual-MiniLM-L12-v2"  # 多语言
    CUSTOM = "custom"


@dataclass
class EmbeddingConfig:
    """优化的嵌入配置"""
    model_type: ModelType = ModelType.MPNET
    dimension: int = 768
    max_length: int = 512
    normalize: bool = True
    batch_size: int = 32
    device: str = "cpu"
    
    # LaTeX处理配置
    latex_weight: float = 1.5
    text_weight: float = 1.0
    
    # 缓存配置
    enable_cache: bool = True
    cache_size: int = 10000
    
    # 量化配置
    enable_quantization: bool = False
    quantization_bits: int = 8
    
    # 性能配置
    use_onnx: bool = False
    use_fp16: bool = False


@dataclass
class ModelMetrics:
    """模型性能指标"""
    model_name: str
    avg_latency_ms: float
    throughput_qps: float
    memory_mb: float
    quality_score: float
    last_evaluated: float = field(default_factory=time.time)


class ModelRegistry:
    """模型注册表 - 管理多个嵌入模型"""
    
    # 预定义的模型配置
    MODEL_CONFIGS = {
        ModelType.MINILM: {
            "dimension": 384,
            "max_length": 512,
            "description": "轻量级模型，适合快速推理",
            "speed_score": 0.95,
            "quality_score": 0.75
        },
        ModelType.MPNET: {
            "dimension": 768,
            "max_length": 512,
            "description": "高质量通用模型",
            "speed_score": 0.70,
            "quality_score": 0.90
        },
        ModelType.MATH_BERT: {
            "dimension": 768,
            "max_length": 512,
            "description": "数学专用模型",
            "speed_score": 0.65,
            "quality_score": 0.95
        },
        ModelType.MULTILINGUAL: {
            "dimension": 384,
            "max_length": 512,
            "description": "多语言支持模型",
            "speed_score": 0.80,
            "quality_score": 0.80
        }
    }
    
    def __init__(self):
        self.loaded_models: Dict[ModelType, any] = {}
        self.metrics: Dict[ModelType, ModelMetrics] = {}
        self._current_model: ModelType = ModelType.MPNET
    
    def get_model_config(self, model_type: ModelType) -> Dict:
        """获取模型配置"""
        return self.MODEL_CONFIGS.get(model_type, self.MODEL_CONFIGS[ModelType.MPNET])
    
    def load_model(self, model_type: ModelType, device: str = "cpu") -> Optional[any]:
        """加载指定模型"""
        if model_type in self.loaded_models:
            return self.loaded_models[model_type]
        
        if not SENTENCE_TRANSFORMERS_AVAILABLE:
            return None
        
        try:
            model_name = model_type.value
            model = SentenceTransformer(model_name, device=device)
            self.loaded_models[model_type] = model
            return model
        except Exception as e:
            print(f"Failed to load model {model_type}: {e}")
            return None
    
    def get_optimal_model(self, query_type: str = "general", latency_requirement_ms: float = 100) -> ModelType:
        """
        根据查询类型和延迟要求选择最优模型
        
        Args:
            query_type: 'general', 'math', 'multilingual'
            latency_requirement_ms: 最大允许延迟（毫秒）
        """
        candidates = []
        
        for model_type, config in self.MODEL_CONFIGS.items():
            # 根据查询类型筛选
            if query_type == "math" and model_type == ModelType.MATH_BERT:
                candidates.append((model_type, config))
            elif query_type == "multilingual" and model_type == ModelType.MULTILINGUAL:
                candidates.append((model_type, config))
            elif query_type == "general":
                candidates.append((model_type, config))
        
        # 根据延迟要求选择
        if latency_requirement_ms < 50:
            # 低延迟要求，选择最轻量的模型
            best = min(candidates, key=lambda x: x[1]["dimension"])
        else:
            # 平衡质量和速度
            best = max(candidates, key=lambda x: x[1]["quality_score"] * 0.6 + x[1]["speed_score"] * 0.4)
        
        return best[0]
    
    def switch_model(self, model_type: ModelType) -> bool:
        """切换当前使用的模型"""
        if model_type in self.loaded_models or self.load_model(model_type):
            self._current_model = model_type
            return True
        return False


class LaTeXTokenizer:
    """增强的LaTeX感知分词器"""
    
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
        'vector': r'\\vec\{([^}]+)\}',
        'matrix': r'\\begin\{(pmatrix|bmatrix|vmatrix)\}(.*?)\\end\{\1\}',
        'partial': r'\\partial',
        'nabla': r'\\nabla',
    }
    
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
        '∈': 'in', '∉': 'notin', '⊂': 'subset', '⊃': 'superset',
        '∪': 'cup', '∩': 'cap', '∅': 'emptyset', '∀': 'forall',
        '∃': 'exists', '∧': 'land', '∨': 'lor', '¬': 'neg',
        '→': 'to', '⇒': 'Rightarrow', '⇔': 'Leftrightarrow',
        '≤': 'leq', '≥': 'geq', '≠': 'neq', '≈': 'approx',
        '×': 'times', '÷': 'div', '±': 'pm', '∂': 'partial',
        '∇': 'nabla', '∫': 'integral', '∑': 'sum', '∏': 'product',
        '√': 'square root', '²': 'squared', '³': 'cubed',
    }
    
    def __init__(self):
        self.compiled_patterns = {
            name: re.compile(pattern, re.DOTALL)
            for name, pattern in self.LATEX_PATTERNS.items()
        }
    
    def extract_latex_expressions(self, text: str) -> List[Dict[str, any]]:
        """提取LaTeX表达式"""
        expressions = []
        seen_positions = set()
        
        for pattern_name, pattern in self.compiled_patterns.items():
            for match in pattern.finditer(text):
                # 避免重复匹配
                pos_key = (match.start(), match.end())
                if pos_key in seen_positions:
                    continue
                seen_positions.add(pos_key)
                
                expressions.append({
                    'type': pattern_name,
                    'content': match.group(0),
                    'groups': match.groups(),
                    'start': match.start(),
                    'end': match.end()
                })
        
        expressions.sort(key=lambda x: x['start'])
        return expressions
    
    def normalize_latex(self, latex: str) -> str:
        """标准化LaTeX"""
        normalized = re.sub(r'\s+', ' ', latex.strip())
        
        for symbol, replacement in self.MATH_SYMBOLS.items():
            normalized = normalized.replace(symbol, replacement)
        
        # 标准化括号
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
        latex_raw = []
        
        last_end = 0
        for expr in latex_exprs:
            if expr['start'] > last_end:
                text_part = text[last_end:expr['start']].strip()
                if text_part:
                    text_tokens.extend(self._tokenize_text(text_part))
            
            normalized = self.normalize_latex(expr['content'])
            latex_tokens.append(normalized)
            latex_raw.append(expr['content'])
            
            last_end = expr['end']
        
        if last_end < len(text):
            text_part = text[last_end:].strip()
            if text_part:
                text_tokens.extend(self._tokenize_text(text_part))
        
        return {
            'text': text_tokens,
            'latex': latex_tokens,
            'latex_raw': latex_raw
        }
    
    def _tokenize_text(self, text: str) -> List[str]:
        """对普通文本分词"""
        text = text.lower()
        tokens = re.findall(r'\b\w+\b|[\u4e00-\u9fff]', text)
        return [t for t in tokens if t]


class QuantizedEmbeddingCache:
    """量化嵌入缓存"""
    
    def __init__(self, max_size: int = 10000, quantization_bits: int = 8):
        self.max_size = max_size
        self.quantization_bits = quantization_bits
        self._cache: Dict[str, np.ndarray] = {}
        self._access_count: Dict[str, int] = {}
        self._cache_hits = 0
        self._cache_misses = 0
    
    def _quantize(self, vector: np.ndarray) -> np.ndarray:
        """量化向量"""
        if self.quantization_bits == 8:
            # 8-bit量化
            min_val, max_val = vector.min(), vector.max()
            scale = (max_val - min_val) / 255.0
            if scale > 0:
                quantized = ((vector - min_val) / scale).astype(np.uint8)
                return quantized, (min_val, scale)
            return vector, None
        return vector, None
    
    def _dequantize(self, quantized: np.ndarray, params: Tuple) -> np.ndarray:
        """反量化向量"""
        if params is None or self.quantization_bits != 8:
            return quantized
        min_val, scale = params
        return quantized.astype(np.float32) * scale + min_val
    
    def get(self, key: str) -> Optional[np.ndarray]:
        """获取缓存"""
        if key in self._cache:
            self._access_count[key] += 1
            self._cache_hits += 1
            return self._cache[key]
        self._cache_misses += 1
        return None
    
    def put(self, key: str, vector: np.ndarray):
        """添加缓存"""
        if len(self._cache) >= self.max_size:
            # LRU淘汰
            min_key = min(self._access_count, key=self._access_count.get)
            del self._cache[min_key]
            del self._access_count[min_key]
        
        self._cache[key] = vector.copy()
        self._access_count[key] = 1
    
    def get_stats(self) -> Dict:
        """获取缓存统计"""
        total = self._cache_hits + self._cache_misses
        hit_rate = self._cache_hits / total if total > 0 else 0
        return {
            'size': len(self._cache),
            'max_size': self.max_size,
            'hits': self._cache_hits,
            'misses': self._cache_misses,
            'hit_rate': hit_rate
        }


class OptimizedEmbeddingService:
    """优化的嵌入服务"""
    
    def __init__(self, config: EmbeddingConfig = None):
        self.config = config or EmbeddingConfig()
        self.model_registry = ModelRegistry()
        self.tokenizer = LaTeXTokenizer()
        
        # 加载默认模型
        self.current_model_type = self.config.model_type
        self.model = self.model_registry.load_model(
            self.current_model_type, 
            device=self.config.device
        )
        
        # 初始化缓存
        self.cache = QuantizedEmbeddingCache(
            max_size=self.config.cache_size,
            quantization_bits=self.config.quantization_bits if self.config.enable_quantization else 32
        )
        
        # 性能监控
        self._latency_history: List[float] = []
        self._max_history_size = 1000
    
    def switch_model(self, model_type: ModelType) -> bool:
        """切换模型"""
        if self.model_registry.switch_model(model_type):
            self.current_model_type = model_type
            self.model = self.model_registry.loaded_models[model_type]
            config = self.model_registry.get_model_config(model_type)
            self.config.dimension = config["dimension"]
            return True
        return False
    
    def auto_select_model(self, text: str) -> ModelType:
        """根据文本内容自动选择模型"""
        # 检测内容类型
        has_math = bool(re.search(r'[\$\\]', text))
        has_chinese = bool(re.search(r'[\u4e00-\u9fff]', text))
        
        if has_math and self.model_registry.load_model(ModelType.MATH_BERT):
            return ModelType.MATH_BERT
        elif has_chinese and self.model_registry.load_model(ModelType.MULTILINGUAL):
            return ModelType.MULTILINGUAL
        else:
            return ModelType.MPNET
    
    def embed_text(self, text: str, use_cache: bool = True) -> np.ndarray:
        """嵌入单个文本"""
        if not text or not text.strip():
            return np.zeros(self.config.dimension)
        
        # 检查缓存
        cache_key = hashlib.md5(text.encode()).hexdigest()
        if use_cache and self.config.enable_cache:
            cached = self.cache.get(cache_key)
            if cached is not None:
                return cached
        
        start_time = time.time()
        
        if self.model is not None:
            embedding = self.model.encode(
                text, 
                normalize_embeddings=self.config.normalize,
                show_progress_bar=False
            )
        else:
            embedding = self._fallback_embed(text)
        
        # 记录延迟
        latency = (time.time() - start_time) * 1000
        self._latency_history.append(latency)
        if len(self._latency_history) > self._max_history_size:
            self._latency_history = self._latency_history[-self._max_history_size:]
        
        # 缓存结果
        if use_cache and self.config.enable_cache:
            self.cache.put(cache_key, embedding)
        
        return embedding
    
    def embed_texts(self, texts: List[str], use_cache: bool = True) -> np.ndarray:
        """批量嵌入文本"""
        if not texts:
            return np.array([])
        
        # 检查缓存
        results = []
        texts_to_embed = []
        indices = []
        
        for i, text in enumerate(texts):
            cache_key = hashlib.md5(text.encode()).hexdigest()
            cached = self.cache.get(cache_key) if use_cache and self.config.enable_cache else None
            
            if cached is not None:
                results.append((i, cached))
            else:
                texts_to_embed.append(text)
                indices.append(i)
        
        # 批量嵌入
        if texts_to_embed:
            start_time = time.time()
            
            if self.model is not None:
                embeddings = self.model.encode(
                    texts_to_embed,
                    normalize_embeddings=self.config.normalize,
                    show_progress_bar=len(texts_to_embed) > 100,
                    batch_size=self.config.batch_size
                )
            else:
                embeddings = np.array([self._fallback_embed(t) for t in texts_to_embed])
            
            latency = (time.time() - start_time) * 1000
            self._latency_history.append(latency / len(texts_to_embed))
            
            # 缓存新结果
            if use_cache and self.config.enable_cache:
                for idx, text, emb in zip(indices, texts_to_embed, embeddings):
                    cache_key = hashlib.md5(text.encode()).hexdigest()
                    self.cache.put(cache_key, emb)
                    results.append((idx, emb))
        
        # 按原始顺序排序
        results.sort(key=lambda x: x[0])
        return np.array([r[1] for r in results])
    
    def embed_math_content(self, text: str) -> np.ndarray:
        """嵌入包含数学公式的内容"""
        tokens = self.tokenizer.tokenize(text)
        
        # 检测是否需要数学专用模型
        if tokens['latex'] and self.current_model_type != ModelType.MATH_BERT:
            if self.model_registry.load_model(ModelType.MATH_BERT):
                temp_model = self.model_registry.loaded_models[ModelType.MATH_BERT]
            else:
                temp_model = self.model
        else:
            temp_model = self.model
        
        text_embedding = None
        latex_embedding = None
        
        if tokens['text']:
            text_str = ' '.join(tokens['text'])
            if temp_model is not None:
                text_embedding = temp_model.encode(text_str, normalize_embeddings=self.config.normalize)
            else:
                text_embedding = self._fallback_embed(text_str)
            text_embedding = text_embedding * self.config.text_weight
        
        if tokens['latex']:
            latex_texts = [self._latex_to_description(latex) for latex in tokens['latex']]
            latex_str = ' '.join(latex_texts)
            
            if temp_model is not None:
                latex_embedding = temp_model.encode(latex_str, normalize_embeddings=self.config.normalize)
            else:
                latex_embedding = self._fallback_embed(latex_str)
            latex_embedding = latex_embedding * self.config.latex_weight
        
        # 合并
        if text_embedding is not None and latex_embedding is not None:
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
        """LaTeX转换为文本描述"""
        desc = latex
        
        replacements = {
            r'\\frac\{([^}]+)\}\{([^}]+)\}': r'fraction of \1 over \2',
            r'\\sum': 'summation',
            r'\\int': 'integral',
            r'\\lim': 'limit',
            r'\\sqrt(?:\[([^\]]+)\])?\{([^}]+)\}': r'\1 root of \2',
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
            r'\\partial': 'partial derivative',
            r'\\nabla': 'gradient',
            r'\\vec\{([^}]+)\}': r'vector \1',
        }
        
        for pattern, replacement in replacements.items():
            try:
                desc = re.sub(pattern, replacement, desc)
            except:
                pass
        
        desc = re.sub(r'\\[a-zA-Z]+', '', desc)
        desc = re.sub(r'[{}\[\]$]', '', desc)
        
        return desc.strip()
    
    def _fallback_embed(self, text: str) -> np.ndarray:
        """Fallback嵌入方法"""
        np.random.seed(hash(text) % 2**32)
        vec = np.random.randn(self.config.dimension)
        if self.config.normalize:
            vec = vec / np.linalg.norm(vec)
        return vec
    
    def compute_similarity(self, embedding1: np.ndarray, embedding2: np.ndarray) -> float:
        """计算余弦相似度"""
        if embedding1 is None or embedding2 is None:
            return 0.0
        
        norm1 = np.linalg.norm(embedding1)
        norm2 = np.linalg.norm(embedding2)
        
        if norm1 == 0 or norm2 == 0:
            return 0.0
        
        return float(np.dot(embedding1, embedding2) / (norm1 * norm2))
    
    def get_performance_stats(self) -> Dict:
        """获取性能统计"""
        stats = {
            'current_model': self.current_model_type.value,
            'cache_stats': self.cache.get_stats(),
            'avg_latency_ms': np.mean(self._latency_history) if self._latency_history else 0,
            'p95_latency_ms': np.percentile(self._latency_history, 95) if self._latency_history else 0,
        }
        return stats


# 全局实例
_embedding_service_optimized: Optional[OptimizedEmbeddingService] = None


def get_embedding_service_optimized(config: EmbeddingConfig = None) -> OptimizedEmbeddingService:
    """获取优化的嵌入服务实例"""
    global _embedding_service_optimized
    if _embedding_service_optimized is None:
        _embedding_service_optimized = OptimizedEmbeddingService(config)
    return _embedding_service_optimized
