"""
LLM客户端主类
统一管理不同LLM提供商的调用
"""
import os
import json
import logging
from typing import Dict, List, Optional, AsyncGenerator, Any
from dataclasses import dataclass, field
from enum import Enum
import asyncio
from datetime import datetime

from .providers import DeepSeekProvider, OpenAIProvider, BaseProvider

logger = logging.getLogger(__name__)


class LLMProvider(Enum):
    """支持的LLM提供商"""
    DEEPSEEK = "deepseek"
    OPENAI = "openai"
    AZURE_OPENAI = "azure_openai"


@dataclass
class LLMConfig:
    """LLM配置"""
    provider: LLMProvider = LLMProvider.DEEPSEEK
    model: str = "deepseek-chat"
    temperature: float = 0.7
    max_tokens: int = 4096
    top_p: float = 0.9
    timeout: int = 60
    retry_count: int = 3
    api_key: Optional[str] = None
    base_url: Optional[str] = None
    
    # 数学专用配置
    math_mode: bool = True  # 启用数学优化模式
    enable_latex_validation: bool = True
    enable_step_by_step: bool = True


@dataclass
class LLMResponse:
    """LLM响应"""
    content: str
    usage: Dict[str, int] = field(default_factory=dict)
    model: str = ""
    finish_reason: str = ""
    latency_ms: float = 0.0
    timestamp: datetime = field(default_factory=datetime.now)
    
    # 数学专用字段
    latex_formulas: List[str] = field(default_factory=list)
    proof_steps: List[str] = field(default_factory=list)
    confidence_score: float = 0.0


@dataclass
class ConversationMessage:
    """对话消息"""
    role: str  # 'system', 'user', 'assistant'
    content: str
    timestamp: datetime = field(default_factory=datetime.now)
    metadata: Dict[str, Any] = field(default_factory=dict)


class ConversationContext:
    """对话上下文管理器"""
    
    def __init__(self, max_history: int = 10):
        self.messages: List[ConversationMessage] = []
        self.max_history = max_history
        self.session_id = f"conv_{datetime.now().timestamp()}"
    
    def add_message(self, role: str, content: str, metadata: Dict = None):
        """添加消息到上下文"""
        message = ConversationMessage(
            role=role,
            content=content,
            metadata=metadata or {}
        )
        self.messages.append(message)
        
        # 保持历史记录在限制内
        if len(self.messages) > self.max_history:
            # 保留系统消息和最近的消息
            system_messages = [m for m in self.messages if m.role == 'system']
            other_messages = [m for m in self.messages if m.role != 'system']
            self.messages = system_messages + other_messages[-(self.max_history - len(system_messages)):]
    
    def get_messages(self, include_system: bool = True) -> List[Dict]:
        """获取消息列表（用于API调用）"""
        messages = []
        for msg in self.messages:
            if not include_system and msg.role == 'system':
                continue
            messages.append({
                'role': msg.role,
                'content': msg.content
            })
        return messages
    
    def clear(self):
        """清空上下文"""
        self.messages = []
    
    def to_dict(self) -> Dict:
        """序列化为字典"""
        return {
            'session_id': self.session_id,
            'messages': [
                {
                    'role': m.role,
                    'content': m.content,
                    'timestamp': m.timestamp.isoformat(),
                    'metadata': m.metadata
                }
                for m in self.messages
            ],
            'max_history': self.max_history
        }


class LLMClient:
    """
    LLM客户端主类
    支持多提供商、对话上下文管理、数学专用功能
    """
    
    def __init__(self, config: LLMConfig = None):
        self.config = config or LLMConfig()
        self.provider: Optional[BaseProvider] = None
        self._init_provider()
        
        # 对话上下文缓存
        self._contexts: Dict[str, ConversationContext] = {}
        
        # 统计信息
        self._stats = {
            'total_requests': 0,
            'total_tokens': 0,
            'errors': 0,
            'avg_latency_ms': 0.0
        }
    
    def _init_provider(self):
        """初始化提供商"""
        if self.config.provider == LLMProvider.DEEPSEEK:
            self.provider = DeepSeekProvider(
                api_key=self.config.api_key or os.getenv('DEEPSEEK_API_KEY'),
                base_url=self.config.base_url or os.getenv('DEEPSEEK_BASE_URL', 'https://api.deepseek.com'),
                model=self.config.model
            )
        elif self.config.provider == LLMProvider.OPENAI:
            self.provider = OpenAIProvider(
                api_key=self.config.api_key or os.getenv('OPENAI_API_KEY'),
                base_url=self.config.base_url,
                model=self.config.model
            )
        else:
            raise ValueError(f"不支持的LLM提供商: {self.config.provider}")
        
        logger.info(f"LLM客户端初始化完成: {self.config.provider.value}, 模型: {self.config.model}")
    
    async def chat(
        self,
        message: str,
        context_id: Optional[str] = None,
        system_prompt: Optional[str] = None,
        temperature: Optional[float] = None,
        stream: bool = False
    ) -> LLMResponse:
        """
        发送聊天消息
        
        Args:
            message: 用户消息
            context_id: 上下文ID（用于多轮对话）
            system_prompt: 系统提示词
            temperature: 温度参数（覆盖默认配置）
            stream: 是否流式输出
        """
        start_time = datetime.now()
        
        try:
            # 获取或创建上下文
            if context_id:
                context = self._get_or_create_context(context_id)
            else:
                context = ConversationContext()
            
            # 添加系统提示词
            if system_prompt and not any(m.role == 'system' for m in context.messages):
                context.add_message('system', system_prompt)
            
            # 添加用户消息
            context.add_message('user', message)
            
            # 调用LLM
            temp = temperature if temperature is not None else self.config.temperature
            
            if stream:
                response_content = ""
                async for chunk in self.provider.chat_stream(
                    messages=context.get_messages(),
                    temperature=temp,
                    max_tokens=self.config.max_tokens
                ):
                    response_content += chunk
            else:
                response = await self.provider.chat(
                    messages=context.get_messages(),
                    temperature=temp,
                    max_tokens=self.config.max_tokens
                )
                response_content = response['content']
                usage = response.get('usage', {})
            
            # 添加助手响应到上下文
            context.add_message('assistant', response_content)
            
            # 如果是新上下文，保存它
            if context_id:
                self._contexts[context_id] = context
            
            # 计算延迟
            latency_ms = (datetime.now() - start_time).total_seconds() * 1000
            
            # 更新统计
            self._update_stats(latency_ms, usage.get('total_tokens', 0))
            
            # 提取数学专用信息
            latex_formulas = self._extract_latex_formulas(response_content)
            proof_steps = self._extract_proof_steps(response_content)
            
            return LLMResponse(
                content=response_content,
                usage=usage if not stream else {},
                model=self.config.model,
                latency_ms=latency_ms,
                latex_formulas=latex_formulas,
                proof_steps=proof_steps,
                confidence_score=self._calculate_confidence(response_content)
            )
            
        except Exception as e:
            logger.error(f"LLM调用失败: {e}")
            self._stats['errors'] += 1
            raise
    
    async def chat_with_math_context(
        self,
        message: str,
        concept_context: Optional[List[str]] = None,
        related_formulas: Optional[List[str]] = None,
        difficulty_level: Optional[str] = None,
        **kwargs
    ) -> LLMResponse:
        """
        带数学上下文的聊天
        
        Args:
            message: 用户消息
            concept_context: 相关概念列表
            related_formulas: 相关公式列表
            difficulty_level: 难度级别 (beginner/intermediate/advanced)
        """
        # 构建数学专用系统提示词
        math_system_prompt = self._build_math_system_prompt(
            concept_context=concept_context,
            related_formulas=related_formulas,
            difficulty_level=difficulty_level
        )
        
        return await self.chat(
            message=message,
            system_prompt=math_system_prompt,
            **kwargs
        )
    
    def _get_or_create_context(self, context_id: str) -> ConversationContext:
        """获取或创建对话上下文"""
        if context_id not in self._contexts:
            self._contexts[context_id] = ConversationContext()
        return self._contexts[context_id]
    
    def get_context(self, context_id: str) -> Optional[ConversationContext]:
        """获取对话上下文"""
        return self._contexts.get(context_id)
    
    def clear_context(self, context_id: str):
        """清空指定上下文"""
        if context_id in self._contexts:
            self._contexts[context_id].clear()
    
    def delete_context(self, context_id: str):
        """删除上下文"""
        if context_id in self._contexts:
            del self._contexts[context_id]
    
    def _build_math_system_prompt(
        self,
        concept_context: Optional[List[str]] = None,
        related_formulas: Optional[List[str]] = None,
        difficulty_level: Optional[str] = None
    ) -> str:
        """构建数学专用系统提示词"""
        prompt_parts = [
            "你是一个专业的数学AI助手，擅长形式化数学和Lean 4。",
            "请使用清晰、准确的语言回答数学问题。",
            "对于数学公式，请使用LaTeX格式（用$包围行内公式，$$包围独立公式）。",
        ]
        
        if difficulty_level:
            level_guidance = {
                'beginner': '请用通俗易懂的语言解释，避免过于抽象的表述。',
                'intermediate': '请给出标准的技术性解释，包含必要的定义和定理。',
                'advanced': '请提供深入的数学细节，可以使用形式化语言。'
            }
            prompt_parts.append(level_guidance.get(difficulty_level, ''))
        
        if concept_context:
            prompt_parts.append(f"\n相关概念: {', '.join(concept_context)}")
        
        if related_formulas:
            formulas_text = '\n'.join([f"- ${f}$" for f in related_formulas[:5]])
            prompt_parts.append(f"\n相关公式:\n{formulas_text}")
        
        prompt_parts.append("\n如果涉及证明，请尽可能给出清晰的证明思路或关键步骤。")
        
        return '\n'.join(prompt_parts)
    
    def _extract_latex_formulas(self, text: str) -> List[str]:
        """提取LaTeX公式"""
        import re
        
        formulas = []
        
        # 匹配独立公式 $$...$$
        display_pattern = r'\$\$(.*?)\$\$'
        formulas.extend(re.findall(display_pattern, text, re.DOTALL))
        
        # 匹配行内公式 $...$
        inline_pattern = r'(?<!\$)\$(?!\$)([^\$]+?)\$(?!\$)'
        formulas.extend(re.findall(inline_pattern, text))
        
        return formulas
    
    def _extract_proof_steps(self, text: str) -> List[str]:
        """提取证明步骤"""
        import re
        
        steps = []
        
        # 匹配步骤标记（如"步骤1:", "Step 1:", "第一步:"等）
        step_patterns = [
            r'(?:步骤|Step|第[一二三四五六七八九十\d]+步)[\s:：]+(.+?)(?=\n|$)',
            r'\d+\.\s+(.+?)(?=\n|$)',
        ]
        
        for pattern in step_patterns:
            matches = re.findall(pattern, text, re.IGNORECASE)
            steps.extend(matches)
        
        return steps
    
    def _calculate_confidence(self, text: str) -> float:
        """估算回答的置信度（简单启发式）"""
        confidence = 0.5
        
        # 包含数学符号增加置信度
        math_indicators = ['$', '\\', '证明', '定理', '定义', 'lemma', 'theorem']
        for indicator in math_indicators:
            if indicator in text:
                confidence += 0.05
        
        # 包含证明步骤增加置信度
        if '步骤' in text or 'Step' in text or '证明' in text:
            confidence += 0.1
        
        return min(confidence, 1.0)
    
    def _update_stats(self, latency_ms: float, tokens: int):
        """更新统计信息"""
        self._stats['total_requests'] += 1
        self._stats['total_tokens'] += tokens
        
        # 更新平均延迟
        n = self._stats['total_requests']
        self._stats['avg_latency_ms'] = (
            (self._stats['avg_latency_ms'] * (n - 1) + latency_ms) / n
        )
    
    def get_stats(self) -> Dict:
        """获取使用统计"""
        return {
            **self._stats,
            'active_contexts': len(self._contexts),
            'provider': self.config.provider.value,
            'model': self.config.model
        }


# 全局LLM客户端实例
_llm_client: Optional[LLMClient] = None


def get_llm_client(config: LLMConfig = None) -> LLMClient:
    """获取全局LLM客户端实例"""
    global _llm_client
    if _llm_client is None:
        _llm_client = LLMClient(config)
    return _llm_client
