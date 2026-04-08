"""
LLM提供商实现
支持DeepSeek、OpenAI等
"""
import os
import json
import logging
from abc import ABC, abstractmethod
from typing import Dict, List, Optional, AsyncGenerator, Any
import asyncio

import aiohttp

logger = logging.getLogger(__name__)


class BaseProvider(ABC):
    """LLM提供商基类"""
    
    def __init__(self, api_key: str, base_url: str, model: str):
        self.api_key = api_key
        self.base_url = base_url.rstrip('/')
        self.model = model
        self.session: Optional[aiohttp.ClientSession] = None
    
    async def _get_session(self) -> aiohttp.ClientSession:
        """获取或创建HTTP会话"""
        if self.session is None or self.session.closed:
            self.session = aiohttp.ClientSession(
                headers=self._get_headers(),
                timeout=aiohttp.ClientTimeout(total=60)
            )
        return self.session
    
    @abstractmethod
    def _get_headers(self) -> Dict[str, str]:
        """获取请求头"""
        pass
    
    @abstractmethod
    async def chat(
        self,
        messages: List[Dict[str, str]],
        temperature: float = 0.7,
        max_tokens: int = 4096,
        **kwargs
    ) -> Dict[str, Any]:
        """发送聊天请求"""
        pass
    
    @abstractmethod
    async def chat_stream(
        self,
        messages: List[Dict[str, str]],
        temperature: float = 0.7,
        max_tokens: int = 4096,
        **kwargs
    ) -> AsyncGenerator[str, None]:
        """流式聊天请求"""
        pass
    
    async def close(self):
        """关闭会话"""
        if self.session and not self.session.closed:
            await self.session.close()


class DeepSeekProvider(BaseProvider):
    """DeepSeek LLM提供商"""
    
    def __init__(self, api_key: str, base_url: str = "https://api.deepseek.com", model: str = "deepseek-chat"):
        super().__init__(api_key, base_url, model)
        self.chat_endpoint = f"{self.base_url}/chat/completions"
    
    def _get_headers(self) -> Dict[str, str]:
        return {
            'Authorization': f'Bearer {self.api_key}',
            'Content-Type': 'application/json'
        }
    
    async def chat(
        self,
        messages: List[Dict[str, str]],
        temperature: float = 0.7,
        max_tokens: int = 4096,
        **kwargs
    ) -> Dict[str, Any]:
        """发送聊天请求"""
        session = await self._get_session()
        
        payload = {
            'model': self.model,
            'messages': messages,
            'temperature': temperature,
            'max_tokens': max_tokens,
            **kwargs
        }
        
        try:
            async with session.post(self.chat_endpoint, json=payload) as response:
                if response.status != 200:
                    error_text = await response.text()
                    raise Exception(f"DeepSeek API错误: {response.status} - {error_text}")
                
                data = await response.json()
                
                return {
                    'content': data['choices'][0]['message']['content'],
                    'usage': data.get('usage', {}),
                    'model': data.get('model', self.model),
                    'finish_reason': data['choices'][0].get('finish_reason', '')
                }
        except aiohttp.ClientError as e:
            logger.error(f"DeepSeek请求失败: {e}")
            raise
    
    async def chat_stream(
        self,
        messages: List[Dict[str, str]],
        temperature: float = 0.7,
        max_tokens: int = 4096,
        **kwargs
    ) -> AsyncGenerator[str, None]:
        """流式聊天请求"""
        session = await self._get_session()
        
        payload = {
            'model': self.model,
            'messages': messages,
            'temperature': temperature,
            'max_tokens': max_tokens,
            'stream': True,
            **kwargs
        }
        
        try:
            async with session.post(self.chat_endpoint, json=payload) as response:
                if response.status != 200:
                    error_text = await response.text()
                    raise Exception(f"DeepSeek API错误: {response.status} - {error_text}")
                
                async for line in response.content:
                    line = line.decode('utf-8').strip()
                    if line.startswith('data: '):
                        data_str = line[6:]
                        if data_str == '[DONE]':
                            break
                        
                        try:
                            data = json.loads(data_str)
                            delta = data['choices'][0]['delta']
                            if 'content' in delta:
                                yield delta['content']
                        except (json.JSONDecodeError, KeyError):
                            continue
        except aiohttp.ClientError as e:
            logger.error(f"DeepSeek流式请求失败: {e}")
            raise


class OpenAIProvider(BaseProvider):
    """OpenAI LLM提供商"""
    
    def __init__(
        self,
        api_key: str,
        base_url: str = "https://api.openai.com/v1",
        model: str = "gpt-4"
    ):
        super().__init__(api_key, base_url, model)
        self.chat_endpoint = f"{self.base_url}/chat/completions"
    
    def _get_headers(self) -> Dict[str, str]:
        return {
            'Authorization': f'Bearer {self.api_key}',
            'Content-Type': 'application/json'
        }
    
    async def chat(
        self,
        messages: List[Dict[str, str]],
        temperature: float = 0.7,
        max_tokens: int = 4096,
        **kwargs
    ) -> Dict[str, Any]:
        """发送聊天请求"""
        session = await self._get_session()
        
        payload = {
            'model': self.model,
            'messages': messages,
            'temperature': temperature,
            'max_tokens': max_tokens,
            **kwargs
        }
        
        try:
            async with session.post(self.chat_endpoint, json=payload) as response:
                if response.status != 200:
                    error_text = await response.text()
                    raise Exception(f"OpenAI API错误: {response.status} - {error_text}")
                
                data = await response.json()
                
                return {
                    'content': data['choices'][0]['message']['content'],
                    'usage': data.get('usage', {}),
                    'model': data.get('model', self.model),
                    'finish_reason': data['choices'][0].get('finish_reason', '')
                }
        except aiohttp.ClientError as e:
            logger.error(f"OpenAI请求失败: {e}")
            raise
    
    async def chat_stream(
        self,
        messages: List[Dict[str, str]],
        temperature: float = 0.7,
        max_tokens: int = 4096,
        **kwargs
    ) -> AsyncGenerator[str, None]:
        """流式聊天请求"""
        session = await self._get_session()
        
        payload = {
            'model': self.model,
            'messages': messages,
            'temperature': temperature,
            'max_tokens': max_tokens,
            'stream': True,
            **kwargs
        }
        
        try:
            async with session.post(self.chat_endpoint, json=payload) as response:
                if response.status != 200:
                    error_text = await response.text()
                    raise Exception(f"OpenAI API错误: {response.status} - {error_text}")
                
                async for line in response.content:
                    line = line.decode('utf-8').strip()
                    if line.startswith('data: '):
                        data_str = line[6:]
                        if data_str == '[DONE]':
                            break
                        
                        try:
                            data = json.loads(data_str)
                            delta = data['choices'][0]['delta']
                            if 'content' in delta:
                                yield delta['content']
                        except (json.JSONDecodeError, KeyError):
                            continue
        except aiohttp.ClientError as e:
            logger.error(f"OpenAI流式请求失败: {e}")
            raise
