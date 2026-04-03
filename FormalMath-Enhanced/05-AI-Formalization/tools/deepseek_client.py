"""
DeepSeek API客户端模块
用于调用DeepSeek-Math API进行数学推理和形式化转换
"""

import os
import time
import json
import logging
from typing import Optional, Dict, Any, List, Union
from dataclasses import dataclass
from enum import Enum
import requests
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry

# 配置日志
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)


class FormalizationMode(Enum):
    """形式化模式"""
    NATURAL_TO_LEAN = "natural_to_lean"      # 自然语言到Lean4
    LEAN_TO_NATURAL = "lean_to_natural"      # Lean4到自然语言
    PROOF_GENERATION = "proof_generation"    # 证明生成
    ERROR_CORRECTION = "error_correction"    # 错误修正


@dataclass
class DeepSeekConfig:
    """DeepSeek API配置"""
    api_key: str
    base_url: str = "https://api.deepseek.com/v1"
    model: str = "deepseek-math"
    temperature: float = 0.3
    max_tokens: int = 4096
    timeout: int = 120
    max_retries: int = 3
    retry_delay: float = 2.0


@dataclass
class FormalizationResult:
    """形式化结果"""
    success: bool
    content: str
    mode: FormalizationMode
    tokens_used: int = 0
    latency_ms: float = 0.0
    error_message: Optional[str] = None
    metadata: Optional[Dict[str, Any]] = None


class DeepSeekClient:
    """
    DeepSeek API客户端

    功能：
    - 调用DeepSeek-Math API进行数学推理
    - 将自然语言数学问题转换为形式化陈述
    - 错误处理和重试机制
    """

    # 提示词模板
    PROMPT_TEMPLATES = {
        FormalizationMode.NATURAL_TO_LEAN: """请将以下自然语言数学问题转换为Lean 4代码。

数学问题：
{problem}

要求：
1. 使用标准的Lean 4语法
2. 导入必要的Mathlib4库
3. 包含完整的定理陈述
4. 如果可能，提供证明框架

请输出完整的Lean 4代码：
```lean4
""",

        FormalizationMode.LEAN_TO_NATURAL: """请将以下Lean 4代码解释为自然语言数学陈述。

Lean 4代码：
```lean4
{code}
```

请用清晰的自然语言解释这个定理的内容和意义：
""",

        FormalizationMode.PROOF_GENERATION: """请为以下Lean 4定理生成完整的证明。

定理：
```lean4
{theorem}
```

要求：
1. 使用适当的证明策略
2. 每一步都要有清晰的注释
3. 利用Mathlib4的相关定理

请输出完整的证明代码：
```lean4
""",

        FormalizationMode.ERROR_CORRECTION: """以下Lean 4代码有错误，请修正。

原始代码：
```lean4
{code}
```

错误信息：
{error}

请输出修正后的完整代码：
```lean4
"""
    }

    def __init__(self, config: Optional[DeepSeekConfig] = None):
        """
        初始化客户端

        Args:
            config: API配置，如果为None则从环境变量读取
        """
        if config is None:
            config = DeepSeekConfig(
                api_key=os.getenv("DEEPSEEK_API_KEY", ""),
                base_url=os.getenv("DEEPSEEK_BASE_URL", "https://api.deepseek.com/v1"),
                model=os.getenv("DEEPSEEK_MODEL", "deepseek-math")
            )

        self.config = config
        self.session = self._create_session()

        if not self.config.api_key:
            logger.warning("DeepSeek API key not set. Please set DEEPSEEK_API_KEY environment variable.")

    def _create_session(self) -> requests.Session:
        """创建带重试机制的HTTP会话"""
        session = requests.Session()

        retry_strategy = Retry(
            total=self.config.max_retries,
            backoff_factor=1,
            status_forcelist=[429, 500, 502, 503, 504],
            allowed_methods=["POST", "GET"]
        )

        adapter = HTTPAdapter(max_retries=retry_strategy)
        session.mount("https://", adapter)
        session.mount("http://", adapter)

        return session

    def _build_prompt(self, mode: FormalizationMode, **kwargs) -> str:
        """构建提示词"""
        template = self.PROMPT_TEMPLATES.get(mode)
        if not template:
            raise ValueError(f"Unknown mode: {mode}")

        try:
            return template.format(**kwargs)
        except KeyError as e:
            raise ValueError(f"Missing required parameter for prompt: {e}")

    def _call_api(self, prompt: str) -> Dict[str, Any]:
        """
        调用DeepSeek API

        Args:
            prompt: 提示词

        Returns:
            API响应
        """
        headers = {
            "Authorization": f"Bearer {self.config.api_key}",
            "Content-Type": "application/json"
        }

        payload = {
            "model": self.config.model,
            "messages": [
                {
                    "role": "system",
                    "content": "You are an expert in mathematical formalization, specializing in Lean 4 and Mathlib4."
                },
                {
                    "role": "user",
                    "content": prompt
                }
            ],
            "temperature": self.config.temperature,
            "max_tokens": self.config.max_tokens
        }

        url = f"{self.config.base_url}/chat/completions"

        for attempt in range(self.config.max_retries):
            try:
                response = self.session.post(
                    url,
                    headers=headers,
                    json=payload,
                    timeout=self.config.timeout
                )
                response.raise_for_status()
                return response.json()

            except requests.exceptions.Timeout:
                logger.warning(f"Request timeout (attempt {attempt + 1}/{self.config.max_retries})")
                if attempt < self.config.max_retries - 1:
                    time.sleep(self.config.retry_delay * (2 ** attempt))
                else:
                    raise

            except requests.exceptions.RequestException as e:
                logger.error(f"API request failed: {e}")
                if attempt < self.config.max_retries - 1:
                    time.sleep(self.config.retry_delay * (2 ** attempt))
                else:
                    raise

        raise RuntimeError("Max retries exceeded")

    def _extract_lean_code(self, content: str) -> str:
        """从响应中提取Lean代码"""
        # 尝试从代码块中提取
        import re

        # 匹配 ```lean4 或 ```lean 代码块
        patterns = [
            r'```lean4\n(.*?)```',
            r'```lean\n(.*?)```',
            r'```\n(.*?)```'
        ]

        for pattern in patterns:
            match = re.search(pattern, content, re.DOTALL)
            if match:
                return match.group(1).strip()

        # 如果没有代码块，返回原始内容
        return content.strip()

    def formalize(self,
                  problem: str,
                  mode: FormalizationMode = FormalizationMode.NATURAL_TO_LEAN,
                  **kwargs) -> FormalizationResult:
        """
        执行形式化转换

        Args:
            problem: 数学问题或代码
            mode: 形式化模式
            **kwargs: 额外参数

        Returns:
            形式化结果
        """
        start_time = time.time()

        try:
            # 构建提示词
            if mode == FormalizationMode.NATURAL_TO_LEAN:
                prompt = self._build_prompt(mode, problem=problem)
            elif mode == FormalizationMode.LEAN_TO_NATURAL:
                prompt = self._build_prompt(mode, code=problem)
            elif mode == FormalizationMode.PROOF_GENERATION:
                prompt = self._build_prompt(mode, theorem=problem)
            elif mode == FormalizationMode.ERROR_CORRECTION:
                error = kwargs.get("error", "Unknown error")
                prompt = self._build_prompt(mode, code=problem, error=error)
            else:
                raise ValueError(f"Unsupported mode: {mode}")

            # 调用API
            response = self._call_api(prompt)

            # 解析响应
            choice = response["choices"][0]
            content = choice["message"]["content"]

            # 提取Lean代码（如果是代码生成模式）
            if mode in [FormalizationMode.NATURAL_TO_LEAN,
                       FormalizationMode.PROOF_GENERATION,
                       FormalizationMode.ERROR_CORRECTION]:
                content = self._extract_lean_code(content)

            latency = (time.time() - start_time) * 1000
            tokens_used = response.get("usage", {}).get("total_tokens", 0)

            return FormalizationResult(
                success=True,
                content=content,
                mode=mode,
                tokens_used=tokens_used,
                latency_ms=latency,
                metadata={
                    "model": response.get("model"),
                    "finish_reason": choice.get("finish_reason")
                }
            )

        except Exception as e:
            latency = (time.time() - start_time) * 1000
            logger.error(f"Formalization failed: {e}")

            return FormalizationResult(
                success=False,
                content="",
                mode=mode,
                latency_ms=latency,
                error_message=str(e)
            )

    def batch_formalize(self,
                       problems: List[str],
                       mode: FormalizationMode = FormalizationMode.NATURAL_TO_LEAN,
                       delay: float = 1.0) -> List[FormalizationResult]:
        """
        批量形式化

        Args:
            problems: 问题列表
            mode: 形式化模式
            delay: 请求间隔（秒）

        Returns:
            结果列表
        """
        results = []

        for i, problem in enumerate(problems):
            logger.info(f"Processing {i+1}/{len(problems)}...")
            result = self.formalize(problem, mode)
            results.append(result)

            if i < len(problems) - 1:
                time.sleep(delay)

        return results

    def interactive_formalize(self) -> None:
        """交互式形式化（用于测试）"""
        print("=" * 60)
        print("DeepSeek Math Formalization Tool")
        print("=" * 60)
        print("\nModes:")
        print("1. Natural Language to Lean 4")
        print("2. Lean 4 to Natural Language")
        print("3. Proof Generation")
        print("4. Error Correction")
        print("q. Quit")
        print("-" * 60)

        while True:
            choice = input("\nSelect mode (1-4, q): ").strip().lower()

            if choice == 'q':
                break

            if choice == '1':
                mode = FormalizationMode.NATURAL_TO_LEAN
                problem = input("Enter mathematical problem:\n")
                result = self.formalize(problem, mode)

            elif choice == '2':
                mode = FormalizationMode.LEAN_TO_NATURAL
                print("Enter Lean 4 code (end with EOF):")
                lines = []
                while True:
                    line = input()
                    if line.strip() == 'EOF':
                        break
                    lines.append(line)
                code = '\n'.join(lines)
                result = self.formalize(code, mode)

            elif choice == '3':
                mode = FormalizationMode.PROOF_GENERATION
                print("Enter theorem (end with EOF):")
                lines = []
                while True:
                    line = input()
                    if line.strip() == 'EOF':
                        break
                    lines.append(line)
                theorem = '\n'.join(lines)
                result = self.formalize(theorem, mode)

            elif choice == '4':
                mode = FormalizationMode.ERROR_CORRECTION
                print("Enter code (end with EOF):")
                lines = []
                while True:
                    line = input()
                    if line.strip() == 'EOF':
                        break
                    lines.append(line)
                code = '\n'.join(lines)
                error = input("Enter error message: ")
                result = self.formalize(code, mode, error=error)

            else:
                print("Invalid choice")
                continue

            print("\n" + "=" * 60)
            if result.success:
                print(f"✓ Success (Latency: {result.latency_ms:.2f}ms, Tokens: {result.tokens_used})")
                print("-" * 60)
                print(result.content)
            else:
                print(f"✗ Failed: {result.error_message}")
            print("=" * 60)


# 便捷函数
def formalize_problem(problem: str, api_key: Optional[str] = None) -> str:
    """
    快速形式化数学问题

    Args:
        problem: 自然语言数学问题
        api_key: DeepSeek API密钥（可选，默认从环境变量读取）

    Returns:
        Lean 4代码
    """
    config = None
    if api_key:
        config = DeepSeekConfig(api_key=api_key)

    client = DeepSeekClient(config)
    result = client.formalize(problem, FormalizationMode.NATURAL_TO_LEAN)

    if result.success:
        return result.content
    else:
        raise RuntimeError(f"Formalization failed: {result.error_message}")


if __name__ == "__main__":
    # 示例用法
    client = DeepSeekClient()
    client.interactive_formalize()
