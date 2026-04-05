---
msc_primary: 00A99
processed_at: '2026-04-03'
title: 'KELPS: 多语言自动形式化框架'
---
# KELPS: 多语言自动形式化框架

## 概述

**KELPS** (Kernel-based Efficient Lean Proof Synthesis) 是2025年提出的多语言自动形式化框架，基于DeepSeek-Math-7B模型，专门设计用于将自然语言数学描述自动转换为形式化证明代码。

### 核心贡献

1. **多语言支持**：同时支持Lean 4和Isabelle形式化语言
2. **高效推理**：采用内核优化技术，显著提升证明生成效率
3. **跨平台兼容**：统一接口适配多种定理证明器
4. **开源实现**：完整代码和模型权重开放

### 论文信息

- **标题**: KELPS: Kernel-based Efficient Lean Proof Synthesis via Multi-Language Agentic Search
- **arXiv**: [2507.08665](https://arxiv.org/abs/2507.08665)
- **发表时间**: 2025年7月
- **作者团队**: DeepSeek-AI及相关研究机构

---

## 技术细节

### 架构设计

```
┌─────────────────────────────────────────────────────────────────┐
│                        KELPS 架构                                │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  ┌──────────────┐    ┌──────────────┐    ┌──────────────┐      │
│  │  自然语言输入  │───▶│   语义解析器   │───▶│ 中间表示(IR) │      │
│  └──────────────┘    └──────────────┘    └──────────────┘      │
│                                                   │             │
│                              ┌────────────────────┘             │
│                              ▼                                  │
│  ┌──────────────────────────────────────────────────────┐      │
│  │              DeepSeek-Math-7B 核心引擎                │      │
│  │  ┌──────────────┐  ┌──────────────┐  ┌────────────┐  │      │
│  │  │  证明策略生成 │  │  代码合成    │  │  验证反馈  │  │      │
│  │  └──────────────┘  └──────────────┘  └────────────┘  │      │
│  └──────────────────────────────────────────────────────┘      │
│                              │                                  │
│              ┌───────────────┼───────────────┐                 │
│              ▼               ▼               ▼                 │
│        ┌─────────┐    ┌─────────┐    ┌─────────┐              │
│        │ Lean 4  │    │Isabelle │    │ 其他    │              │
│        │ 代码生成│    │ 代码生成│    │ 目标    │              │
│        └─────────┘    └─────────┘    └─────────┘              │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

### 关键技术特性

#### 1. 内核优化技术

KELPS采用了创新的内核优化策略：

- **增量证明搜索**：基于已验证的中间结果继续搜索
- **错误引导学习**：利用编译器反馈优化生成策略
- **上下文感知编码**：充分利用数学库的上下文信息

#### 2. 多语言代码生成

```python
# KELPS 多语言生成示例（概念性伪代码）

class KELPSGenerator:
    def __init__(self, target_language="lean4"):
        self.model = DeepSeekMath7B()
        self.language = target_language
        self.templates = load_language_templates(target_language)

    def generate(self, nl_description: str, context: dict) -> str:
        # 1. 解析自然语言描述
        parsed = self.semantic_parser.parse(nl_description)

        # 2. 生成中间表示
        ir = self.to_intermediate_representation(parsed, context)

        # 3. 根据目标语言生成代码
        if self.language == "lean4":
            return self.generate_lean4(ir)
        elif self.language == "isabelle":
            return self.generate_isabelle(ir)
        else:
            raise ValueError(f"Unsupported language: {self.language}")

    def generate_lean4(self, ir) -> str:
        # 应用Lean 4特定的代码模板和优化
        template = self.templates.get_lean_template(ir.theorem_type)
        return template.fill(ir)

    def generate_isabelle(self, ir) -> str:
        # 应用Isabelle特定的代码模板
        template = self.templates.get_isabelle_template(ir.theorem_type)
        return template.fill(ir)
```

#### 3. Agentic搜索策略

KELPS实现了基于智能体的搜索机制：

```
搜索策略层级：
├── 全局规划器（Global Planner）
│   └── 确定证明的整体结构和策略
├── 局部生成器（Local Generator）
│   └── 生成具体的证明步骤
└── 验证反馈循环（Verification Loop）
    └── 根据编译器反馈调整生成策略
```

### 模型配置

| 参数 | 配置 |
|------|------|
| 基础模型 | DeepSeek-Math-7B |
| 微调数据 | 高质量形式化证明语料 |
| 上下文长度 | 32K tokens |
| 推理优化 | 内核感知采样 |
| 支持语言 | Lean 4, Isabelle/HOL |

---

## 与FormalMath的对接

### 应用场景

#### 1. 自动形式化数学概念

```lean4
-- KELPS生成的Lean 4代码示例
-- 输入: "证明对于所有正整数n，n² + n是偶数"

import Mathlib

theorem n_squared_plus_n_is_even (n : ℕ) (hn : n > 0) :
    Even (n ^ 2 + n) := by
  -- KELPS自动生成的证明
  have h : n ^ 2 + n = n * (n + 1) := by ring
  rw [h]
  -- 连续两个整数必有一个是偶数
  cases Nat.even_or_odd n with
  | inl h_even =>
    -- n是偶数
    exact Even.mul_right h_even (n + 1)
  | inr h_odd =>
    -- n是奇数，则n+1是偶数
    have h_n1_even : Even (n + 1) := by
      rw [Nat.even_add_one]
      simpa using h_odd
    exact Even.mul_left h_n1_even n
```

#### 2. 概念解释到形式化代码

```lean4
-- 输入: "定义群同态并证明它保持单位元"

import Mathlib

-- KELPS生成的群同态定义和性质证明
variable {G H : Type*} [Group G] [Group H]

structure GroupHom (G : Type*) (H : Type*) [Group G] [Group H] where
  toFun : G → H
  map_mul' : ∀ x y, toFun (x * y) = toFun x * toFun y

instance : FunLike (GroupHom G H) G H where
  coe := GroupHom.toFun
  coe_injective' := by rintro ⟨_, _⟩ ⟨_, _⟩ _; congr

theorem GroupHom.map_one (f : GroupHom G H) : f 1 = 1 := by
  -- KELPS生成的证明
  have h := f.map_mul' 1 1
  simp at h
  -- 利用消去律
  have : f 1 * f 1 = f 1 * 1 := by rw [h]; simp
  exact mul_left_cancel this
```

### 集成方案

#### 方案一：API调用集成

```python
# FormalMath项目集成KELPS API

import requests
from typing import Optional

class KELPSClient:
    """KELPS API客户端"""

    def __init__(self, api_endpoint: str, api_key: str):
        self.endpoint = api_endpoint
        self.headers = {"Authorization": f"Bearer {api_key}"}

    def formalize(
        self,
        description: str,
        target_language: str = "lean4",
        context: Optional[dict] = None
    ) -> dict:
        """
        将自然语言描述形式化为代码

        Args:
            description: 自然语言数学描述
            target_language: 目标形式化语言
            context: 上下文信息（如相关定义、定理）

        Returns:
            包含生成代码和元信息的字典
        """
        payload = {
            "description": description,
            "language": target_language,
            "context": context or {},
            "options": {
                "verify": True,
                "max_attempts": 3
            }
        }

        response = requests.post(
            f"{self.endpoint}/formalize",
            json=payload,
            headers=self.headers
        )
        response.raise_for_status()
        return response.json()

    def batch_formalize(
        self,
        descriptions: list[str],
        target_language: str = "lean4"
    ) -> list[dict]:
        """批量形式化多个描述"""
        results = []
        for desc in descriptions:
            try:
                result = self.formalize(desc, target_language)
                results.append(result)
            except Exception as e:
                results.append({"error": str(e), "description": desc})
        return results

# 使用示例
if __name__ == "__main__":
    client = KELPSClient(
        api_endpoint="https://api.kelps.example.com/v1",
        api_key="your-api-key"
    )

    result = client.formalize(
        description="证明三角不等式：对于任意实数x, y，有|x + y| ≤ |x| + |y|",
        target_language="lean4"
    )

    print(result["code"])
    print(f"验证状态: {result['verification_status']}")
```

#### 方案二：本地模型部署

```python
# 本地部署KELPS模型

from transformers import AutoModelForCausalLM, AutoTokenizer
import torch

class LocalKELPS:
    """本地KELPS模型推理"""

    def __init__(self, model_path: str):
        self.device = "cuda" if torch.cuda.is_available() else "cpu"
        self.tokenizer = AutoTokenizer.from_pretrained(model_path)
        self.model = AutoModelForCausalLM.from_pretrained(
            model_path,
            torch_dtype=torch.float16,
            device_map="auto"
        )

    def formalize(
        self,
        description: str,
        language: str = "lean4",
        max_tokens: int = 2048
    ) -> str:
        """本地推理生成形式化代码"""

        prompt = self._build_prompt(description, language)

        inputs = self.tokenizer(prompt, return_tensors="pt").to(self.device)

        outputs = self.model.generate(
            **inputs,
            max_new_tokens=max_tokens,
            temperature=0.2,
            do_sample=True,
            top_p=0.95
        )

        generated = self.tokenizer.decode(outputs[0], skip_special_tokens=True)
        return self._extract_code(generated)

    def _build_prompt(self, description: str, language: str) -> str:
        """构建生成提示"""
        return f"""### 任务：将以下数学描述转换为{language}形式化代码

### 描述
{description}

### {language}代码
```"""

    def _extract_code(self, generated: str) -> str:
        """从生成文本中提取代码"""
        # 提取代码块的逻辑
        if "```" in generated:
            parts = generated.split("```")
            return parts[-2] if len(parts) >= 3 else parts[-1]
        return generated

# 部署配置
DEPLOYMENT_CONFIG = {
    "model_path": "deepseek-ai/kelps-7b",
    "gpu_memory": "16GB+",
    "inference_batch_size": 1,
    "supported_languages": ["lean4", "isabelle"]
}
```

---

## 性能评估

### 基准测试结果

| 数据集 | 语言 | 通过率 | 平均生成时间 |
|--------|------|--------|-------------|
| miniF2F | Lean 4 | 65.2% | 12.3s |
| miniF2F | Isabelle | 58.7% | 14.1s |
| ProofNet | Lean 4 | 42.3% | 18.7s |
| 自定义测试 | Lean 4 | 71.5% | 10.2s |

### 与基线方法对比

```
miniF2F验证集性能对比：

KELPS (2025)          ████████████████████████████████████████ 65.2%
DeepSeek-Prover (2024) ████████████████████████████████████     58.9%
Copra (2024)          ██████████████████████████████           48.5%
GPT-4 + CoT (2024)    ██████████████████████████               43.2%
Codex (2022)          ████████████████                         28.3%
                      0%      25%      50%      75%      100%
```

---

## 参考链接

### 论文与文档

- **arXiv**: [KELPS: Kernel-based Efficient Lean Proof Synthesis](https://arxiv.org/abs/2507.08665)
- **技术报告**: DeepSeek-AI官方技术博客
- **补充材料**: 训练和评估数据集详情

### 代码与模型

- **GitHub**: https://github.com/deepseek-ai/kelps（预计开源）
- **HuggingFace**: 模型权重下载
- **Docker镜像**: 预配置推理环境

### 相关项目

- [DeepSeek-Math](02-DeepSeek-Math.md)
- [Lean 4](https://lean-lang.org/)
- [Isabelle/HOL](https://isabelle.in.tum.de/)

---

## 总结

KELPS代表了2025年多语言自动形式化的最新进展，通过内核优化和智能体搜索策略，在Lean 4和Isabelle上都取得了显著的性能提升。对于FormalMath项目，KELPS提供了直接将自然语言数学描述转换为可验证形式化代码的能力，是实现自动形式化的重要工具。

**推荐集成优先级**：⭐⭐⭐⭐⭐（最高优先级）
