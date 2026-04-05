---
msc_primary: 00A99
processed_at: '2026-04-03'
title: AI形式化数学代码示例与工具链接
---
# AI形式化数学代码示例与工具链接

本文档提供与AI形式化数学相关的实用代码示例和工具资源链接，帮助开发者快速上手和集成相关技术。

---

## 1. 环境配置

### Lean 4开发环境

```bash
# Windows安装Lean 4
# 方法1：使用elan（推荐）
curl -O --location https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1
powershell -ExecutionPolicy Bypass -f elan-init.ps1

# 方法2：使用VS Code插件
# 1. 安装VS Code
# 2. 在扩展商店搜索并安装 "Lean 4"
# 3. 插件会自动安装所需的Lean工具链

# 验证安装
lean --version
# 输出类似：Lean (version 4.7.0, commit 6fce8f7, Release)
```

### Python环境配置

```bash
# 创建虚拟环境
python -m venv formalmath-ai-env

# 激活环境
# Windows:
formalmath-ai-env\Scripts\activate
# Linux/Mac:
source formalmath-ai-env/bin/activate

# 安装依赖
pip install transformers torch numpy datasets fastapi uvicorn
pip install openai anthropic  # API客户端
pip install python-lean  # Lean Python接口（如有）
```

### 创建项目结构

```bash
# 创建FormalMath AI项目结构
mkdir -p formalmath-ai/{src,data,models,tests,docs}
cd formalmath-ai

# 初始化项目
git init

# 创建基本文件
touch README.md requirements.txt .gitignore
```

---

## 2. DeepSeek-Math集成示例

### 基础推理示例

```python
# examples/deepseek_basic.py

from transformers import AutoModelForCausalLM, AutoTokenizer
import torch

class DeepSeekMathSolver:
    """DeepSeek-Math基础封装"""

    def __init__(self, model_name="deepseek-ai/deepseek-math-7b-rl"):
        print(f"正在加载模型: {model_name}")

        self.tokenizer = AutoTokenizer.from_pretrained(
            model_name,
            trust_remote_code=True
        )

        self.model = AutoModelForCausalLM.from_pretrained(
            model_name,
            trust_remote_code=True,
            torch_dtype=torch.float16,
            device_map="auto"
        )

        print("模型加载完成")

    def solve(self, problem: str, max_length: int = 2048) -> str:
        """解决数学问题"""

        # 构建提示
        prompt = f"""请详细解答以下数学问题：

问题：{problem}

请给出详细的解答过程：
"""

        # 编码输入
        inputs = self.tokenizer(
            prompt,
            return_tensors="pt",
            truncation=True,
            max_length=1024
        ).to(self.model.device)

        # 生成解答
        with torch.no_grad():
            outputs = self.model.generate(
                **inputs,
                max_new_tokens=max_length,
                temperature=0.3,
                top_p=0.95,
                do_sample=True,
                pad_token_id=self.tokenizer.eos_token_id
            )

        # 解码输出
        solution = self.tokenizer.decode(
            outputs[0][inputs.input_ids.shape[1]:],
            skip_special_tokens=True
        )

        return solution.strip()

    def batch_solve(self, problems: list[str]) -> list[str]:
        """批量解决问题"""
        return [self.solve(p) for p in problems]

# 使用示例
if __name__ == "__main__":
    solver = DeepSeekMathSolver()

    # 测试问题
    problems = [
        "证明：对于任意正整数n，n³ - n 能被6整除。",
        "求函数 f(x) = x² - 4x + 5 的最小值。",
        "证明 √2 是无理数。"
    ]

    for i, problem in enumerate(problems, 1):
        print(f"\n{'='*60}")
        print(f"问题 {i}: {problem}")
        print(f"{'='*60}")

        solution = solver.solve(problem)
        print(f"\n解答:\n{solution}")
```

### API调用示例

```python
# examples/deepseek_api.py

import requests
import json
from typing import Optional

class DeepSeekAPIClient:
    """DeepSeek API客户端"""

    def __init__(self, api_key: str, base_url: str = "https://api.deepseek.com"):
        self.api_key = api_key
        self.base_url = base_url
        self.headers = {
            "Authorization": f"Bearer {api_key}",
            "Content-Type": "application/json"
        }

    def chat_completion(
        self,
        messages: list[dict],
        model: str = "deepseek-math",
        temperature: float = 0.3,
        max_tokens: int = 2048
    ) -> dict:
        """调用聊天补全API"""

        payload = {
            "model": model,
            "messages": messages,
            "temperature": temperature,
            "max_tokens": max_tokens
        }

        response = requests.post(
            f"{self.base_url}/v1/chat/completions",
            headers=self.headers,
            json=payload
        )

        response.raise_for_status()
        return response.json()

    def solve_math_problem(
        self,
        problem: str,
        show_reasoning: bool = True
    ) -> dict:
        """专门用于解决数学问题"""

        system_prompt = """你是一位专业的数学家。请：
1. 仔细分析问题
2. 给出清晰的解题步骤
3. 验证答案的正确性
4. 如有多种解法，选择最简洁的一种"""

        messages = [
            {"role": "system", "content": system_prompt},
            {"role": "user", "content": f"请解决以下数学问题：\n\n{problem}"}
        ]

        result = self.chat_completion(messages)

        return {
            "problem": problem,
            "solution": result["choices"][0]["message"]["content"],
            "model": result["model"],
            "usage": result["usage"]
        }

# 使用示例
if __name__ == "__main__":
    import os

    # 从环境变量获取API密钥
    api_key = os.getenv("DEEPSEEK_API_KEY")
    if not api_key:
        print("请设置 DEEPSEEK_API_KEY 环境变量")
        exit(1)

    client = DeepSeekAPIClient(api_key)

    # 解决问题
    result = client.solve_math_problem(
        "证明：对于任意实数x, y，有 |x + y| ≤ |x| + |y|"
    )

    print(f"问题: {result['problem']}")
    print(f"\n解答:\n{result['solution']}")
    print(f"\nToken使用: {result['usage']}")
```

---

## 3. Lean 4自动化工具

### Lean代码验证器

```python
# examples/lean_verifier.py

import subprocess
import tempfile
import os
from pathlib import Path

class LeanVerifier:
    """Lean 4代码验证工具"""

    def __init__(self, lean_path: str = "lean"):
        self.lean_path = lean_path
        self._check_lean_installation()

    def _check_lean_installation(self):
        """检查Lean安装"""
        try:
            result = subprocess.run(
                [self.lean_path, "--version"],
                capture_output=True,
                text=True
            )
            if result.returncode != 0:
                raise RuntimeError("Lean 4未正确安装")
            print(f"Lean版本: {result.stdout.strip()}")
        except FileNotFoundError:
            raise RuntimeError(f"找不到Lean命令: {self.lean_path}")

    def verify(self, code: str, timeout: int = 30) -> dict:
        """
        验证Lean 4代码

        Returns:
            {
                "valid": bool,
                "errors": list[str],
                "warnings": list[str],
                "time": float
            }
        """
        # 创建临时文件
        with tempfile.NamedTemporaryFile(
            mode='w',
            suffix='.lean',
            delete=False
        ) as f:
            f.write(code)
            temp_file = f.name

        try:
            import time
            start_time = time.time()

            # 运行Lean检查
            result = subprocess.run(
                [self.lean_path, temp_file],
                capture_output=True,
                text=True,
                timeout=timeout
            )

            elapsed_time = time.time() - start_time

            # 解析输出
            errors = []
            warnings = []

            for line in result.stderr.split('\n'):
                if 'error:' in line:
                    errors.append(line)
                elif 'warning:' in line:
                    warnings.append(line)

            return {
                "valid": result.returncode == 0,
                "errors": errors,
                "warnings": warnings,
                "time": elapsed_time,
                "return_code": result.returncode
            }

        except subprocess.TimeoutExpired:
            return {
                "valid": False,
                "errors": ["验证超时"],
                "warnings": [],
                "time": timeout,
                "return_code": -1
            }
        finally:
            os.unlink(temp_file)

    def verify_file(self, file_path: str, timeout: int = 60) -> dict:
        """验证Lean文件"""
        with open(file_path, 'r', encoding='utf-8') as f:
            code = f.read()
        return self.verify(code, timeout)

# 使用示例
if __name__ == "__main__":
    verifier = LeanVerifier()

    # 测试代码
    test_code = """
import Mathlib

theorem test_theorem (n : ℕ) : n + 0 = n := by
  simp
"""

    result = verifier.verify(test_code)

    print(f"验证结果: {'通过' if result['valid'] else '失败'}")
    print(f"耗时: {result['time']:.2f}秒")

    if result['errors']:
        print(f"\n错误 ({len(result['errors'])}):")
        for err in result['errors']:
            print(f"  - {err}")

    if result['warnings']:
        print(f"\n警告 ({len(result['warnings'])}):")
        for warn in result['warnings']:
            print(f"  - {warn}")
```

### Lean代码生成器模板

```python
# examples/lean_generator.py

from dataclasses import dataclass
from typing import Optional, List

@dataclass
class LeanTheorem:
    """Lean定理表示"""
    name: str
    statement: str
    proof: Optional[str] = None
    imports: List[str] = None

    def __post_init__(self):
        if self.imports is None:
            self.imports = ["Mathlib"]

    def to_code(self) -> str:
        """生成完整的Lean代码"""
        code = "\n".join(f"import {imp}" for imp in self.imports)
        code += f"\n\ntheorem {self.name} {self.statement}"

        if self.proof:
            code += f" := by\n  {self.proof}"
        else:
            code += " := by\n  sorry"

        return code

class LeanCodeGenerator:
    """Lean代码生成器"""

    def __init__(self):
        self.templates = self._load_templates()

    def _load_templates(self) -> dict:
        """加载代码模板"""
        return {
            "number_theory": {
                "imports": ["Mathlib"],
                "common_tactics": ["norm_num", "omega", "nlinarith"]
            },
            "algebra": {
                "imports": ["Mathlib.Algebra"],
                "common_tactics": ["ring", "field_simp", "nlinarith"]
            },
            "geometry": {
                "imports": ["Mathlib.Geometry"],
                "common_tactics": ["simp", "rw", "apply"]
            }
        }

    def generate_theorem(
        self,
        name: str,
        description: str,
        domain: str = "number_theory"
    ) -> LeanTheorem:
        """
        根据描述生成定理框架

        注意：这只是框架，具体内容需要根据描述填充
        """
        template = self.templates.get(domain, self.templates["number_theory"])

        # 这里应该接入AI模型进行实际转换
        # 目前返回示例框架
        statement = "(n : ℕ) : n = n"  # 占位符

        return LeanTheorem(
            name=name,
            statement=statement,
            imports=template["imports"]
        )

    def generate_proof_skeleton(self, theorem: LeanTheorem) -> str:
        """生成证明骨架"""
        # 根据定理类型生成不同的证明骨架
        skeleton = """-- 证明思路：
-- 1. 首先明确目标
-- 2. 考虑使用的基础引理
-- 3. 分步推导

intro n
-- 在此添加证明步骤
sorry
"""
        return skeleton

# 使用示例
if __name__ == "__main__":
    generator = LeanCodeGenerator()

    # 生成定理
    theorem = generator.generate_theorem(
        name="sum_of_first_n",
        description="前n个自然数的和等于n(n+1)/2",
        domain="number_theory"
    )

    print("生成的Lean代码：")
    print("=" * 60)
    print(theorem.to_code())
    print("=" * 60)
```

---

## 4. IMO Lean数据集处理

### 数据集加载器

```python
# examples/imo_dataset_loader.py

import json
from pathlib import Path
from typing import Iterator, Dict, List
from dataclasses import dataclass

@dataclass
class IMOProblem:
    """IMO题目数据结构"""
    year: int
    number: int
    domain: str
    statement: str
    formal_statement: str
    formal_proof: str = ""
    difficulty: str = "unknown"

    @property
    def id(self) -> str:
        return f"imo{self.year}_q{self.number}"

class IMODatasetLoader:
    """IMO Lean数据集加载器"""

    def __init__(self, dataset_path: str):
        self.dataset_path = Path(dataset_path)
        if not self.dataset_path.exists():
            raise FileNotFoundError(f"数据集路径不存在: {dataset_path}")

    def load_all(self) -> List[IMOProblem]:
        """加载所有题目"""
        problems = []

        # 遍历年份目录
        for year_dir in sorted(self.dataset_path.glob("imo*")):
            if not year_dir.is_dir():
                continue

            year = int(year_dir.name[3:])

            # 加载该年份的题目
            for problem_file in sorted(year_dir.glob("*.json")):
                problem = self._load_problem_file(problem_file, year)
                if problem:
                    problems.append(problem)

        return problems

    def _load_problem_file(self, file_path: Path, year: int) -> Optional[IMOProblem]:
        """加载单个题目文件"""
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                data = json.load(f)

            # 提取题号
            number = int(file_path.stem.split('_q')[1])

            return IMOProblem(
                year=year,
                number=number,
                domain=data.get("domain", "unknown"),
                statement=data.get("statement", ""),
                formal_statement=data.get("formal_statement", ""),
                formal_proof=data.get("formal_proof", ""),
                difficulty=data.get("difficulty", "unknown")
            )
        except Exception as e:
            print(f"加载文件失败 {file_path}: {e}")
            return None

    def load_by_year(self, year: int) -> List[IMOProblem]:
        """按年份加载题目"""
        all_problems = self.load_all()
        return [p for p in all_problems if p.year == year]

    def load_by_domain(self, domain: str) -> List[IMOProblem]:
        """按领域加载题目"""
        all_problems = self.load_all()
        return [p for p in all_problems if p.domain == domain]

    def iterate_problems(self) -> Iterator[IMOProblem]:
        """迭代所有题目"""
        yield from self.load_all()

    def get_statistics(self) -> Dict:
        """获取数据集统计信息"""
        problems = self.load_all()

        stats = {
            "total_problems": len(problems),
            "by_year": {},
            "by_domain": {},
            "with_proofs": sum(1 for p in problems if p.formal_proof),
        }

        for p in problems:
            stats["by_year"][p.year] = stats["by_year"].get(p.year, 0) + 1
            stats["by_domain"][p.domain] = stats["by_domain"].get(p.domain, 0) + 1

        return stats

# 使用示例
if __name__ == "__main__":
    # 假设数据集路径
    loader = IMODatasetLoader("/path/to/imo_lean/dataset")

    # 获取统计信息
    stats = loader.get_statistics()
    print("数据集统计：")
    print(f"  总题目数: {stats['total_problems']}")
    print(f"  有形式化证明: {stats['with_proofs']}")
    print(f"\n按领域分布:")
    for domain, count in sorted(stats["by_domain"].items()):
        print(f"  {domain}: {count}")

    # 加载特定年份
    problems_2023 = loader.load_by_year(2023)
    print(f"\n2023年题目数: {len(problems_2023)}")

    # 遍历所有题目
    for problem in loader.iterate_problems():
        print(f"{problem.id}: {problem.statement[:50]}...")
```

### 评估基准工具

```python
# examples/evaluation_benchmark.py

from typing import Callable, Dict, List
from dataclasses import dataclass
import time

@dataclass
class EvaluationResult:
    """评估结果"""
    problem_id: str
    success: bool
    generated_code: str
    syntax_correct: bool
    semantic_match: bool
    execution_time: float
    error_message: str = ""

class FormalizationBenchmark:
    """形式化评估基准"""

    def __init__(self, dataset_loader, verifier):
        self.loader = dataset_loader
        self.verifier = verifier

    def evaluate_model(
        self,
        model: Callable[[str], str],
        sample_size: int = None,
        verbose: bool = True
    ) -> Dict:
        """
        评估形式化模型

        Args:
            model: 形式化模型，输入自然语言，输出Lean代码
            sample_size: 评估样本数，None表示全部
            verbose: 是否打印详细进度

        Returns:
            评估结果统计
        """
        problems = self.loader.load_all()
        if sample_size:
            import random
            problems = random.sample(problems, min(sample_size, len(problems)))

        results = []

        for i, problem in enumerate(problems):
            if verbose:
                print(f"\n评估进度: {i+1}/{len(problems)} - {problem.id}")

            result = self._evaluate_single(model, problem)
            results.append(result)

            if verbose:
                status = "✓" if result.success else "✗"
                print(f"  结果: {status} (语法: {result.syntax_correct}, 语义: {result.semantic_match})")

        # 计算统计指标
        total = len(results)
        successful = sum(1 for r in results if r.success)
        syntax_correct = sum(1 for r in results if r.syntax_correct)

        return {
            "total": total,
            "successful": successful,
            "success_rate": successful / total if total > 0 else 0,
            "syntax_correct_rate": syntax_correct / total if total > 0 else 0,
            "average_time": sum(r.execution_time for r in results) / total if total > 0 else 0,
            "detailed_results": results
        }

    def _evaluate_single(
        self,
        model: Callable[[str], str],
        problem
    ) -> EvaluationResult:
        """评估单个问题"""
        start_time = time.time()

        try:
            # 生成形式化代码
            generated_code = model(problem.statement)

            # 验证语法
            verification = self.verifier.verify(generated_code)
            syntax_correct = verification["valid"]

            # 语义匹配检查（简化版）
            semantic_match = self._check_semantic_match(
                generated_code,
                problem.formal_statement
            )

            success = syntax_correct and semantic_match

            return EvaluationResult(
                problem_id=problem.id,
                success=success,
                generated_code=generated_code,
                syntax_correct=syntax_correct,
                semantic_match=semantic_match,
                execution_time=time.time() - start_time
            )

        except Exception as e:
            return EvaluationResult(
                problem_id=problem.id,
                success=False,
                generated_code="",
                syntax_correct=False,
                semantic_match=False,
                execution_time=time.time() - start_time,
                error_message=str(e)
            )

    def _check_semantic_match(self, generated: str, expected: str) -> bool:
        """
        检查生成的代码与期望代码是否语义等价

        注意：这是简化实现，实际应该使用更复杂的语义比较
        """
        # 提取定理名和陈述
        # 这里使用简单的字符串匹配作为示例
        gen_parts = generated.split(":=")[0].strip()
        exp_parts = expected.split(":=")[0].strip()

        return gen_parts == exp_parts

# 使用示例
if __name__ == "__main__":
    from imo_dataset_loader import IMODatasetLoader
    from lean_verifier import LeanVerifier

    # 初始化组件
    loader = IMODatasetLoader("/path/to/imo_lean")
    verifier = LeanVerifier()
    benchmark = FormalizationBenchmark(loader, verifier)

    # 定义测试模型（示例：简单的字符串复制）
    def dummy_model(description: str) -> str:
        # 实际应该接入真实的AI模型
        return f"-- 自动形式化: {description[:30]}\ntheorem placeholder : True := by trivial"

    # 运行评估
    results = benchmark.evaluate_model(dummy_model, sample_size=5)

    print("\n" + "=" * 60)
    print("评估结果:")
    print(f"  总题目: {results['total']}")
    print(f"  成功率: {results['success_rate']:.1%}")
    print(f"  语法正确率: {results['syntax_correct_rate']:.1%}")
    print(f"  平均耗时: {results['average_time']:.2f}秒")
```

---

## 5. 完整集成示例

### 自动形式化流水线

```python
# examples/autoformalization_pipeline.py

import asyncio
from typing import Optional
from dataclasses import dataclass

@dataclass
class PipelineResult:
    """流水线处理结果"""
    input_description: str
    generated_code: str
    verified: bool
    error_messages: list
    processing_time: float
    model_used: str

class AutoformalizationPipeline:
    """自动形式化流水线"""

    def __init__(self):
        # 初始化各组件
        self.nl_processor = DeepSeekMathClient()
        self.formalizer = KELPSClient()  # 或其他形式化模型
        self.verifier = LeanVerifier()
        self.knowledge_base = TheoremKnowledgeBase()

    async def process(
        self,
        description: str,
        verify: bool = True,
        max_attempts: int = 3
    ) -> PipelineResult:
        """
        处理自然语言描述，生成并验证形式化代码

        Args:
            description: 自然语言数学描述
            verify: 是否验证生成的代码
            max_attempts: 最大尝试次数

        Returns:
            处理结果
        """
        import time
        start_time = time.time()

        error_messages = []

        for attempt in range(max_attempts):
            try:
                # 步骤1: 语义理解
                understanding = await self.nl_processor.analyze(description)

                # 步骤2: 形式化生成
                context = {
                    "understanding": understanding,
                    "similar_theorems": await self.knowledge_base.find_similar(description)
                }

                generated_code = await self.formalizer.generate(
                    description=description,
                    context=context
                )

                # 步骤3: 验证（如果启用）
                verified = False
                if verify:
                    verification = self.verifier.verify(generated_code)
                    verified = verification["valid"]

                    if not verified:
                        error_messages.append(
                            f"尝试 {attempt + 1}: 验证失败 - {verification['errors']}"
                        )
                        # 可以在这里添加自动修正逻辑
                        continue

                # 成功
                return PipelineResult(
                    input_description=description,
                    generated_code=generated_code,
                    verified=verified,
                    error_messages=error_messages,
                    processing_time=time.time() - start_time,
                    model_used="kelps-v1"
                )

            except Exception as e:
                error_messages.append(f"尝试 {attempt + 1}: {str(e)}")
                if attempt == max_attempts - 1:
                    # 最后一次尝试失败
                    return PipelineResult(
                        input_description=description,
                        generated_code="",
                        verified=False,
                        error_messages=error_messages,
                        processing_time=time.time() - start_time,
                        model_used="kelps-v1"
                    )

        # 所有尝试都失败
        return PipelineResult(
            input_description=description,
            generated_code="",
            verified=False,
            error_messages=error_messages + ["所有尝试均失败"],
            processing_time=time.time() - start_time,
            model_used="kelps-v1"
        )

    async def batch_process(
        self,
        descriptions: list[str],
        **kwargs
    ) -> list[PipelineResult]:
        """批量处理"""
        tasks = [self.process(desc, **kwargs) for desc in descriptions]
        return await asyncio.gather(*tasks)

# 使用示例
async def main():
    pipeline = AutoformalizationPipeline()

    descriptions = [
        "证明：对于任意正整数n，n² + n是偶数。",
        "证明三角不等式：对于任意实数x, y，有|x + y| ≤ |x| + |y|"。",
        "定义群同态并证明它保持单位元。"
    ]

    results = await pipeline.batch_process(descriptions)

    for desc, result in zip(descriptions, results):
        print(f"\n{'='*60}")
        print(f"输入: {desc}")
        print(f"结果: {'✓ 成功' if result.verified else '✗ 失败'}")
        print(f"耗时: {result.processing_time:.2f}秒")
        if result.generated_code:
            print(f"\n生成的代码:\n{result.generated_code}")
        if result.error_messages:
            print(f"\n错误: {result.error_messages}")

if __name__ == "__main__":
    asyncio.run(main())
```

---

## 6. 工具和资源链接

### 官方资源

#### Lean生态

| 资源 | 链接 | 说明 |
|------|------|------|
| Lean 4官网 | https://lean-lang.org/ | 官方文档和下载 |
| Mathlib 4 | https://github.com/leanprover-community/mathlib4 | 数学库 |
| Lean Zulip | https://leanprover.zulipchat.com/ | 社区讨论 |
| Lean 4 API文档 | https://lean-lang.org/api/lean4/ | API参考 |

#### AI形式化项目

| 项目 | 链接 | 说明 |
|------|------|------|
| DeepSeek | https://github.com/deepseek-ai | DeepSeek系列模型 |
| LeanDojo | https://leandojo.org/ | Lean交互环境 |
| ReProver | https://github.com/lean-dojo/ReProver | 检索增强证明器 |
| IMO Lean | https://github.com/jsm28/IMOLean | IMO题目形式化 |

### 模型下载

```bash
# HuggingFace模型下载示例

# DeepSeek-Math
huggingface-cli download deepseek-ai/deepseek-math-7b-rl

# 使用Python下载
from huggingface_hub import snapshot_download

# 下载DeepSeek-Math
snapshot_download(
    repo_id="deepseek-ai/deepseek-math-7b-rl",
    local_dir="./models/deepseek-math-7b",
    local_dir_use_symlinks=False
)
```

### 数据集下载

```bash
# IMO Lean数据集
# 方法1：直接克隆
git clone https://github.com/jsm28/IMOLean.git

# 方法2：作为子模块
git submodule add https://github.com/jsm28/IMOLean.git data/imo_lean
```

### Docker环境

```dockerfile
# Dockerfile for FormalMath AI Environment

FROM python:3.10-slim

# 安装系统依赖
RUN apt-get update && apt-get install -y \
    git \
    curl \
    && rm -rf /var/lib/apt/lists/*

# 安装elan (Lean工具链管理器)
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
ENV PATH="/root/.elan/bin:${PATH}"

# 设置工作目录
WORKDIR /app

# 安装Python依赖
COPY requirements.txt .
RUN pip install --no-cache-dir -r requirements.txt

# 安装Lean 4
RUN elan toolchain install stable
RUN elan default stable

# 复制项目代码
COPY . .

# 暴露端口
EXPOSE 8000

# 启动命令
CMD ["uvicorn", "main:app", "--host", "0.0.0.0", "--port", "8000"]
```

```yaml
# docker-compose.yml

version: '3.8'

services:
  formalmath-ai:
    build: .
    ports:
      - "8000:8000"
    volumes:
      - ./models:/app/models
      - ./data:/app/data
    environment:
      - DEEPSEEK_API_KEY=${DEEPSEEK_API_KEY}
      - CUDA_VISIBLE_DEVICES=0
    deploy:
      resources:
        reservations:
          devices:
            - driver: nvidia
              count: 1
              capabilities: [gpu]

  lean-server:
    image: leanprover/lean4:latest
    volumes:
      - ./lean_projects:/workspace
    command: sleep infinity
```

---

## 7. 常见问题排查

### Lean相关问题

```bash
# 问题1: lean命令找不到
# 解决: 检查elan安装
elan --version
which lean

# 问题2: 导入Mathlib失败
# 解决: 初始化lake项目并添加依赖
lake init myproject
# 编辑lakefile.lean添加依赖
lake update
lake build

# 问题3: 内存不足
# 解决: 增加交换空间或使用更小的项目测试
```

### Python相关问题

```bash
# 问题1: CUDA out of memory
# 解决: 使用更小的模型或CPU推理
export CUDA_VISIBLE_DEVICES=""
# 或在代码中设置 device_map="cpu"

# 问题2: transformers版本不兼容
# 解决: 安装特定版本
pip install transformers==4.36.0

# 问题3: 模型下载慢
# 解决: 使用镜像或设置HF_ENDPOINT
export HF_ENDPOINT=https://hf-mirror.com
```

---

## 8. 进一步学习资源

### 教程

- [Theorem Proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/) - 官方教程
- [Functional Programming in Lean](https://leanprover.github.io/functional_programming_in_lean/) - 函数式编程
- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/) - 数学证明

### 论文

- [DeepSeek-Math](https://arxiv.org/abs/2402.03300)
- [LeanDojo](https://arxiv.org/abs/2306.15626)
- [DSP: Draft, Sketch, and Prove](https://arxiv.org/abs/2210.00683)

---

## 总结

本文档提供了从环境配置到完整集成的代码示例，帮助开发者快速上手AI形式化数学技术。建议按照以下路径学习：

1. **环境准备**：安装Lean 4和Python环境
2. **基础练习**：运行DeepSeek-Math示例
3. **Lean集成**：掌握Lean代码验证和生成
4. **数据集处理**：熟悉IMO Lean数据集
5. **完整集成**：构建端到端流水线

---

*文档版本：1.0*
*最后更新：2026年4月*
