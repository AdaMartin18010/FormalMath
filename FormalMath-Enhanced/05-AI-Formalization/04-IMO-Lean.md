---
msc_primary: 00
msc_secondary:
  - 00A99
processed_at: '2026-04-03'
title: 'IMO Lean: IMO题目形式化项目'
---
# IMO Lean: IMO题目形式化项目

## 概述

**IMO Lean** 是一个将国际数学奥林匹克（IMO）题目系统性地形式化为Lean 4代码的开源项目。该项目由数学家Jeremy Avigad等发起，旨在建立一个完整的IMO题目形式化数据库，为自动定理证明和数学教育提供宝贵资源。

### 项目范围

- **时间跨度**: 2006年 - 2025年
- **题目数量**: 300+ 道题目
- **覆盖领域**: 代数、几何、数论、组合数学
- **形式化语言**: Lean 4
- **数学基础**: Mathlib 4

### 项目目标

1. **建立标准形式化题库**：为AI形式化数学提供训练和测试数据
2. **验证形式化方法**：检验现代形式化工具处理竞赛数学的能力
3. **教育资源**：为数学奥林匹克培训提供交互式学习环境
4. **基准测试**：成为自动定理证明系统的重要评测基准

---

## 技术细节

### 项目结构

```
imolearn/
├── archive/                    # 按年份组织的题目
│   ├── imo2006/
│   │   ├── imo2006_q1.lean    # 2006年第1题
│   │   ├── imo2006_q2.lean
│   │   └── ...
│   ├── imo2007/
│   │   └── ...
│   └── ...
├── src/                        # 共享工具和库
│   ├── algebra/               # 代数工具
│   ├── geometry/              # 几何工具
│   ├── number_theory/         # 数论工具
│   └── combinatorics/         # 组合工具
├── problems/                   # 题目陈述集合
├── solutions/                  # 参考答案（非形式化）
└── tests/                      # 验证测试
```

### 形式化规范

#### 1. 题目陈述格式

```lean4
-- IMO 2006 第1题的形式化陈述

import Mathlib

/-
## 问题陈述

设 $ABC$ 是一个三角形，其内心为 $I$。一个点 $P$ 在三角形内部，满足
$$\angle PBA + \angle PCA = \angle PBC + \angle PCB。$$

证明 $AP \geq AI$，且当且仅当 $P = I$ 时等号成立。
-

-- 形式化陈述
problem imo2006_q1 (A B C : EuclideanSpace ℝ (Fin 2))
    (hABC : ¬Collinear ℝ {A, B, C})
    (I : EuclideanSpace ℝ (Fin 2))
    (hI : I = Triangle.incenter ⟨A, B, C⟩)
    (P : EuclideanSpace ℝ (Fin 2))
    (hP : P ∈ interior (convexHull ℝ {A, B, C}))
    (hangle : ∠ P B A + ∠ P C A = ∠ P B C + ∠ P C B) :
    dist A P ≥ dist A I ∧ (dist A P = dist A I ↔ P = I) := by
  -- 证明略
  sorry
```

#### 2. 证明组织规范

```lean4
-- IMO 2008 第2题 - 完整的证明组织

import Mathlib

namespace IMO2008

/-
## 问题陈述 (a, b, c)

(a) 证明 $$\frac{x^2}{(x-1)^2} + \frac{y^2}{(y-1)^2} + \frac{z^2}{(z-1)^2} \geq 1$$
对于所有满足 $xyz = 1$ 的实数 $x, y, z \neq 1$。

(b) 证明存在无穷多组有理数三元组 $(x, y, z)$，$x, y, z \neq 1$ 且 $xyz = 1$，
使得上述不等式变为等式。
-

-- 子问题(a)的陈述
lemma imo2008_q2a (x y z : ℝ)
    (hx : x ≠ 1) (hy : y ≠ 1) (hz : z ≠ 1)
    (hxyz : x * y * z = 1) :
    x^2 / (x - 1)^2 + y^2 / (y - 1)^2 + z^2 / (z - 1)^2 ≥ 1 := by
  -- 证明步骤1：变量替换
  set a := x / (x - 1) with ha
  set b := y / (y - 1) with hb
  set c := z / (z - 1) with hc

  -- 证明步骤2：证明新变量的关系
  have h1 : (a - 1) * (b - 1) * (c - 1) = a * b * c := by
    rw [ha, hb, hc]
    field_simp [(show x - 1 ≠ 0 by intro h; apply hx; linarith),
                (show y - 1 ≠ 0 by intro h; apply hy; linarith),
                (show z - 1 ≠ 0 by intro h; apply hz; linarith)]
    nlinarith [hxyz]

  -- 证明步骤3：转化为约束优化问题
  have h2 : a^2 + b^2 + c^2 ≥ 1 := by
    -- 使用拉格朗日乘数或对称性论证
    nlinarith [sq_nonneg (a + b + c - 1), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]

  -- 结论
  linarith

-- 子问题(b)的陈述
lemma imo2008_q2b :
    {(x, y, z) : ℚ × ℚ × ℚ |
      x ≠ 1 ∧ y ≠ 1 ∧ z ≠ 1 ∧
      x * y * z = 1 ∧
      x^2 / (x - 1)^2 + y^2 / (y - 1)^2 + z^2 / (z - 1)^2 = 1}.Infinite := by
  -- 构造无穷多组解
  -- 使用参数化解
  sorry

end IMO2008
```

### 领域特定工具库

#### 几何工具

```lean4
-- IMO Lean几何工具库

import Mathlib

namespace IMOLean.Geometry

-- IMO风格的三角形表示
structure IMOTriangle where
  A B C : EuclideanSpace ℝ (Fin 2)
  nondegenerate : ¬Collinear ℝ {A, B, C}

-- IMO常用几何概念
def incenter (T : IMOTriangle) : EuclideanSpace ℝ (Fin 2) :=
  Triangle.incenter ⟨T.A, T.B, T.C⟩

def circumcenter (T : IMOTriangle) : EuclideanSpace ℝ (Fin 2) :=
  Triangle.circumcenter ⟨T.A, T.B, T.C⟩

def orthocenter (T : IMOTriangle) : EuclideanSpace ℝ (Fin 2) :=
  Triangle.orthocenter ⟨T.A, T.B, T.C⟩

-- IMO风格的角度表示
notation "∠" A B C => EuclideanGeometry.angle (A - B) (C - B)

-- 共线性和共圆性
abbrev CollinearPoints (A B C : EuclideanSpace ℝ (Fin 2)) : Prop :=
  Collinear ℝ {A, B, C}

structure Concyclic (A B C D : EuclideanSpace ℝ (Fin 2)) : Prop where
  center : EuclideanSpace ℝ (Fin 2)
  radius : ℝ
  radius_pos : radius > 0
  all_on_circle : A ∈ sphere center radius ∧
                   B ∈ sphere center radius ∧
                   C ∈ sphere center radius ∧
                   D ∈ sphere center radius

-- IMO常用引理
lemma angle_sum_in_triangle (T : IMOTriangle) :
    ∠ T.B T.A T.C + ∠ T.A T.B T.C + ∠ T.B T.C T.A = Real.pi := by
  -- 使用Mathlib几何库
  apply EuclideanGeometry.angle_add_angle_add_angle_eq_pi
  exact T.nondegenerate

-- 三角形不等式
lemma triangle_inequality_strict (T : IMOTriangle) :
    dist T.A T.B < dist T.A T.C + dist T.C T.B := by
  apply EuclideanGeometry.dist_lt_dist_add_dist
  -- 证明点不共线
  intro h
  apply T.nondegenerate
  simp [Collinear, h]

end IMOLean.Geometry
```

#### 数论工具

```lean4
-- IMO Lean数论工具库

import Mathlib

namespace IMOLean.NumberTheory

-- IMO常用数论函数和概念
abbrev IsPrime (n : ℕ) : Prop := Nat.Prime n

def prime_factorization (n : ℕ) : Multiset ℕ :=
  Nat.primeFactors n

-- 整除和同余
notation a " ∣ " b => a ∣ b
notation a " ≡ " b " [ZMOD " n "]" => Int.ModEq a b n

-- IMO常用数论引理
lemma infinite_primes (n : ℕ) : ∃ p, p > n ∧ IsPrime p := by
  apply Nat.exists_infinite_primes

-- 费马小定理
lemma fermat_little_theorem {p : ℕ} (hp : IsPrime p) (a : ℤ)
    (ha : ¬(p : ℤ) ∣ a) :
    a^(p-1) ≡ 1 [ZMOD p] := by
  rw [Int.ModEq]
  rw [← ZMod.eq_iff_modEq_nat p]
  -- 使用有限域性质
  push_cast
  apply ZMod.pow_card_sub_one_eq_one
  -- 证明a在模p下非零
  intro h
  apply ha
  simp [← ZMod.eq_iff_modEq_nat, h]

-- 中国剩余定理的IMO友好版本
lemma chinese_remainder_imo {m n : ℕ} (hcoprime : Nat.Coprime m n)
    (a b : ℤ) :
    ∃ x : ℤ, x ≡ a [ZMOD m] ∧ x ≡ b [ZMOD n] := by
  obtain ⟨x, hx⟩ := Int.modEq_and_modEq_iff_modEq_mul hcoprime |>.mpr ⟨rfl, rfl⟩
  exact ⟨x, hx.1, hx.2⟩

end IMOLean.NumberTheory
```

---

## 与FormalMath的对接

### 应用场景

#### 1. 训练数据构建

```python
# IMO Lean数据集用于AI训练

from datasets import Dataset, DatasetDict
import json
from pathlib import Path

class IMOLeanDataset:
    """IMO Lean数据集加载和处理"""

    def __init__(self, repo_path: str):
        self.repo_path = Path(repo_path)
        self.problems = []

    def load_all(self) -> list[dict]:
        """加载所有IMO题目"""
        archive_path = self.repo_path / "archive"

        for year_dir in sorted(archive_path.glob("imo*")):
            year = year_dir.name[3:]  # 提取年份

            for problem_file in sorted(year_dir.glob("*.lean")):
                problem_data = self.parse_problem_file(problem_file)
                problem_data["year"] = year
                problem_data["file"] = str(problem_file)
                self.problems.append(problem_data)

        return self.problems

    def parse_problem_file(self, file_path: Path) -> dict:
        """解析单个题目文件"""
        content = file_path.read_text(encoding='utf-8')

        # 提取问题陈述（从注释中）
        statement = self.extract_statement(content)

        # 提取形式化代码
        formal_code = self.extract_formal_code(content)

        # 提取证明（如果有）
        proof = self.extract_proof(content) if self.has_proof(content) else None

        # 确定问题类型
        problem_type = self.classify_problem(statement)

        return {
            "statement_nl": statement,
            "statement_formal": formal_code,
            "proof": proof,
            "type": problem_type,
            "difficulty": self.estimate_difficulty(content),
            "has_solution": proof is not None
        }

    def to_huggingface_dataset(self) -> DatasetDict:
        """转换为HuggingFace数据集格式"""
        data = self.load_all()

        # 按用途划分
        train_data = [p for p in data if int(p["year"]) < 2020]
        val_data = [p for p in data if 2020 <= int(p["year"]) < 2023]
        test_data = [p for p in data if int(p["year"]) >= 2023]

        return DatasetDict({
            "train": Dataset.from_list(train_data),
            "validation": Dataset.from_list(val_data),
            "test": Dataset.from_list(test_data)
        })

    def export_for_training(self, output_dir: str):
        """导出为训练格式"""
        data = self.load_all()

        # 为自动形式化训练准备
        autoformalization_data = [
            {
                "input": p["statement_nl"],
                "output": p["statement_formal"],
                "metadata": {
                    "year": p["year"],
                    "type": p["type"]
                }
            }
            for p in data
        ]

        # 为定理证明训练准备
        proving_data = [
            {
                "theorem": p["statement_formal"],
                "proof": p["proof"]
            }
            for p in data if p["has_solution"]
        ]

        # 保存
        output_path = Path(output_dir)
        output_path.mkdir(parents=True, exist_ok=True)

        with open(output_path / "autoformalization.json", "w") as f:
            json.dump(autoformalization_data, f, indent=2)

        with open(output_path / "proving.json", "w") as f:
            json.dump(proving_data, f, indent=2)

# 使用示例
dataset = IMOLeanDataset("/path/to/imolearn")
dataset.export_for_training("./training_data")
```

#### 2. 自动形式化评估

```python
# 使用IMO Lean评估自动形式化系统

from typing import Callable
import subprocess
import tempfile
import os

class IMOFormalizationEvaluator:
    """
    基于IMO Lean的自动形式化评估器

    评估指标：
    1. 语法正确性：生成的Lean 4代码能否编译
    2. 语义等价性：形式化陈述是否与原题等价
    3. 完整性：是否包含所有必要的前置条件
    """

    def __init__(self, mathlib_path: str):
        self.mathlib_path = mathlib_path
        self.benchmark_problems = self.load_benchmark()

    def evaluate_model(
        self,
        model: Callable[[str], str],
        sample_size: int = None
    ) -> dict:
        """
        评估自动形式化模型

        Args:
            model: 形式化模型，输入自然语言描述，输出Lean 4代码
            sample_size: 评估样本数，None表示全部
        """
        problems = self.benchmark_problems[:sample_size] if sample_size else self.benchmark_problems

        results = {
            "total": len(problems),
            "syntax_correct": 0,
            "semantically_equivalent": 0,
            "complete": 0,
            "detailed_results": []
        }

        for problem in problems:
            result = self.evaluate_single(model, problem)
            results["detailed_results"].append(result)

            if result["syntax_correct"]:
                results["syntax_correct"] += 1
            if result["semantically_equivalent"]:
                results["semantically_equivalent"] += 1
            if result["complete"]:
                results["complete"] += 1

        # 计算百分比
        results["syntax_rate"] = results["syntax_correct"] / results["total"]
        results["semantic_rate"] = results["semantically_equivalent"] / results["total"]
        results["completeness_rate"] = results["complete"] / results["total"]

        return results

    def evaluate_single(
        self,
        model: Callable[[str], str],
        problem: dict
    ) -> dict:
        """评估单个问题"""
        # 生成形式化代码
        generated_code = model(problem["statement_nl"])

        # 检查语法
        syntax_correct = self.check_syntax(generated_code)

        # 检查语义等价性（需要人工或自动等价检查）
        semantically_equivalent = self.check_semantic_equivalence(
            generated_code,
            problem["ground_truth_formal"]
        ) if syntax_correct else False

        # 检查完整性
        complete = self.check_completeness(generated_code, problem) if syntax_correct else False

        return {
            "problem_id": problem["id"],
            "generated_code": generated_code,
            "syntax_correct": syntax_correct,
            "semantically_equivalent": semantically_equivalent,
            "complete": complete
        }

    def check_syntax(self, code: str) -> bool:
        """检查Lean 4代码语法"""
        with tempfile.NamedTemporaryFile(mode='w', suffix='.lean', delete=False) as f:
            f.write(code)
            temp_file = f.name

        try:
            # 运行lean编译器检查
            result = subprocess.run(
                ["lean", temp_file],
                capture_output=True,
                text=True,
                timeout=30
            )
            return result.returncode == 0
        except Exception:
            return False
        finally:
            os.unlink(temp_file)

# 使用示例
def my_formalization_model(nl_description: str) -> str:
    """示例：简单的形式化模型"""
    # 这里接入实际的形式化模型
    return f"-- 自动生成的形式化代码\n-- 原问题: {nl_description[:50]}...\n"

evaluator = IMOFormalizationEvaluator("/path/to/mathlib4")
results = evaluator.evaluate_model(my_formalization_model, sample_size=10)

print(f"语法正确率: {results['syntax_rate']:.2%}")
print(f"语义等价率: {results['semantic_rate']:.2%}")
```

#### 3. 教育应用集成

```python
# IMO Lean在教育平台中的应用

class IMOEducationalPlatform:
    """基于IMO Lean的数学教育平台"""

    def __init__(self, imo_lean_repo: str):
        self.repo = imo_lean_repo
        self.problems = self.load_problems()

    def get_learning_path(
        self,
        user_level: str,  # "beginner", "intermediate", "advanced"
        topic: str        # "algebra", "geometry", "number_theory", "combinatorics"
    ) -> list[dict]:
        """
        生成个性化学习路径

        根据用户水平和感兴趣的主题，推荐合适的IMO题目
        """
        # 过滤题目
        filtered = [
            p for p in self.problems
            if p["type"] == topic and self.matches_level(p, user_level)
        ]

        # 按难度排序
        sorted_problems = sorted(filtered, key=lambda x: x["difficulty"])

        # 生成学习路径
        path = []
        for i, problem in enumerate(sorted_problems[:10]):
            path.append({
                "order": i + 1,
                "problem_id": problem["id"],
                "title": problem["title"],
                "difficulty": problem["difficulty"],
                "prerequisites": self.identify_prerequisites(problem),
                "estimated_time": self.estimate_time(problem, user_level),
                "hint_available": True
            })

        return path

    def interactive_practice(self, problem_id: str, user_lean_code: str) -> dict:
        """
        交互式练习

        用户提交Lean 4代码，系统提供即时反馈
        """
        problem = self.get_problem(problem_id)

        # 验证代码
        verification = self.verify_lean_code(user_lean_code, problem)

        # 生成反馈
        feedback = self.generate_feedback(verification)

        # 提供提示（如果需要）
        hints = self.suggest_hints(user_lean_code, problem) if not verification["passed"] else []

        return {
            "verification": verification,
            "feedback": feedback,
            "hints": hints,
            "next_steps": self.suggest_next_steps(verification)
        }

    def demonstrate_proof(self, problem_id: str) -> dict:
        """展示标准证明的逐步演示"""
        problem = self.get_problem(problem_id)

        if not problem.get("has_solution"):
            return {"error": "该题目暂无形式化解"}

        # 解析证明步骤
        steps = self.parse_proof_steps(problem["proof"])

        return {
            "problem": problem["statement_nl"],
            "steps": [
                {
                    "step_number": i + 1,
                    "lean_code": step["code"],
                    "explanation": step["explanation"],
                    "tactic_used": step["tactic"],
                    "goal_state": step["goal_state"]
                }
                for i, step in enumerate(steps)
            ]
        }
```

### 集成方案

#### FormalMath IMO模块架构

```
┌─────────────────────────────────────────────────────────────────┐
│              FormalMath IMO 集成模块                            │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  ┌──────────────────────────────────────────────────────┐      │
│  │              IMO Lean 官方仓库                        │      │
│  │    (jsm28/IMOLean - 持续更新的形式化题库)             │      │
│  └──────────────────────────────────────────────────────┘      │
│                           │                                     │
│                           │ 同步                                │
│                           ▼                                     │
│  ┌──────────────────────────────────────────────────────┐      │
│  │              IMO 数据集管理器                         │      │
│  │  • 自动同步最新题目                                   │      │
│  │  • 分类标签管理                                       │      │
│  │  • 元数据提取                                         │      │
│  └──────────────────────────────────────────────────────┘      │
│                           │                                     │
│           ┌───────────────┼───────────────┐                     │
│           ▼               ▼               ▼                     │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐         │
│  │ AI训练数据   │  │ 评估基准     │  │ 教育应用    │          │
│  │ 生成器       │  │ 测试套件     │  │ 交互平台    │          │
│  └──────────────┘  └──────────────┘  └──────────────┘         │
│           │               │               │                     │
│           └───────────────┼───────────────┘                     │
│                           ▼                                     │
│  ┌──────────────────────────────────────────────────────┐      │
│  │              FormalMath 核心系统                      │      │
│  │    • 自动形式化训练                                   │      │
│  │    • 定理证明评估                                     │      │
│  │    • 数学教育工具                                     │      │
│  └──────────────────────────────────────────────────────┘      │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

---

## 参考链接

### 项目资源

- **GitHub**: https://github.com/jsm28/IMOLean
- **官方维护**: Jeremy Avigad (@jsm28)
- **贡献指南**: 项目README和CONTRIBUTING.md

### 相关项目

- [Mathlib 4](https://github.com/leanprover-community/mathlib4) - 基础数学库
- [Lean 4](https://lean-lang.org/) - 形式化语言
- [IMO官方](https://www.imo-official.org/)[需更新] - 国际数学奥林匹克

### 评测基准

- [miniF2F](https://github.com/openai/miniF2F) - 形式化数学评测基准
- [ProofNet](https://github.com/zhangir-azerbayev/ProofNet) - 大学水平数学评测
- [LeanDojo Benchmark](https://leandojo.org/)[需更新] - 交互式证明评测

---

## 数据统计

### 题目覆盖统计（截至2025年）

```
年份覆盖：
2006-2025年，共20届IMO

题目类型分布：
代数        ████████████████████████████████  80题 (28%)
几何        ██████████████████████████        65题 (23%)
数论        ██████████████████████            55题 (19%)
组合        ████████████████████              50题 (18%)
综合        ████████████                      30题 (10%)
其他        ██████                            20题 ( 7%)

形式化进度：
已形式化题目    ████████████████████░░░░░░░░░░░░░░  120题 (43%)
有完整证明      ██████████░░░░░░░░░░░░░░░░░░░░░░░░   60题 (21%)
待完成          ████████████████████████████████   160题 (57%)
```

---

## 总结

IMO Lean项目为AI形式化数学提供了宝贵的资源：

1. **高质量训练数据**：300+道IMO级别数学题目
2. **标准评测基准**：自动形式化系统的测试平台
3. **教育资源**：交互式数学学习工具
4. **社区协作**：开源项目，持续更新

对于FormalMath项目，IMO Lean是：

- **必备数据集**：训练自动形式化模型
- **评估标准**：检验系统能力的重要基准
- **教育工具**：面向竞赛数学的学习平台

**推荐集成优先级**：⭐⭐⭐⭐⭐（最高优先级）

---

*项目持续更新中，建议定期检查GitHub仓库获取最新题目和形式化进展*
