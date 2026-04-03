"""
自动化形式化工作流
整合所有工具，实现端到端自动形式化流程
"""

import os
import sys
import json
import time
import logging
from typing import List, Dict, Any, Optional, Callable
from dataclasses import dataclass, field, asdict
from pathlib import Path
from datetime import datetime

# 导入其他工具
from deepseek_client import DeepSeekClient, DeepSeekConfig, FormalizationMode, FormalizationResult
from lean_verifier import LeanVerifier, LeanProjectConfig, VerificationResult, VerificationStatus
from imo_dataset import IMODatasetProcessor, DatasetConfig, IMOProblem
from msc_recommender import MSCRecommender, MSCRecommendation

logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s'
)
logger = logging.getLogger(__name__)


@dataclass
class WorkflowConfig:
    """工作流配置"""
    deepseek_config: Optional[DeepSeekConfig] = None
    lean_config: Optional[LeanProjectConfig] = None
    dataset_config: Optional[DatasetConfig] = None
    output_dir: str = "./output"
    max_retries: int = 3
    verify_after_formalization: bool = True
    auto_fix_errors: bool = True
    generate_report: bool = True


@dataclass
class FormalizationTask:
    """形式化任务"""
    task_id: str
    problem_text: str
    source: str = ""
    metadata: Dict[str, Any] = field(default_factory=dict)
    
    # 结果
    generated_lean_code: str = ""
    verification_result: Optional[VerificationResult] = None
    msc_recommendations: List[MSCRecommendation] = field(default_factory=list)
    retry_count: int = 0
    status: str = "pending"  # pending, processing, success, failed
    error_message: str = ""
    
    # 时间戳
    created_at: str = field(default_factory=lambda: datetime.now().isoformat())
    started_at: str = ""
    completed_at: str = ""
    
    def to_dict(self) -> Dict[str, Any]:
        """转换为字典"""
        data = asdict(self)
        if self.verification_result:
            data['verification_result'] = {
                'status': self.verification_result.status.value,
                'is_valid': self.verification_result.is_valid,
                'error_count': len(self.verification_result.errors),
                'warning_count': len(self.verification_result.warnings),
                'elapsed_time_ms': self.verification_result.elapsed_time_ms
            }
        return data


@dataclass
class WorkflowResult:
    """工作流结果"""
    workflow_id: str
    tasks: List[FormalizationTask]
    total_tasks: int
    successful_tasks: int
    failed_tasks: int
    total_time_ms: float
    created_at: str
    completed_at: str
    report_path: str = ""


class AutoFormalizationWorkflow:
    """
    自动化形式化工作流
    
    功能：
    - 端到端自动形式化流程
    - 整合DeepSeek、Lean验证、IMO数据集、MSC推荐
    - 生成报告
    """
    
    def __init__(self, config: Optional[WorkflowConfig] = None):
        """
        初始化工作流
        
        Args:
            config: 工作流配置
        """
        if config is None:
            config = WorkflowConfig()
        
        self.config = config
        
        # 初始化各组件
        self.deepseek = DeepSeekClient(config.deepseek_config)
        self.lean_verifier = LeanVerifier(config.lean_config)
        self.msc_recommender = MSCRecommender()
        
        # 创建输出目录
        Path(self.config.output_dir).mkdir(parents=True, exist_ok=True)
        
        # 回调函数
        self.on_task_start: Optional[Callable[[FormalizationTask], None]] = None
        self.on_task_complete: Optional[Callable[[FormalizationTask], None]] = None
        self.on_error: Optional[Callable[[FormalizationTask, str], None]] = None
    
    def process_problem(self, problem_text: str, 
                       source: str = "",
                       metadata: Optional[Dict[str, Any]] = None) -> FormalizationTask:
        """
        处理单个数学问题
        
        Args:
            problem_text: 数学问题文本
            source: 问题来源
            metadata: 元数据
            
        Returns:
            任务结果
        """
        task_id = f"task_{int(time.time() * 1000)}"
        task = FormalizationTask(
            task_id=task_id,
            problem_text=problem_text,
            source=source,
            metadata=metadata or {}
        )
        
        return self._execute_task(task)
    
    def _execute_task(self, task: FormalizationTask) -> FormalizationTask:
        """执行任务"""
        task.status = "processing"
        task.started_at = datetime.now().isoformat()
        
        if self.on_task_start:
            self.on_task_start(task)
        
        try:
            logger.info(f"Processing task {task.task_id}")
            
            # 步骤1: MSC编码推荐
            logger.info("  Step 1: MSC recommendation")
            task.msc_recommendations = self.msc_recommender.recommend(
                task.problem_text, top_k=3
            )
            
            # 步骤2: 形式化转换
            logger.info("  Step 2: Formalization")
            formalization_result = self.deepseek.formalize(
                task.problem_text,
                mode=FormalizationMode.NATURAL_TO_LEAN
            )
            
            if not formalization_result.success:
                raise RuntimeError(f"Formalization failed: {formalization_result.error_message}")
            
            task.generated_lean_code = formalization_result.content
            
            # 步骤3: 验证（如果启用）
            if self.config.verify_after_formalization:
                logger.info("  Step 3: Verification")
                task = self._verify_and_fix(task)
            
            task.status = "success"
            
        except Exception as e:
            task.status = "failed"
            task.error_message = str(e)
            logger.error(f"Task {task.task_id} failed: {e}")
            
            if self.on_error:
                self.on_error(task, str(e))
        
        finally:
            task.completed_at = datetime.now().isoformat()
            
            if self.on_task_complete:
                self.on_task_complete(task)
        
        return task
    
    def _verify_and_fix(self, task: FormalizationTask) -> FormalizationTask:
        """验证并尝试修复错误"""
        for attempt in range(self.config.max_retries):
            # 验证代码
            verification = self.lean_verifier.verify(task.generated_lean_code)
            task.verification_result = verification
            
            if verification.is_valid:
                logger.info(f"  ✓ Verification passed")
                break
            
            logger.warning(f"  ✗ Verification failed (attempt {attempt + 1})")
            
            # 尝试自动修复
            if self.config.auto_fix_errors and attempt < self.config.max_retries - 1:
                logger.info("  Step 3.5: Auto-fixing errors")
                fixed_code = self.lean_verifier.fix_common_errors(
                    task.generated_lean_code,
                    verification.errors
                )
                
                # 如果修复成功，更新代码
                if fixed_code != task.generated_lean_code:
                    task.generated_lean_code = fixed_code
                    task.retry_count += 1
                else:
                    # 尝试使用DeepSeek修复
                    error_msg = "\n".join([e.message for e in verification.errors])
                    fix_result = self.deepseek.formalize(
                        task.generated_lean_code,
                        mode=FormalizationMode.ERROR_CORRECTION,
                        error=error_msg
                    )
                    
                    if fix_result.success:
                        task.generated_lean_code = fix_result.content
                        task.retry_count += 1
            else:
                break
        
        return task
    
    def batch_process(self, problems: List[Dict[str, Any]]) -> WorkflowResult:
        """
        批量处理问题
        
        Args:
            problems: 问题列表，每项包含problem_text, source, metadata
            
        Returns:
            工作流结果
        """
        workflow_id = f"wf_{int(time.time() * 1000)}"
        start_time = time.time()
        
        tasks = []
        successful = 0
        failed = 0
        
        logger.info(f"Starting workflow {workflow_id} with {len(problems)} tasks")
        
        for i, prob in enumerate(problems):
            logger.info(f"Processing {i+1}/{len(problems)}")
            
            task = self.process_problem(
                problem_text=prob.get("problem_text", ""),
                source=prob.get("source", ""),
                metadata=prob.get("metadata", {})
            )
            
            tasks.append(task)
            
            if task.status == "success":
                successful += 1
            else:
                failed += 1
        
        elapsed = (time.time() - start_time) * 1000
        
        result = WorkflowResult(
            workflow_id=workflow_id,
            tasks=tasks,
            total_tasks=len(tasks),
            successful_tasks=successful,
            failed_tasks=failed,
            total_time_ms=elapsed,
            created_at=datetime.now().isoformat(),
            completed_at=datetime.now().isoformat()
        )
        
        # 生成报告
        if self.config.generate_report:
            result.report_path = self._generate_report(result)
        
        return result
    
    def process_imo_problems(self, years: Optional[List[int]] = None,
                            categories: Optional[List[str]] = None) -> WorkflowResult:
        """
        处理IMO题目
        
        Args:
            years: 年份列表，None表示所有年份
            categories: 类别列表，None表示所有类别
            
        Returns:
            工作流结果
        """
        # 加载IMO数据集
        dataset_config = self.config.dataset_config or DatasetConfig(
            base_path="../../03-IMO-Competition"
        )
        processor = IMODatasetProcessor(dataset_config)
        problems = processor.load_problems()
        
        # 过滤
        if years:
            problems = [p for p in problems if p.year in years]
        if categories:
            problems = [p for p in problems if p.category in categories]
        
        logger.info(f"Processing {len(problems)} IMO problems")
        
        # 转换为工作流输入格式
        problem_inputs = [
            {
                "problem_text": p.statement,
                "source": f"IMO {p.year} Problem {p.problem_number}",
                "metadata": {
                    "year": p.year,
                    "problem_number": p.problem_number,
                    "category": p.category,
                    "concepts": p.concepts
                }
            }
            for p in problems
        ]
        
        return self.batch_process(problem_inputs)
    
    def _generate_report(self, result: WorkflowResult) -> str:
        """生成报告"""
        report_path = Path(self.config.output_dir) / f"report_{result.workflow_id}.md"
        
        md = f"""# 自动形式化工作流报告

## 概览

- **工作流ID**: {result.workflow_id}
- **总任务数**: {result.total_tasks}
- **成功**: {result.successful_tasks}
- **失败**: {result.failed_tasks}
- **成功率**: {result.successful_tasks / result.total_tasks * 100:.1f}%
- **总耗时**: {result.total_time_ms / 1000:.2f} 秒
- **平均耗时**: {result.total_time_ms / result.total_tasks:.0f} ms/任务

## 任务详情

"""
        
        for task in result.tasks:
            md += f"""### {task.task_id}

- **来源**: {task.source or "N/A"}
- **状态**: {'✅ 成功' if task.status == 'success' else '❌ 失败'}
- **重试次数**: {task.retry_count}
"""
            
            if task.error_message:
                md += f"- **错误**: {task.error_message}\n"
            
            # MSC推荐
            if task.msc_recommendations:
                md += "- **MSC推荐**:\n"
                for rec in task.msc_recommendations[:3]:
                    md += f"  - {rec.code}: {rec.description} (置信度: {rec.confidence:.2f})\n"
            
            # 验证结果
            if task.verification_result:
                vr = task.verification_result
                md += f"- **验证结果**: {vr.status.value}\n"
                md += f"- **错误数**: {len(vr.errors)}\n"
                md += f"- **警告数**: {len(vr.warnings)}\n"
            
            # 生成的代码
            if task.generated_lean_code:
                md += "\n**生成的Lean 4代码**:\n\n```lean4\n"
                md += task.generated_lean_code[:500]  # 只显示前500字符
                if len(task.generated_lean_code) > 500:
                    md += "\n... (truncated)"
                md += "\n```\n"
            
            md += "\n---\n\n"
        
        # 保存报告
        report_path.write_text(md, encoding='utf-8')
        logger.info(f"Report saved to {report_path}")
        
        # 同时保存JSON格式的详细结果
        json_path = Path(self.config.output_dir) / f"result_{result.workflow_id}.json"
        json_data = {
            "workflow_id": result.workflow_id,
            "summary": {
                "total_tasks": result.total_tasks,
                "successful": result.successful_tasks,
                "failed": result.failed_tasks,
                "success_rate": result.successful_tasks / result.total_tasks,
                "total_time_ms": result.total_time_ms
            },
            "tasks": [task.to_dict() for task in result.tasks]
        }
        json_path.write_text(json.dumps(json_data, indent=2, ensure_ascii=False), encoding='utf-8')
        
        return str(report_path)
    
    def interactive_mode(self) -> None:
        """交互式模式"""
        print("=" * 60)
        print("自动形式化工作流 - 交互式模式")
        print("=" * 60)
        print("\n选项:")
        print("1. 输入数学问题")
        print("2. 处理IMO题目")
        print("3. 批量处理文件")
        print("q. 退出")
        print("-" * 60)
        
        while True:
            choice = input("\n选择 (1-3, q): ").strip().lower()
            
            if choice == 'q':
                break
            
            elif choice == '1':
                print("\n输入数学问题（结束输入请在新行输入 'EOF'）:")
                lines = []
                while True:
                    line = input()
                    if line.strip() == 'EOF':
                        break
                    lines.append(line)
                
                problem_text = '\n'.join(lines)
                
                print("\n处理中...")
                task = self.process_problem(problem_text)
                
                print("\n" + "=" * 60)
                if task.status == "success":
                    print("✅ 形式化成功!")
                    print("-" * 60)
                    print("MSC推荐:")
                    for rec in task.msc_recommendations[:3]:
                        print(f"  - {rec.code}: {rec.description}")
                    print("-" * 60)
                    print("生成的Lean 4代码:")
                    print(task.generated_lean_code)
                    
                    if task.verification_result:
                        print("-" * 60)
                        print(f"验证结果: {task.verification_result.status.value}")
                else:
                    print(f"❌ 失败: {task.error_message}")
                print("=" * 60)
            
            elif choice == '2':
                year_input = input("输入年份 (逗号分隔, 或 'all'): ").strip()
                years = None if year_input.lower() == 'all' else [
                    int(y.strip()) for y in year_input.split(',') if y.strip().isdigit()
                ]
                
                result = self.process_imo_problems(years=years)
                
                print(f"\n处理完成!")
                print(f"  总数: {result.total_tasks}")
                print(f"  成功: {result.successful_tasks}")
                print(f"  失败: {result.failed_tasks}")
                print(f"  报告: {result.report_path}")
            
            elif choice == '3':
                file_path = input("输入JSON文件路径: ").strip()
                
                if not os.path.exists(file_path):
                    print(f"文件不存在: {file_path}")
                    continue
                
                with open(file_path, 'r', encoding='utf-8') as f:
                    problems = json.load(f)
                
                result = self.batch_process(problems)
                
                print(f"\n处理完成!")
                print(f"  总数: {result.total_tasks}")
                print(f"  成功: {result.successful_tasks}")
                print(f"  失败: {result.failed_tasks}")
                print(f"  报告: {result.report_path}")
            
            else:
                print("无效选择")


# 便捷函数
def quick_formalize(problem_text: str, 
                   api_key: Optional[str] = None,
                   verify: bool = True) -> Dict[str, Any]:
    """
    快速形式化单个问题
    
    Args:
        problem_text: 数学问题文本
        api_key: DeepSeek API密钥
        verify: 是否验证
        
    Returns:
        结果字典
    """
    config = WorkflowConfig()
    if api_key:
        config.deepseek_config = DeepSeekConfig(api_key=api_key)
    config.verify_after_formalization = verify
    
    workflow = AutoFormalizationWorkflow(config)
    task = workflow.process_problem(problem_text)
    
    return {
        "success": task.status == "success",
        "lean_code": task.generated_lean_code,
        "msc_codes": [
            {"code": r.code, "description": r.description}
            for r in task.msc_recommendations
        ],
        "verification": {
            "status": task.verification_result.status.value if task.verification_result else "skipped",
            "is_valid": task.verification_result.is_valid if task.verification_result else None
        } if task.verification_result else None,
        "error": task.error_message if task.status == "failed" else None
    }


if __name__ == "__main__":
    # 示例用法
    workflow = AutoFormalizationWorkflow()
    workflow.interactive_mode()
