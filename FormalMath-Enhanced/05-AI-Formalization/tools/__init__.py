"""
AI形式化数学工具包

提供数学问题的自动形式化转换、验证和数据处理功能。
"""

from .deepseek_client import (
    DeepSeekClient,
    DeepSeekConfig,
    FormalizationMode,
    FormalizationResult,
    formalize_problem
)

from .lean_verifier import (
    LeanVerifier,
    LeanProjectConfig,
    VerificationResult,
    VerificationStatus,
    LeanError,
    verify_lean_code,
    check_syntax
)

from .imo_dataset import (
    IMODatasetProcessor,
    DatasetConfig,
    IMOProblem,
    load_imo_problems,
    export_imo_dataset
)

from .msc_recommender import (
    MSCRecommender,
    MSCRecommendation,
    MSCCode,
    recommend_msc,
    get_category_name
)

from .auto_formalize import (
    AutoFormalizationWorkflow,
    WorkflowConfig,
    FormalizationTask,
    WorkflowResult,
    quick_formalize
)

__version__ = "1.0.0"
__author__ = "FormalMath Team"

__all__ = [
    # DeepSeek客户端
    "DeepSeekClient",
    "DeepSeekConfig",
    "FormalizationMode",
    "FormalizationResult",
    "formalize_problem",
    
    # Lean验证器
    "LeanVerifier",
    "LeanProjectConfig",
    "VerificationResult",
    "VerificationStatus",
    "LeanError",
    "verify_lean_code",
    "check_syntax",
    
    # IMO数据集
    "IMODatasetProcessor",
    "DatasetConfig",
    "IMOProblem",
    "load_imo_problems",
    "export_imo_dataset",
    
    # MSC推荐器
    "MSCRecommender",
    "MSCRecommendation",
    "MSCCode",
    "recommend_msc",
    "get_category_name",
    
    # 自动化工作流
    "AutoFormalizationWorkflow",
    "WorkflowConfig",
    "FormalizationTask",
    "WorkflowResult",
    "quick_formalize"
]
