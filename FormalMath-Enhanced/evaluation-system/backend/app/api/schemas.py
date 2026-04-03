"""Pydantic schemas for API."""
from datetime import datetime
from typing import Dict, List, Optional, Any
from pydantic import BaseModel, Field
from enum import Enum


# Enums
class EvaluationTypeEnum(str, Enum):
    PROCESS = "process"
    VALUE_ADDED = "value_added"
    PERFORMANCE = "performance"
    DIVERGENT = "divergent"
    COMPREHENSIVE = "comprehensive"


# Assessment Schemas
class DimensionScores(BaseModel):
    """Five dimension scores."""
    knowledge_mastery: float = Field(..., ge=0, le=100, description="知识掌握度")
    problem_solving: float = Field(..., ge=0, le=100, description="问题解决能力")
    proof_ability: float = Field(..., ge=0, le=100, description="证明能力")
    application: float = Field(..., ge=0, le=100, description="应用能力")
    innovation: float = Field(..., ge=0, le=100, description="创新思维")


class AssessmentRequest(BaseModel):
    """Request for assessment."""
    user_id: str = Field(..., description="用户ID")
    scores: DimensionScores
    evaluation_type: EvaluationTypeEnum = Field(
        default=EvaluationTypeEnum.COMPREHENSIVE,
        description="评估类型"
    )
    period: Optional[str] = Field(None, description="评估周期")
    assessor_id: Optional[str] = Field(None, description="评估者ID")
    notes: Optional[str] = Field(None, description="备注")
    raw_data: Optional[Dict[str, Any]] = Field(None, description="原始数据")


class AssessmentResponse(BaseModel):
    """Response from assessment."""
    record_id: str
    user_id: str
    evaluation_type: str
    scores: Dict[str, Any]
    created_at: str


# Report Schemas
class ReportRequest(BaseModel):
    """Request for report generation."""
    user_id: str
    record_id: Optional[str] = None
    include_history: bool = True
    include_comparison: bool = False
    format: str = Field(default="json", regex="^(json|pdf)$")


class DimensionScoreDetail(BaseModel):
    """Detailed dimension score."""
    name: str
    score: float
    weight: float
    weighted_score: float
    percentage: float


class ReportResponse(BaseModel):
    """Evaluation report response."""
    report_metadata: Dict[str, Any]
    executive_summary: Dict[str, Any]
    detailed_scores: Dict[str, Any]
    dimension_analysis: Dict[str, Any]
    strengths_and_improvements: Dict[str, Any]
    feedback: Optional[Dict[str, Any]] = None
    learning_trajectory: Optional[Dict[str, Any]] = None


# Progress/Trajectory Schemas
class TrajectoryDataPoint(BaseModel):
    """Single trajectory data point."""
    date: str
    period: Optional[str]
    scores: Dict[str, float]


class ProgressRequest(BaseModel):
    """Request for progress data."""
    user_id: str
    start_date: Optional[str] = None
    end_date: Optional[str] = None
    periods: int = Field(default=6, ge=1, le=24)


class ProgressResponse(BaseModel):
    """Progress/trajectory response."""
    user_id: str
    data_points: int
    trajectory: List[TrajectoryDataPoint]
    growth_analysis: Optional[Dict[str, Any]] = None


# Feedback Schemas
class FeedbackRequest(BaseModel):
    """Request for feedback generation."""
    user_id: str
    record_id: str
    custom_template: Optional[str] = None


class FeedbackResponse(BaseModel):
    """Feedback response."""
    feedback_id: str
    user_id: str
    record_id: str
    summary: str
    strengths: List[Dict[str, Any]]
    weaknesses: List[Dict[str, Any]]
    suggestions: List[Dict[str, Any]]
    dimension_feedback: Dict[str, List[str]]
    recommended_resources: List[Dict[str, Any]]
    recommended_path: Dict[str, Any]
    generated_at: str


# Comparison Schemas
class ComparisonRequest(BaseModel):
    """Request for class comparison."""
    user_id: str
    class_user_ids: List[str]


class ComparisonResponse(BaseModel):
    """Class comparison response."""
    user_id: str
    class_size: int
    user_scores: Dict[str, float]
    class_average: Dict[str, float]
    comparison: Dict[str, Dict[str, Any]]
    rank_percentile: float


# Standard/Criteria Schemas
class EvaluationStandardCreate(BaseModel):
    """Create evaluation standard."""
    name: str
    evaluation_type: EvaluationTypeEnum
    description: Optional[str] = None
    criteria: Dict[str, Any]
    scoring_rules: Optional[Dict[str, Any]] = None
    dimension_weights: Optional[Dict[str, float]] = None


class EvaluationStandardResponse(BaseModel):
    """Evaluation standard response."""
    id: int
    name: str
    evaluation_type: str
    description: Optional[str]
    criteria: Dict[str, Any]
    is_active: bool
    created_at: datetime


# Error Schema
class ErrorResponse(BaseModel):
    """Error response."""
    error: str
    detail: Optional[str] = None
