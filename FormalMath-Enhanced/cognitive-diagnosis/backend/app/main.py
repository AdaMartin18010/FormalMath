"""
FastAPI主应用入口
"""

from fastapi import FastAPI
from fastapi.middleware.cors import CORSMiddleware

from app.api import diagnosis, questions, reports
from app.core.config import settings

app = FastAPI(
    title="认知诊断系统 API",
    description="基于HCD框架的认知诊断系统",
    version="1.0.0",
)

# CORS配置
app.add_middleware(
    CORSMiddleware,
    allow_origins=settings.ALLOWED_HOSTS,
    allow_credentials=True,
    allow_methods=["*"],
    allow_headers=["*"],
)

# 注册路由
app.include_router(diagnosis.router, prefix="/api/diagnosis", tags=["诊断"])
app.include_router(questions.router, prefix="/api/questions", tags=["题目"])
app.include_router(reports.router, prefix="/api/reports", tags=["报告"])


@app.get("/")
async def root():
    return {
        "message": "认知诊断系统 API",
        "version": "1.0.0",
        "docs": "/docs"
    }


@app.get("/health")
async def health_check():
    return {"status": "healthy"}
