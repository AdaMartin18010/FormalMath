"""
自适应学习路径系统主入口
FastAPI应用配置
"""

import os
import sys
from contextlib import asynccontextmanager

from fastapi import FastAPI
from fastapi.middleware.cors import CORSMiddleware
from fastapi.staticfiles import StaticFiles

# 确保可以导入本地模块
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from api.routes import router, initialize_services
from models.knowledge_graph import (
    KnowledgeGraph, ConceptNode, RelationEdge,
    FORMALMATH_CONCEPTS, FORMALMATH_RELATIONS
)


def init_knowledge_graph() -> KnowledgeGraph:
    """初始化知识图谱"""
    kg = KnowledgeGraph(name="FormalMath Knowledge Graph", version="1.0")
    
    # 添加概念节点
    concept_id_map = {}
    for concept_data in FORMALMATH_CONCEPTS:
        node = ConceptNode(
            name=concept_data["name"],
            msc_code=concept_data["msc_code"],
            difficulty=concept_data["difficulty"],
            estimated_time_minutes=concept_data["estimated_time_minutes"],
            description=concept_data["description"]
        )
        cid = kg.add_node(node)
        concept_id_map[concept_data["name"]] = cid
    
    # 添加关系边
    for relation in FORMALMATH_RELATIONS:
        source_name = relation["source"]
        target_name = relation["target"]
        
        if source_name in concept_id_map and target_name in concept_id_map:
            edge = RelationEdge(
                source_id=concept_id_map[source_name],
                target_id=concept_id_map[target_name],
                relation_type=relation["type"],
                weight=relation["weight"],
                strength=relation["strength"]
            )
            kg.add_edge(edge)
    
    return kg


@asynccontextmanager
async def lifespan(app: FastAPI):
    """应用生命周期管理"""
    # 启动时初始化
    print("🚀 初始化自适应学习路径系统...")
    
    # 初始化知识图谱
    kg = init_knowledge_graph()
    print(f"✅ 知识图谱初始化完成: {len(kg.nodes)} 个概念, {len(kg.edges)} 条关系")
    
    # 初始化服务
    data_dir = os.path.join(os.path.dirname(os.path.dirname(__file__)), "..", "data")
    data_dir = os.path.abspath(data_dir)
    os.makedirs(data_dir, exist_ok=True)
    
    initialize_services(kg, data_dir)
    print("✅ 服务初始化完成")
    
    yield
    
    # 关闭时清理
    print("👋 关闭自适应学习路径系统...")


# 创建FastAPI应用
app = FastAPI(
    title="FormalMath 自适应学习路径系统",
    description="基于知识图谱和认知诊断的个性化学习路径生成与管理系统",
    version="1.0.0",
    lifespan=lifespan
)

# 配置CORS
app.add_middleware(
    CORSMiddleware,
    allow_origins=["*"],  # 生产环境应限制为特定域名
    allow_credentials=True,
    allow_methods=["*"],
    allow_headers=["*"],
)

# 注册路由
app.include_router(router, prefix="/api/v1")


# 健康检查
@app.get("/health")
async def health_check():
    """健康检查端点"""
    return {
        "status": "healthy",
        "service": "adaptive-learning-system",
        "version": "1.0.0"
    }


# 系统信息
@app.get("/info")
async def system_info():
    """系统信息"""
    return {
        "name": "FormalMath 自适应学习路径系统",
        "version": "1.0.0",
        "features": [
            "学习者特征分析",
            "个性化路径生成",
            "实时调整机制",
            "学习支持系统",
            "资源推荐",
            "学习伙伴匹配",
            "难点预警",
            "成就系统"
        ],
        "api_version": "v1",
        "api_prefix": "/api/v1"
    }


# 根路径
@app.get("/")
async def root():
    """根路径重定向到文档"""
    return {
        "message": "FormalMath 自适应学习路径系统 API",
        "docs": "/docs",
        "api": "/api/v1"
    }


if __name__ == "__main__":
    import uvicorn
    
    # 启动服务器
    uvicorn.run(
        "main:app",
        host="0.0.0.0",
        port=8000,
        reload=True,
        log_level="info"
    )
