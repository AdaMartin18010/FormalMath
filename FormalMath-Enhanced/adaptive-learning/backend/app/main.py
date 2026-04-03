"""
FormalMath 自适应学习路径系统 - FastAPI 主应用
"""
from fastapi import FastAPI
from fastapi.middleware.cors import CORSMiddleware
from contextlib import asynccontextmanager

from .api.adaptive_routes import router as adaptive_router
from .knowledge_graph import get_knowledge_graph
from .core.config import settings


@asynccontextmanager
async def lifespan(app: FastAPI):
    """
    应用生命周期管理
    
    启动时加载知识图谱
    """
    # 启动时执行
    print("正在加载知识图谱...")
    kg = get_knowledge_graph()
    if kg._initialized:
        print(f"知识图谱加载完成: {len(kg.concepts)} 个概念")
    else:
        print("警告: 知识图谱加载失败")
    
    yield
    
    # 关闭时执行
    print("应用关闭")


# 创建 FastAPI 应用
app = FastAPI(
    title=settings.APP_NAME,
    version=settings.APP_VERSION,
    description="""
    FormalMath 自适应学习路径系统 API
    
    提供个性化学习路径生成、实时路径调整、学习资源推荐等功能。
    
    ## 主要功能
    
    - **学习路径生成**: 基于 A* 算法、动态规划等算法生成最优学习路径
    - **路径实时调整**: 根据学习表现动态调整学习路径
    - **资源推荐**: 基于认知风格和学习偏好推荐学习资源
    - **进度追踪**: 实时追踪学习进度和掌握度
    
    ## 技术栈
    
    - FastAPI
    - NetworkX (知识图谱)
    - Python 3.8+
    """,
    lifespan=lifespan
)

# 配置 CORS
app.add_middleware(
    CORSMiddleware,
    allow_origins=settings.CORS_ORIGINS,
    allow_credentials=True,
    allow_methods=["*"],
    allow_headers=["*"],
)

# 注册路由
app.include_router(
    adaptive_router,
    prefix=settings.API_PREFIX
)


@app.get("/")
async def root():
    """根路径 - 服务状态检查"""
    return {
        "name": settings.APP_NAME,
        "version": settings.APP_VERSION,
        "status": "running",
        "docs_url": "/docs",
        "api_prefix": settings.API_PREFIX
    }


@app.get("/health")
async def health_check():
    """健康检查端点"""
    kg = get_knowledge_graph()
    
    return {
        "status": "healthy",
        "knowledge_graph": {
            "loaded": kg._initialized,
            "concepts_count": len(kg.concepts) if kg._initialized else 0
        },
        "api_version": settings.APP_VERSION
    }


@app.get("/api/v1/concept-graph")
async def get_concept_graph():
    """
    获取完整的概念图谱（用于可视化）
    
    返回知识图谱的节点和边数据
    """
    kg = get_knowledge_graph()
    
    if not kg._initialized:
        return {"error": "知识图谱未加载"}
    
    # 构建图数据
    nodes = []
    for concept_id, concept in kg.concepts.items():
        nodes.append({
            "id": concept_id,
            "name": concept.name,
            "branch": concept.branch,
            "difficulty": concept.difficulty.value,
            "description": concept.description
        })
    
    edges = []
    for relation in kg.relations:
        edges.append({
            "source": relation.source,
            "target": relation.target,
            "type": relation.type.value,
            "description": relation.description
        })
    
    return {
        "nodes": nodes,
        "edges": edges,
        "stats": {
            "total_concepts": len(nodes),
            "total_relations": len(edges)
        }
    }


if __name__ == "__main__":
    import uvicorn
    uvicorn.run(app, host="0.0.0.0", port=8000)
