"""
个性化学习路径推荐系统 - 主入口

命令行界面和演示运行器
"""

import argparse
import json
import sys
from datetime import datetime
from typing import Optional

from user_profile import UserProfile, create_preset_profile, LearningStyle
from recommendation_engine import RecommendationEngine, PathStrategy, create_sample_graph
from path_visualization import DashboardRenderer, VisualizationTheme
from api import (
    UserProfileAPI, RecommendationAPI, VisualizationAPI,
    initialize_default_engine
)


def print_header(text: str):
    """打印标题"""
    print("\n" + "=" * 60)
    print(f" {text}")
    print("=" * 60)


def print_section(text: str):
    """打印小节标题"""
    print(f"\n--- {text} ---")


def demo_full_workflow():
    """演示完整工作流"""
    print_header("个性化学习路径推荐系统 - 完整演示")
    
    # 1. 初始化概念图
    print_section("1. 初始化知识图谱")
    concept_graph = create_sample_graph()
    print(f"✓ 加载了 {len(concept_graph.graph.nodes)} 个概念")
    print(f"✓ 建立了 {len(concept_graph.graph.edges)} 条依赖关系")
    
    # 2. 创建用户画像
    print_section("2. 创建用户画像")
    print("选择用户类型:")
    print("  1. 初学者学生")
    print("  2. 进阶学习者")
    print("  3. 研究者")
    print("  4. 视觉型学习者")
    print("  5. 实践型学习者")
    
    choice = input("\n请选择 (1-5) [默认: 2]: ").strip() or "2"
    preset_map = {
        "1": "beginner_student",
        "2": "advanced_learner",
        "3": "researcher",
        "4": "visual_learner",
        "5": "practical_learner"
    }
    
    preset_type = preset_map.get(choice, "advanced_learner")
    user = create_preset_profile(preset_type, name="演示用户")
    
    print(f"✓ 创建用户: {user.name}")
    print(f"  - 学习风格: {user.learning_preference.get_dominant_style().value}")
    print(f"  - 每日学习: {user.time_preference.daily_hours}小时")
    
    # 3. 设置已掌握概念
    print_section("3. 设置先验知识")
    
    # 模拟一些已掌握的概念
    user.update_mastery("set_theory", 0.85)
    user.update_mastery("functions", 0.75)
    user.update_mastery("relations", 0.70)
    
    print("已掌握概念:")
    for cid in user.get_mastered_concept_ids():
        mastery = user.get_concept_mastery(cid)
        print(f"  - {cid}: {mastery:.0%}")
    
    # 4. 设置学习目标
    print_section("4. 设置学习目标")
    target_concepts = ["algebraic_topology", "linear_algebra"]
    print(f"目标概念: {', '.join(target_concepts)}")
    
    # 5. 选择推荐策略
    print_section("5. 选择推荐策略")
    print("可选策略:")
    print("  1. 最短时间 - 最小化总学习时间")
    print("  2. 牢固基础 - 优先打好基础知识")
    print("  3. 快速预览 - 先建立整体框架")
    print("  4. 平衡模式 - 综合优化")
    print("  5. 自适应 - 智能选择最佳策略")
    
    strategy_choice = input("\n请选择 (1-5) [默认: 5]: ").strip() or "5"
    strategy_map = {
        "1": PathStrategy.SHORTEST_TIME,
        "2": PathStrategy.SOLID_FOUNDATION,
        "3": PathStrategy.QUICK_OVERVIEW,
        "4": PathStrategy.BALANCED,
        "5": PathStrategy.ADAPTIVE
    }
    
    selected_strategy = strategy_map.get(strategy_choice, PathStrategy.ADAPTIVE)
    print(f"✓ 选择策略: {selected_strategy.value}")
    
    # 6. 生成推荐
    print_section("6. 生成学习路径推荐")
    engine = RecommendationEngine(concept_graph)
    
    print("正在分析知识依赖...")
    print("正在计算最优路径...")
    print("正在生成可视化数据...")
    
    paths = engine.recommend(
        user_profile=user,
        strategy=selected_strategy,
        target_concepts=target_concepts,
        num_alternatives=2
    )
    
    print(f"✓ 生成了 {len(paths)} 条推荐路径")
    
    # 7. 展示推荐结果
    print_section("7. 推荐路径详情")
    
    for i, path in enumerate(paths[:3], 1):
        print(f"\n路径 {i}: {path.name}")
        print(f"  策略: {path.strategy.value}")
        print(f"  描述: {path.description}")
        print(f"  概念数: {len(path.nodes)}")
        print(f"  预计时间: {path.total_estimated_hours:.1f}小时")
        print(f"  综合评分: {path.overall_score:.2f}")
        print(f"  难度平滑度: {path.difficulty_smoothness_score:.2f}")
        print(f"  时间效率: {path.time_efficiency_score:.2f}")
        
        # 显示前5个概念
        preview = " -> ".join(path.node_order[:5])
        if len(path.node_order) > 5:
            preview += " -> ..."
        print(f"  学习顺序: {preview}")
    
    # 8. 导出可视化
    print_section("8. 导出可视化")
    
    best_path = paths[0]
    
    # 生成仪表板HTML
    renderer = DashboardRenderer()
    html = renderer.render_full_dashboard(user, best_path, concept_graph)
    
    filename = f"learning_dashboard_{datetime.now().strftime('%Y%m%d_%H%M%S')}.html"
    with open(filename, "w", encoding="utf-8") as f:
        f.write(html)
    
    print(f"✓ 仪表板已保存: {filename}")
    
    # 导出JSON
    json_data = {
        "path": best_path.to_dict(),
        "user": user.to_dict(),
        "export_time": datetime.now().isoformat()
    }
    
    json_filename = f"learning_path_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json"
    with open(json_filename, "w", encoding="utf-8") as f:
        json.dump(json_data, f, ensure_ascii=False, indent=2)
    
    print(f"✓ 路径数据已保存: {json_filename}")
    
    print_header("演示完成")
    print(f"\n推荐路径: {best_path.name}")
    print(f"预计学习时间: {best_path.total_estimated_hours:.1f}小时")
    print(f"开始你的数学之旅吧！")


def run_api_server(host: str = "127.0.0.1", port: int = 8000):
    """运行API服务器"""
    try:
        from fastapi import FastAPI
        from fastapi.responses import JSONResponse, HTMLResponse
        import uvicorn
        
        app = FastAPI(title="个性化学习路径推荐API", version="1.0.0")
        
        # 初始化
        initialize_default_engine()
        
        @app.get("/")
        def root():
            return {"message": "个性化学习路径推荐API", "version": "1.0.0"}
        
        @app.post("/users")
        def create_user(name: str, email: str, preset_type: Optional[str] = None):
            result = UserProfileAPI.create_user(name, email, preset_type)
            return JSONResponse(content=result)
        
        @app.get("/users/{user_id}")
        def get_user(user_id: str):
            result = UserProfileAPI.get_user(user_id)
            return JSONResponse(content=result)
        
        @app.post("/users/{user_id}/mastery")
        def add_mastery(user_id: str, concept_id: str, score: float):
            result = UserProfileAPI.add_mastery(user_id, concept_id, score)
            return JSONResponse(content=result)
        
        @app.post("/recommendations")
        def recommend_paths(user_id: str, strategy: str = "adaptive"):
            result = RecommendationAPI.recommend_paths(user_id, strategy=strategy)
            return JSONResponse(content=result)
        
        @app.get("/visualizations/timeline/{user_id}/{path_id}")
        def get_timeline(user_id: str, path_id: str):
            result = VisualizationAPI.get_timeline(user_id, path_id)
            return JSONResponse(content=result)
        
        @app.get("/visualizations/dashboard/{user_id}/{path_id}", response_class=HTMLResponse)
        def get_dashboard(user_id: str, path_id: str):
            result = VisualizationAPI.export_dashboard_html(user_id, path_id)
            if result.get("success"):
                return HTMLResponse(content=result["data"]["html"])
            return JSONResponse(content=result)
        
        print(f"启动API服务器: http://{host}:{port}")
        uvicorn.run(app, host=host, port=port)
        
    except ImportError:
        print("错误: 需要安装FastAPI和uvicorn才能运行API服务器")
        print("  pip install fastapi uvicorn")
        sys.exit(1)


def run_tests():
    """运行测试"""
    print_header("运行测试")
    
    import subprocess
    
    # 测试用户画像
    print("\n测试用户画像模块...")
    result = subprocess.run([sys.executable, "user_profile.py"], 
                          capture_output=True, text=True)
    if result.returncode == 0:
        print("✓ 用户画像模块测试通过")
    else:
        print("✗ 用户画像模块测试失败")
        print(result.stderr)
    
    # 测试推荐引擎
    print("\n测试推荐引擎模块...")
    result = subprocess.run([sys.executable, "recommendation_engine.py"], 
                          capture_output=True, text=True)
    if result.returncode == 0:
        print("✓ 推荐引擎模块测试通过")
    else:
        print("✗ 推荐引擎模块测试失败")
        print(result.stderr)
    
    # 测试可视化
    print("\n测试可视化模块...")
    result = subprocess.run([sys.executable, "path_visualization.py"], 
                          capture_output=True, text=True)
    if result.returncode == 0:
        print("✓ 可视化模块测试通过")
    else:
        print("✗ 可视化模块测试失败")
        print(result.stderr)
    
    # 测试API
    print("\n测试API模块...")
    result = subprocess.run([sys.executable, "api.py"], 
                          capture_output=True, text=True)
    if result.returncode == 0:
        print("✓ API模块测试通过")
    else:
        print("✗ API模块测试失败")
        print(result.stderr)
    
    print_header("测试完成")


def main():
    """主函数"""
    parser = argparse.ArgumentParser(
        description="个性化学习路径推荐系统",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
使用示例:
  %(prog)s demo              # 运行完整演示
  %(prog)s api               # 启动API服务器
  %(prog)s test              # 运行测试
        """
    )
    
    parser.add_argument(
        "command",
        choices=["demo", "api", "test"],
        help="要执行的命令"
    )
    
    parser.add_argument(
        "--host",
        default="127.0.0.1",
        help="API服务器主机 (默认: 127.0.0.1)"
    )
    
    parser.add_argument(
        "--port",
        type=int,
        default=8000,
        help="API服务器端口 (默认: 8000)"
    )
    
    args = parser.parse_args()
    
    if args.command == "demo":
        demo_full_workflow()
    elif args.command == "api":
        run_api_server(args.host, args.port)
    elif args.command == "test":
        run_tests()
    else:
        parser.print_help()


if __name__ == "__main__":
    main()
