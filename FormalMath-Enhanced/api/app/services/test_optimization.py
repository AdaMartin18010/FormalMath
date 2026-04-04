"""
语义搜索优化效果测试
对比原始版本和优化版本的性能差异
"""
import time
import statistics
from typing import List, Dict, Any
import json


class OptimizationComparisonTest:
    """优化效果对比测试"""
    
    def __init__(self):
        self.original_service = None
        self.optimized_service = None
        self.test_results = []
    
    def setup_services(self):
        """初始化服务"""
        print("初始化搜索服务...")
        
        # 导入原始版本
        from .semantic_search_service import (
            SemanticSearchService, 
            SearchRequest as OriginalRequest
        )
        self.original_service = SemanticSearchService()
        self.OriginalRequest = OriginalRequest
        
        # 导入优化版本
        from .semantic_search_optimized import (
            OptimizedSemanticSearchService,
            SearchRequest as OptimizedRequest
        )
        self.optimized_service = OptimizedSemanticSearchService()
        self.OptimizedRequest = OptimizedRequest
    
    def setup_test_data(self):
        """设置测试数据"""
        self.test_documents = [
            {
                "id": f"doc_{i:03d}",
                "content": f"""
                Mathematical analysis is the branch of mathematics dealing with limits and related theories, 
                such as differentiation {i}, integration, measure, infinite series, and analytic functions.
                The fundamental theorem of calculus states that differentiation and integration are inverse operations.
                $$\\int_a^b f(x) dx = F(b) - F(a)$$
                where $F$ is the antiderivative of $f$.
                """,
                "metadata": {"subject": "analysis", "level": i % 3}
            }
            for i in range(100)
        ]
        
        self.test_queries = [
            "fundamental theorem calculus",
            "integration differentiation inverse",
            "mathematical analysis limits",
            "infinite series convergence",
            "analytic functions complex"
        ]
    
    def index_documents(self):
        """索引测试文档"""
        print("索引测试文档...")
        
        for doc in self.test_documents:
            self.original_service.index_document(
                doc_id=doc["id"],
                content=doc["content"],
                metadata=doc["metadata"]
            )
            self.optimized_service.index_document(
                doc_id=doc["id"],
                content=doc["content"],
                metadata=doc["metadata"]
            )
    
    def test_search_latency(self, iterations: int = 50) -> Dict[str, Any]:
        """测试搜索延迟"""
        print(f"\n测试搜索延迟 ({iterations} 次迭代)...")
        
        original_times = []
        optimized_times = []
        
        for query in self.test_queries:
            for _ in range(iterations // len(self.test_queries)):
                # 测试原始版本
                start = time.time()
                self.original_service.search(
                    self.OriginalRequest(query=query, k=10)
                )
                original_times.append((time.time() - start) * 1000)
                
                # 测试优化版本
                start = time.time()
                self.optimized_service.search(
                    self.OptimizedRequest(query=query, k=10)
                )
                optimized_times.append((time.time() - start) * 1000)
        
        result = {
            "test": "搜索延迟",
            "original_avg_ms": statistics.mean(original_times),
            "optimized_avg_ms": statistics.mean(optimized_times),
            "original_p95_ms": sorted(original_times)[int(len(original_times) * 0.95)],
            "optimized_p95_ms": sorted(optimized_times)[int(len(optimized_times) * 0.95)],
            "improvement": (1 - statistics.mean(optimized_times) / statistics.mean(original_times)) * 100
        }
        
        print(f"  原始版本平均延迟: {result['original_avg_ms']:.2f} ms")
        print(f"  优化版本平均延迟: {result['optimized_avg_ms']:.2f} ms")
        print(f"  P95延迟 - 原始: {result['original_p95_ms']:.2f} ms, 优化: {result['optimized_p95_ms']:.2f} ms")
        print(f"  性能提升: {result['improvement']:.1f}%")
        
        return result
    
    def test_search_quality(self) -> Dict[str, Any]:
        """测试搜索质量"""
        print("\n测试搜索质量...")
        
        quality_scores = {
            "original": [],
            "optimized": []
        }
        
        for query in self.test_queries:
            # 原始版本
            orig_response = self.original_service.search(
                self.OriginalRequest(query=query, k=10)
            )
            
            # 优化版本
            opt_response = self.optimized_service.search(
                self.OptimizedRequest(query=query, k=10, rerank=True)
            )
            
            # 计算平均分数作为质量指标
            orig_avg_score = sum(r.get("combined_score", 0) for r in orig_response.results) / len(orig_response.results) if orig_response.results else 0
            opt_avg_score = sum(r.get("combined_score", 0) for r in opt_response.results) / len(opt_response.results) if opt_response.results else 0
            
            quality_scores["original"].append(orig_avg_score)
            quality_scores["optimized"].append(opt_avg_score)
        
        result = {
            "test": "搜索质量",
            "original_avg_score": statistics.mean(quality_scores["original"]),
            "optimized_avg_score": statistics.mean(quality_scores["optimized"]),
            "improvement": (statistics.mean(quality_scores["optimized"]) / statistics.mean(quality_scores["original"]) - 1) * 100 if quality_scores["original"] else 0
        }
        
        print(f"  原始版本平均分数: {result['original_avg_score']:.4f}")
        print(f"  优化版本平均分数: {result['optimized_avg_score']:.4f}")
        print(f"  质量提升: {result['improvement']:.1f}%")
        
        return result
    
    def test_formula_search(self) -> Dict[str, Any]:
        """测试公式搜索"""
        print("\n测试公式搜索...")
        
        test_formulas = [
            "\\int_a^b f(x) dx",
            "\\sum_{n=1}^{\\infty} \\frac{1}{n^2}",
            "e^{i\\pi} + 1 = 0"
        ]
        
        original_times = []
        optimized_times = []
        
        for formula in test_formulas:
            # 原始版本
            start = time.time()
            self.original_service.search_formula(formula, k=5)
            original_times.append((time.time() - start) * 1000)
            
            # 优化版本
            start = time.time()
            self.optimized_service.search_formula(formula, k=5)
            optimized_times.append((time.time() - start) * 1000)
        
        result = {
            "test": "公式搜索",
            "original_avg_ms": statistics.mean(original_times),
            "optimized_avg_ms": statistics.mean(optimized_times),
            "improvement": (1 - statistics.mean(optimized_times) / statistics.mean(original_times)) * 100
        }
        
        print(f"  原始版本平均延迟: {result['original_avg_ms']:.2f} ms")
        print(f"  优化版本平均延迟: {result['optimized_avg_ms']:.2f} ms")
        print(f"  性能提升: {result['improvement']:.1f}%")
        
        return result
    
    def test_cache_performance(self) -> Dict[str, Any]:
        """测试缓存性能"""
        print("\n测试缓存性能...")
        
        query = self.test_queries[0]
        iterations = 20
        
        # 清除缓存
        if hasattr(self.optimized_service.vector_store, 'query_cache'):
            self.optimized_service.vector_store.query_cache.clear()
        
        # 冷缓存测试
        cold_times = []
        for _ in range(iterations):
            if hasattr(self.optimized_service.vector_store, 'query_cache'):
                self.optimized_service.vector_store.query_cache.clear()
            
            start = time.time()
            self.optimized_service.search(
                self.OptimizedRequest(query=query, k=10)
            )
            cold_times.append((time.time() - start) * 1000)
        
        # 热缓存测试
        warm_times = []
        for _ in range(iterations):
            start = time.time()
            self.optimized_service.search(
                self.OptimizedRequest(query=query, k=10)
            )
            warm_times.append((time.time() - start) * 1000)
        
        result = {
            "test": "缓存性能",
            "cold_cache_avg_ms": statistics.mean(cold_times),
            "warm_cache_avg_ms": statistics.mean(warm_times),
            "speedup": statistics.mean(cold_times) / statistics.mean(warm_times)
        }
        
        print(f"  冷缓存平均延迟: {result['cold_cache_avg_ms']:.2f} ms")
        print(f"  热缓存平均延迟: {result['warm_cache_avg_ms']:.2f} ms")
        print(f"  缓存加速比: {result['speedup']:.2f}x")
        
        return result
    
    def test_different_strategies(self) -> List[Dict[str, Any]]:
        """测试不同重排序策略"""
        print("\n测试不同重排序策略...")
        
        strategies = ["hybrid", "cross_encoder", "rrf", "diversity", "formula"]
        query = self.test_queries[0]
        
        results = []
        for strategy in strategies:
            times = []
            scores = []
            
            for _ in range(10):
                start = time.time()
                response = self.optimized_service.search(
                    self.OptimizedRequest(
                        query=query,
                        k=10,
                        rerank=True,
                        rerank_strategy=strategy
                    )
                )
                times.append((time.time() - start) * 1000)
                
                avg_score = sum(r.get("combined_score", 0) for r in response.results) / len(response.results) if response.results else 0
                scores.append(avg_score)
            
            result = {
                "strategy": strategy,
                "avg_time_ms": statistics.mean(times),
                "avg_score": statistics.mean(scores)
            }
            results.append(result)
            print(f"  {strategy:15s}: {result['avg_time_ms']:6.2f} ms, 分数: {result['avg_score']:.4f}")
        
        return results
    
    def run_all_tests(self) -> Dict[str, Any]:
        """运行所有测试"""
        print("=" * 70)
        print("FormalMath 语义搜索优化效果对比测试")
        print("=" * 70)
        
        try:
            self.setup_services()
            self.setup_test_data()
            self.index_documents()
            
            # 运行各项测试
            results = {
                "latency": self.test_search_latency(),
                "quality": self.test_search_quality(),
                "formula": self.test_formula_search(),
                "cache": self.test_cache_performance(),
                "strategies": self.test_different_strategies()
            }
            
            # 生成汇总
            summary = {
                "avg_latency_improvement": results["latency"]["improvement"],
                "avg_quality_improvement": results["quality"]["improvement"],
                "formula_search_improvement": results["formula"]["improvement"],
                "cache_speedup": results["cache"]["speedup"]
            }
            
            results["summary"] = summary
            
            print("\n" + "=" * 70)
            print("测试结果汇总")
            print("=" * 70)
            print(f"平均延迟提升: {summary['avg_latency_improvement']:+.1f}%")
            print(f"搜索质量提升: {summary['avg_quality_improvement']:+.1f}%")
            print(f"公式搜索提升: {summary['formula_search_improvement']:+.1f}%")
            print(f"缓存加速比: {summary['cache_speedup']:.2f}x")
            
            # 保存结果
            with open("optimization_test_results.json", "w") as f:
                json.dump(results, f, indent=2)
            print("\n详细结果已保存到: optimization_test_results.json")
            
            return results
            
        except Exception as e:
            print(f"\n测试过程中出错: {e}")
            import traceback
            traceback.print_exc()
            return {"error": str(e)}


def main():
    """主函数"""
    test = OptimizationComparisonTest()
    return test.run_all_tests()


if __name__ == "__main__":
    main()
