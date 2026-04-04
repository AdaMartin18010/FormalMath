"""
语义搜索性能基准测试
- 响应时间测试
- 准确率评估
- 吞吐量测试
- 对比分析
"""
import time
import random
import statistics
from typing import List, Dict, Tuple, Any
from dataclasses import dataclass, field
from datetime import datetime
import json
import os

# 测试数据生成
SAMPLE_MATH_DOCUMENTS = [
    {
        "id": "doc_001",
        "content": """
        The Riemann Hypothesis is a conjecture that the Riemann zeta function has its zeros 
        only at the negative even integers and complex numbers with real part 1/2. 
        $$\\zeta(s) = \\sum_{n=1}^{\\infty} \\frac{1}{n^s}$$
        This is one of the most important unsolved problems in mathematics.
        """,
        "metadata": {"subject": "number_theory", "difficulty": "advanced"}
    },
    {
        "id": "doc_002",
        "content": """
        Euler's identity is often cited as an example of deep mathematical beauty. 
        $$e^{i\\pi} + 1 = 0$$
        Three basic arithmetic operations occur exactly once each: addition, multiplication, and exponentiation.
        """,
        "metadata": {"subject": "complex_analysis", "difficulty": "intermediate"}
    },
    {
        "id": "doc_003",
        "content": """
        The Fundamental Theorem of Calculus establishes the relationship between differentiation and integration.
        $$\\int_a^b f(x) dx = F(b) - F(a)$$
        where F is the antiderivative of f.
        """,
        "metadata": {"subject": "calculus", "difficulty": "intermediate"}
    },
    {
        "id": "doc_004",
        "content": """
        Linear algebra is the branch of mathematics concerning linear equations, linear functions, and their representations 
        through matrices and vector spaces. A matrix $A$ is invertible if there exists $A^{-1}$ such that $AA^{-1} = I$.
        """,
        "metadata": {"subject": "linear_algebra", "difficulty": "beginner"}
    },
    {
        "id": "doc_005",
        "content": """
        The Pythagorean theorem states that in a right triangle, the square of the hypotenuse equals the sum of 
        squares of the other two sides: $a^2 + b^2 = c^2$.
        """,
        "metadata": {"subject": "geometry", "difficulty": "beginner"}
    },
    {
        "id": "doc_006",
        "content": """
        Fourier series represent periodic functions as sums of sine and cosine waves.
        $$f(x) = \\frac{a_0}{2} + \\sum_{n=1}^{\\infty} (a_n \\cos(nx) + b_n \\sin(nx))$$
        """,
        "metadata": {"subject": "analysis", "difficulty": "advanced"}
    },
    {
        "id": "doc_007",
        "content": """
        Group theory studies the algebraic structures known as groups. A group $(G, \\cdot)$ satisfies closure, 
        associativity, identity, and inverse properties.
        """,
        "metadata": {"subject": "algebra", "difficulty": "intermediate"}
    },
    {
        "id": "doc_008",
        "content": """
        The Navier-Stokes equations describe the motion of viscous fluid substances.
        $$\\rho(\\frac{\\partial \\mathbf{u}}{\\partial t} + \\mathbf{u} \\cdot \\nabla \\mathbf{u}) = -\\nabla p + \\mu \\nabla^2 \\mathbf{u} + \\mathbf{f}$$
        """,
        "metadata": {"subject": "pde", "difficulty": "advanced"}
    },
    {
        "id": "doc_009",
        "content": """
        Probability theory is the branch of mathematics concerned with probability. 
        The normal distribution has probability density function:
        $$f(x) = \\frac{1}{\\sigma\\sqrt{2\\pi}} e^{-\\frac{(x-\\mu)^2}{2\\sigma^2}}$$
        """,
        "metadata": {"subject": "probability", "difficulty": "intermediate"}
    },
    {
        "id": "doc_010",
        "content": """
        Topology studies properties of space that are preserved under continuous deformations.
        A topological space $(X, \\tau)$ consists of a set X and a collection of open sets.
        """,
        "metadata": {"subject": "topology", "difficulty": "advanced"}
    }
]

SAMPLE_QUERIES = [
    {"query": "Riemann zeta function zeros", "relevant_docs": ["doc_001"], "type": "math_concept"},
    {"query": "Euler identity complex numbers", "relevant_docs": ["doc_002"], "type": "math_concept"},
    {"query": "fundamental theorem calculus integration", "relevant_docs": ["doc_003"], "type": "theorem"},
    {"query": "matrix linear algebra inverse", "relevant_docs": ["doc_004"], "type": "concept"},
    {"query": "Pythagorean theorem right triangle", "relevant_docs": ["doc_005"], "type": "theorem"},
    {"query": "Fourier series sine cosine", "relevant_docs": ["doc_006"], "type": "math_concept"},
    {"query": "group theory algebraic structure", "relevant_docs": ["doc_007"], "type": "concept"},
    {"query": "Navier-Stokes fluid equation", "relevant_docs": ["doc_008"], "type": "equation"},
    {"query": "probability normal distribution", "relevant_docs": ["doc_009"], "type": "concept"},
    {"query": "topology continuous space", "relevant_docs": ["doc_010"], "type": "concept"}
]

SAMPLE_FORMULAS = [
    {"latex": "\\zeta(s) = \\sum_{n=1}^{\\infty} \\frac{1}{n^s}", "related_docs": ["doc_001"]},
    {"latex": "e^{i\\pi} + 1 = 0", "related_docs": ["doc_002"]},
    {"latex": "\\int_a^b f(x) dx = F(b) - F(a)", "related_docs": ["doc_003"]},
    {"latex": "a^2 + b^2 = c^2", "related_docs": ["doc_005"]},
    {"latex": "\\frac{1}{\\sigma\\sqrt{2\\pi}} e^{-\\frac{(x-\\mu)^2}{2\\sigma^2}}", "related_docs": ["doc_009"]}
]


@dataclass
class BenchmarkResult:
    """基准测试结果"""
    test_name: str
    total_time_ms: float
    avg_time_ms: float
    min_time_ms: float
    max_time_ms: float
    p95_time_ms: float
    p99_time_ms: float
    throughput_qps: float
    success_rate: float
    details: Dict[str, Any] = field(default_factory=dict)


@dataclass
class AccuracyResult:
    """准确率结果"""
    test_name: str
    precision_at_k: Dict[int, float]
    recall_at_k: Dict[int, float]
    f1_at_k: Dict[int, float]
    ndcg_at_k: Dict[int, float]
    mrr: float
    map_score: float
    details: Dict[str, Any] = field(default_factory=dict)


class SearchBenchmark:
    """搜索性能基准测试"""
    
    def __init__(self, search_service):
        self.search_service = search_service
        self.results: List[BenchmarkResult] = []
        self.accuracy_results: List[AccuracyResult] = []
    
    def run_all_benchmarks(self) -> Dict[str, Any]:
        """运行所有基准测试"""
        print("=" * 60)
        print("语义搜索性能基准测试")
        print("=" * 60)
        
        # 索引文档
        print("\n[1/7] 索引文档...")
        self._index_documents()
        
        # 延迟测试
        print("\n[2/7] 测试搜索延迟...")
        latency_result = self.benchmark_latency()
        self.results.append(latency_result)
        
        # 吞吐量测试
        print("\n[3/7] 测试吞吐量...")
        throughput_result = self.benchmark_throughput()
        self.results.append(throughput_result)
        
        # 准确率测试
        print("\n[4/7] 评估搜索准确率...")
        accuracy_result = self.benchmark_accuracy()
        self.accuracy_results.append(accuracy_result)
        
        # 不同搜索类型对比
        print("\n[5/7] 对比不同搜索类型...")
        type_comparison = self.benchmark_search_types()
        
        # 重排序策略对比
        print("\n[6/7] 对比重排序策略...")
        rerank_comparison = self.benchmark_rerank_strategies()
        
        # 缓存性能测试
        print("\n[7/7] 测试缓存性能...")
        cache_result = self.benchmark_cache_performance()
        self.results.append(cache_result)
        
        # 生成报告
        report = self._generate_report()
        
        print("\n" + "=" * 60)
        print("基准测试完成")
        print("=" * 60)
        
        return report
    
    def _index_documents(self):
        """索引测试文档"""
        start_time = time.time()
        
        for doc in SAMPLE_MATH_DOCUMENTS:
            self.search_service.index_document(
                doc_id=doc["id"],
                content=doc["content"],
                metadata=doc["metadata"]
            )
        
        elapsed = (time.time() - start_time) * 1000
        print(f"  索引 {len(SAMPLE_MATH_DOCUMENTS)} 个文档，耗时: {elapsed:.2f} ms")
    
    def benchmark_latency(self, iterations: int = 50) -> BenchmarkResult:
        """测试搜索延迟"""
        times = []
        errors = 0
        
        for i in range(iterations):
            query_data = random.choice(SAMPLE_QUERIES)
            
            try:
                start = time.time()
                response = self.search_service.search(
                    self.search_service.SearchRequest(
                        query=query_data["query"],
                        k=5
                    )
                )
                elapsed = (time.time() - start) * 1000
                times.append(elapsed)
            except Exception as e:
                errors += 1
                print(f"    Error on iteration {i}: {e}")
        
        if not times:
            times = [0]
        
        result = BenchmarkResult(
            test_name="搜索延迟测试",
            total_time_ms=sum(times),
            avg_time_ms=statistics.mean(times),
            min_time_ms=min(times),
            max_time_ms=max(times),
            p95_time_ms=statistics.quantiles(times, n=20)[18] if len(times) >= 20 else max(times),
            p99_time_ms=statistics.quantiles(times, n=100)[98] if len(times) >= 100 else max(times),
            throughput_qps=1000 / statistics.mean(times) if times else 0,
            success_rate=(iterations - errors) / iterations * 100,
            details={
                "iterations": iterations,
                "errors": errors,
                "std_dev": statistics.stdev(times) if len(times) > 1 else 0
            }
        )
        
        print(f"  平均延迟: {result.avg_time_ms:.2f} ms")
        print(f"  P95延迟: {result.p95_time_ms:.2f} ms")
        print(f"  P99延迟: {result.p99_time_ms:.2f} ms")
        print(f"  成功率: {result.success_rate:.1f}%")
        
        return result
    
    def benchmark_throughput(self, duration_seconds: int = 10) -> BenchmarkResult:
        """测试吞吐量"""
        start_time = time.time()
        count = 0
        errors = 0
        times = []
        
        while time.time() - start_time < duration_seconds:
            query_data = random.choice(SAMPLE_QUERIES)
            
            try:
                req_start = time.time()
                self.search_service.search(
                    self.search_service.SearchRequest(
                        query=query_data["query"],
                        k=5
                    )
                )
                elapsed = (time.time() - req_start) * 1000
                times.append(elapsed)
                count += 1
            except Exception as e:
                errors += 1
        
        actual_duration = time.time() - start_time
        
        result = BenchmarkResult(
            test_name="吞吐量测试",
            total_time_ms=actual_duration * 1000,
            avg_time_ms=statistics.mean(times) if times else 0,
            min_time_ms=min(times) if times else 0,
            max_time_ms=max(times) if times else 0,
            p95_time_ms=0,
            p99_time_ms=0,
            throughput_qps=count / actual_duration,
            success_rate=count / (count + errors) * 100 if (count + errors) > 0 else 0,
            details={
                "total_requests": count,
                "errors": errors,
                "duration_seconds": actual_duration
            }
        )
        
        print(f"  总请求数: {count}")
        print(f"  持续时间: {actual_duration:.1f} 秒")
        print(f"  吞吐量: {result.throughput_qps:.2f} QPS")
        print(f"  成功率: {result.success_rate:.1f}%")
        
        return result
    
    def benchmark_accuracy(self) -> AccuracyResult:
        """评估搜索准确率"""
        k_values = [1, 3, 5, 10]
        
        precision_at_k = {k: [] for k in k_values}
        recall_at_k = {k: [] for k in k_values}
        f1_at_k = {k: [] for k in k_values}
        ndcg_at_k = {k: [] for k in k_values}
        mrr_scores = []
        ap_scores = []
        
        for query_data in SAMPLE_QUERIES:
            try:
                response = self.search_service.search(
                    self.search_service.SearchRequest(
                        query=query_data["query"],
                        k=10
                    )
                )
                
                results = response.results
                relevant_docs = set(query_data["relevant_docs"])
                
                # 计算MRR
                for rank, result in enumerate(results, 1):
                    if result["id"] in relevant_docs:
                        mrr_scores.append(1.0 / rank)
                        break
                else:
                    mrr_scores.append(0)
                
                # 计算Precision@K, Recall@K, F1@K, NDCG@K
                for k in k_values:
                    top_k = results[:k]
                    retrieved_ids = set(r["id"] for r in top_k)
                    
                    # Precision
                    relevant_retrieved = len(retrieved_ids & relevant_docs)
                    precision = relevant_retrieved / k if k > 0 else 0
                    precision_at_k[k].append(precision)
                    
                    # Recall
                    recall = relevant_retrieved / len(relevant_docs) if relevant_docs else 0
                    recall_at_k[k].append(recall)
                    
                    # F1
                    if precision + recall > 0:
                        f1 = 2 * precision * recall / (precision + recall)
                    else:
                        f1 = 0
                    f1_at_k[k].append(f1)
                    
                    # NDCG
                    dcg = 0
                    for rank, result in enumerate(top_k, 1):
                        if result["id"] in relevant_docs:
                            dcg += 1 / (1 + 1)
                    ndcg_at_k[k].append(dcg)
                
                # 计算AP (Average Precision)
                ap = 0
                relevant_count = 0
                for rank, result in enumerate(results, 1):
                    if result["id"] in relevant_docs:
                        relevant_count += 1
                        ap += relevant_count / rank
                ap = ap / len(relevant_docs) if relevant_docs else 0
                ap_scores.append(ap)
                
            except Exception as e:
                print(f"    Error on query '{query_data['query']}': {e}")
                for k in k_values:
                    precision_at_k[k].append(0)
                    recall_at_k[k].append(0)
                    f1_at_k[k].append(0)
                    ndcg_at_k[k].append(0)
                mrr_scores.append(0)
                ap_scores.append(0)
        
        # 计算平均值
        result = AccuracyResult(
            test_name="搜索准确率评估",
            precision_at_k={k: statistics.mean(v) * 100 for k, v in precision_at_k.items()},
            recall_at_k={k: statistics.mean(v) * 100 for k, v in recall_at_k.items()},
            f1_at_k={k: statistics.mean(v) * 100 for k, v in f1_at_k.items()},
            ndcg_at_k={k: statistics.mean(v) * 100 for k, v in ndcg_at_k.items()},
            mrr=statistics.mean(mrr_scores),
            map_score=statistics.mean(ap_scores),
            details={
                "num_queries": len(SAMPLE_QUERIES),
                "mrr_percentage": statistics.mean(mrr_scores) * 100
            }
        )
        
        print(f"  Precision@1: {result.precision_at_k[1]:.1f}%")
        print(f"  Precision@5: {result.precision_at_k[5]:.1f}%")
        print(f"  Recall@5: {result.recall_at_k[5]:.1f}%")
        print(f"  F1@5: {result.f1_at_k[5]:.1f}%")
        print(f"  MRR: {result.mrr:.3f} ({result.details['mrr_percentage']:.1f}%)")
        print(f"  MAP: {result.map_score:.3f}")
        
        return result
    
    def benchmark_search_types(self) -> Dict[str, BenchmarkResult]:
        """对比不同搜索类型"""
        search_types = ["semantic", "keyword", "hybrid"]
        results = {}
        
        test_query = SAMPLE_QUERIES[0]["query"]
        iterations = 20
        
        for search_type in search_types:
            times = []
            
            for _ in range(iterations):
                start = time.time()
                self.search_service.search(
                    self.search_service.SearchRequest(
                        query=test_query,
                        search_type=search_type,
                        k=5
                    )
                )
                elapsed = (time.time() - start) * 1000
                times.append(elapsed)
            
            result = BenchmarkResult(
                test_name=f"搜索类型对比 - {search_type}",
                total_time_ms=sum(times),
                avg_time_ms=statistics.mean(times),
                min_time_ms=min(times),
                max_time_ms=max(times),
                p95_time_ms=0,
                p99_time_ms=0,
                throughput_qps=1000 / statistics.mean(times),
                success_rate=100.0
            )
            
            results[search_type] = result
            print(f"  {search_type:12s}: {result.avg_time_ms:.2f} ms avg")
        
        return results
    
    def benchmark_rerank_strategies(self) -> Dict[str, BenchmarkResult]:
        """对比重排序策略"""
        strategies = ["hybrid", "cross_encoder", "rrf", "diversity"]
        results = {}
        
        test_query = SAMPLE_QUERIES[0]["query"]
        iterations = 10
        
        for strategy in strategies:
            times = []
            
            for _ in range(iterations):
                start = time.time()
                self.search_service.search(
                    self.search_service.SearchRequest(
                        query=test_query,
                        rerank=True,
                        rerank_strategy=strategy,
                        k=5
                    )
                )
                elapsed = (time.time() - start) * 1000
                times.append(elapsed)
            
            result = BenchmarkResult(
                test_name=f"重排序策略对比 - {strategy}",
                total_time_ms=sum(times),
                avg_time_ms=statistics.mean(times),
                min_time_ms=min(times),
                max_time_ms=max(times),
                p95_time_ms=0,
                p99_time_ms=0,
                throughput_qps=1000 / statistics.mean(times),
                success_rate=100.0
            )
            
            results[strategy] = result
            print(f"  {strategy:15s}: {result.avg_time_ms:.2f} ms avg")
        
        return results
    
    def benchmark_cache_performance(self) -> BenchmarkResult:
        """测试缓存性能"""
        test_query = SAMPLE_QUERIES[0]["query"]
        iterations = 20
        
        # 第一次：冷缓存
        cold_times = []
        for _ in range(iterations):
            # 清除缓存
            if hasattr(self.search_service.vector_store, 'query_cache'):
                self.search_service.vector_store.query_cache.clear()
            
            start = time.time()
            self.search_service.search(
                self.search_service.SearchRequest(query=test_query, k=5)
            )
            cold_times.append((time.time() - start) * 1000)
        
        # 第二次：热缓存
        warm_times = []
        for _ in range(iterations):
            start = time.time()
            self.search_service.search(
                self.search_service.SearchRequest(query=test_query, k=5)
            )
            warm_times.append((time.time() - start) * 1000)
        
        speedup = statistics.mean(cold_times) / statistics.mean(warm_times) if warm_times else 1
        
        result = BenchmarkResult(
            test_name="缓存性能测试",
            total_time_ms=0,
            avg_time_ms=statistics.mean(warm_times),
            min_time_ms=min(warm_times),
            max_time_ms=max(warm_times),
            p95_time_ms=0,
            p99_time_ms=0,
            throughput_qps=1000 / statistics.mean(warm_times),
            success_rate=100.0,
            details={
                "cold_cache_avg_ms": statistics.mean(cold_times),
                "warm_cache_avg_ms": statistics.mean(warm_times),
                "speedup": speedup
            }
        )
        
        print(f"  冷缓存平均: {result.details['cold_cache_avg_ms']:.2f} ms")
        print(f"  热缓存平均: {result.details['warm_cache_avg_ms']:.2f} ms")
        print(f"  加速比: {speedup:.2f}x")
        
        return result
    
    def _generate_report(self) -> Dict[str, Any]:
        """生成测试报告"""
        report = {
            "timestamp": datetime.now().isoformat(),
            "summary": {
                "total_tests": len(self.results),
                "avg_latency_ms": next(
                    (r.avg_time_ms for r in self.results if r.test_name == "搜索延迟测试"),
                    0
                ),
                "throughput_qps": next(
                    (r.throughput_qps for r in self.results if r.test_name == "吞吐量测试"),
                    0
                ),
                "precision_at_5": next(
                    (r.precision_at_k.get(5, 0) for r in self.accuracy_results),
                    0
                ),
                "mrr": next(
                    (r.mrr for r in self.accuracy_results),
                    0
                )
            },
            "benchmark_results": [
                {
                    "test_name": r.test_name,
                    "avg_time_ms": r.avg_time_ms,
                    "p95_time_ms": r.p95_time_ms,
                    "throughput_qps": r.throughput_qps,
                    "success_rate": r.success_rate,
                    "details": r.details
                }
                for r in self.results
            ],
            "accuracy_results": [
                {
                    "test_name": r.test_name,
                    "precision_at_k": r.precision_at_k,
                    "recall_at_k": r.recall_at_k,
                    "mrr": r.mrr,
                    "map_score": r.map_score
                }
                for r in self.accuracy_results
            ]
        }
        
        return report
    
    def save_report(self, filepath: str = "benchmark_report.json"):
        """保存报告到文件"""
        report = self._generate_report()
        
        with open(filepath, 'w', encoding='utf-8') as f:
            json.dump(report, f, indent=2, ensure_ascii=False)
        
        print(f"\n报告已保存到: {filepath}")


def run_benchmark():
    """运行基准测试"""
    # 导入优化版搜索服务
    try:
        from .semantic_search_optimized import (
            OptimizedSemanticSearchService,
            SearchRequest
        )
        
        # 添加SearchRequest到类
        OptimizedSemanticSearchService.SearchRequest = SearchRequest
        
        service = OptimizedSemanticSearchService()
        benchmark = SearchBenchmark(service)
        
        report = benchmark.run_all_benchmarks()
        benchmark.save_report("benchmark_report.json")
        
        return report
        
    except Exception as e:
        print(f"运行基准测试时出错: {e}")
        import traceback
        traceback.print_exc()
        return None


if __name__ == "__main__":
    run_benchmark()
